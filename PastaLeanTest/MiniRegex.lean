/-
MiniRegex — a small, self-contained backtracking regular-expression engine.

This exists to replace the external `Regex` dependency that PALC
(`PastaLeanCheck.lean`) used to lean on. It implements just the feature set that
PALC's compiled patterns actually exercise:

  * literals and escaped literals (`\.`, `\(`, ...)
  * `.`            — any character except newline (matching lean-regex's default)
  * `[...]`        — character classes with ranges, negation (`[^...]`) and the
                     escapes `\t \r \n \f \v \0 \d \w \s \D \W \S`
  * `( )`          — capturing groups, numbered by opening paren
  * `(?: )`        — non-capturing groups
  * `|`            — alternation
  * `* + ?`        — greedy quantifiers, plus their lazy `*? +? ??` variants

Matching is leftmost (the search tries start positions 0, 1, 2, ...), and
quantifiers follow the usual greedy/lazy preference order, so the results agree
with the PCRE-style semantics PALC depended on.

The public surface mirrors the slice of the old `Regex` API that PALC used:
`Regex`, `Regex.parse`, `Regex.parse!`, `Regex.capture` (+ `Captures.get`),
`Regex.findAll`, and `Regex.test`. Unlike the old API, `Captures.get` and
`findAll` return plain `String`s directly (no `Slice`/`.copy` step).
-/

namespace PastaLeanTest.MiniRegex

/-- Parse / structural errors. Derives `Repr` because PALC interpolates `repr e`. -/
inductive Error where
  | unbalancedParen
  | unbalancedClass
  | trailingBackslash
  | trailingInput (c : Char)
  | emptyInput
deriving Repr, Inhabited

/-- One member of a character class: a single char or an inclusive range. -/
inductive ClassItem where
  | single (c : Char)
  | range (lo hi : Char)
deriving Repr, Inhabited

/-- The compiled regex syntax tree. -/
inductive Re where
  | empty
  | char (c : Char)
  | dot
  | cls (negated : Bool) (items : Array ClassItem)
  | concat (a b : Re)
  | alt (a b : Re)
  | star (greedy : Bool) (r : Re)
  | plus (greedy : Bool) (r : Re)
  | opt (greedy : Bool) (r : Re)
  | group (idx : Nat) (r : Re)
deriving Inhabited

/-- Slots: a flat buffer of `2 * (numGroups + 1)` optional positions.
Slot `2*i` / `2*i+1` are the start / end of group `i` (group `0` = whole match). -/
abbrev Caps := Array (Option Nat)

/-- Class items for `\w` / `[...\w...]`. -/
def wordItems : Array ClassItem :=
  #[.range 'a' 'z', .range 'A' 'Z', .range '0' '9', .single '_']

/-- Class items for `\s` / `[...\s...]`. -/
def spaceItems : Array ClassItem :=
  #[.single ' ', .single '\t', .single '\n', .single '\r',
    .single (Char.ofNat 0x0c), .single (Char.ofNat 0x0b)]

/-- Resolve an escaped atom outside a character class to a sub-pattern. -/
def escapeAtom (c : Char) : Re :=
  match c with
  | 'n' => .char '\n'
  | 't' => .char '\t'
  | 'r' => .char '\r'
  | 'f' => .char (Char.ofNat 0x0c)
  | 'v' => .char (Char.ofNat 0x0b)
  | '0' => .char (Char.ofNat 0)
  | 'd' => .cls false #[.range '0' '9']
  | 'D' => .cls true #[.range '0' '9']
  | 'w' => .cls false wordItems
  | 'W' => .cls true wordItems
  | 's' => .cls false spaceItems
  | 'S' => .cls true spaceItems
  | _   => .char c

/-- Resolve an escaped char *inside* a character class to the items it adds. -/
def classEscape (c : Char) : Array ClassItem :=
  match c with
  | 'n' => #[.single '\n']
  | 't' => #[.single '\t']
  | 'r' => #[.single '\r']
  | 'f' => #[.single (Char.ofNat 0x0c)]
  | 'v' => #[.single (Char.ofNat 0x0b)]
  | '0' => #[.single (Char.ofNat 0)]
  | 'd' => #[.range '0' '9']
  | 'w' => wordItems
  | 's' => spaceItems
  | _   => #[.single c]

/-- Consume a trailing lazy `?` marker after a quantifier, if present. -/
def lazyFlag : List Char → Bool × List Char
  | '?' :: rest => (true, rest)
  | cs          => (false, cs)

/-- Fold an array of sub-patterns into a left-nested concatenation. -/
def concatAll (items : Array Re) : Re :=
  match items.toList with
  | []      => .empty
  | x :: xs => xs.foldl (fun a r => .concat a r) x

/-- Does `c` fall in the class described by `items`? -/
def classMatch (items : Array ClassItem) (c : Char) : Bool :=
  items.any fun it =>
    match it with
    | .single x    => x == c
    | .range lo hi => lo.toNat ≤ c.toNat && c.toNat ≤ hi.toNat

/-- Extract `chars[a:b)` as a `String`. -/
def mkStr (chars : Array Char) (a b : Nat) : String :=
  String.ofList (chars.extract a b).toList

/-- Parse the body of a character class, after the optional leading `^`,
up to and including the closing `]`. Escapes become single items; `-` between
two plain chars becomes a range. -/
partial def pClassItems : List Char → Array ClassItem → Except Error (Array ClassItem × List Char)
  | [], _ => throw .unbalancedClass
  | ']' :: rest, acc => return (acc, rest)
  | '\\' :: c :: rest, acc => pClassItems rest (acc ++ classEscape c)
  | a :: '-' :: b :: rest, acc =>
    if b == ']' then
      -- A trailing `-` is a literal hyphen; hand the `]` back to the loop.
      pClassItems (']' :: rest) ((acc.push (.single a)).push (.single '-'))
    else
      pClassItems rest (acc.push (.range a b))
  | a :: rest, acc => pClassItems rest (acc.push (.single a))

/-- Parse `[ ... ]` (the leading `[` already consumed). -/
def parseClass (cs : List Char) (g : Nat) : Except Error (Re × List Char × Nat) := do
  let (negated, cs0) := match cs with
    | '^' :: r => (true, r)
    | _        => (false, cs)
  let (items, rest) ← pClassItems cs0 #[]
  return (.cls negated items, rest, g)

mutual
  /-- alternation: lowest precedence (`a|b|c`). -/
  partial def pAlt (cs : List Char) (g : Nat) : Except Error (Re × List Char × Nat) := do
    let (items, cs1, g1) ← pSeq cs g #[]
    let left := concatAll items
    match cs1 with
    | '|' :: rest =>
      let (right, cs2, g2) ← pAlt rest g1
      return (.alt left right, cs2, g2)
    | _ => return (left, cs1, g1)

  /-- a run of quantified atoms, stopping at `|`, `)`, or end of input. -/
  partial def pSeq (cs : List Char) (g : Nat) (acc : Array Re) :
      Except Error (Array Re × List Char × Nat) := do
    match cs with
    | []           => return (acc, cs, g)
    | '|' :: _     => return (acc, cs, g)
    | ')' :: _     => return (acc, cs, g)
    | _ =>
      let (atom, cs1, g1) ← pQuant cs g
      pSeq cs1 g1 (acc.push atom)

  /-- an atom optionally followed by `*`, `+`, or `?` (with lazy `?` suffix). -/
  partial def pQuant (cs : List Char) (g : Nat) : Except Error (Re × List Char × Nat) := do
    let (atom, cs1, g1) ← pAtom cs g
    match cs1 with
    | '*' :: rest => let (lz, r) := lazyFlag rest; return (.star (!lz) atom, r, g1)
    | '+' :: rest => let (lz, r) := lazyFlag rest; return (.plus (!lz) atom, r, g1)
    | '?' :: rest => let (lz, r) := lazyFlag rest; return (.opt (!lz) atom, r, g1)
    | _           => return (atom, cs1, g1)

  /-- a single atom: group, class, dot, escape, or literal char. -/
  partial def pAtom (cs : List Char) (g : Nat) : Except Error (Re × List Char × Nat) := do
    match cs with
    | '(' :: '?' :: ':' :: rest =>
      let (inner, cs1, g1) ← pAlt rest g
      match cs1 with
      | ')' :: cs2 => return (inner, cs2, g1)
      | _          => throw .unbalancedParen
    | '(' :: rest =>
      let idx := g + 1
      let (inner, cs1, g1) ← pAlt rest idx
      match cs1 with
      | ')' :: cs2 => return (.group idx inner, cs2, g1)
      | _          => throw .unbalancedParen
    | '[' :: rest    => parseClass rest g
    | '.' :: rest    => return (.dot, rest, g)
    | '\\' :: c :: rest => return (escapeAtom c, rest, g)
    | '\\' :: []     => throw .trailingBackslash
    | c :: rest      => return (.char c, rest, g)
    | []             => throw .emptyInput
end

/-- A compiled regular expression. -/
structure Regex where
  node : Re
  numGroups : Nat
deriving Inhabited

/-- The capture groups of a single match, bound to the haystack characters. -/
structure Captures where
  chars : Array Char
  slots : Caps

/-- Get capture group `index` (`0` = whole match) as a `String`, or `none` if
that group did not participate in the match. -/
def Captures.get (self : Captures) (index : Nat) : Option String := do
  let lo ← (self.slots[2 * index]?).join
  let hi ← (self.slots[2 * index + 1]?).join
  return mkStr self.chars lo hi

mutual
  /-- CPS backtracking matcher. `k` is the continuation: given the position and
  capture buffer after this node matched, it finishes matching the rest. -/
  partial def matchRe (s : Array Char) (re : Re) (pos : Nat) (caps : Caps)
      (k : Nat → Caps → Option Caps) : Option Caps :=
    match re with
    | .empty => k pos caps
    | .char c =>
      if h : pos < s.size then
        if s[pos] == c then k (pos + 1) caps else none
      else none
    | .dot =>
      if h : pos < s.size then
        if s[pos] != '\n' then k (pos + 1) caps else none
      else none
    | .cls negated items =>
      if h : pos < s.size then
        if classMatch items s[pos] != negated then k (pos + 1) caps else none
      else none
    | .concat a b => matchRe s a pos caps (fun p c => matchRe s b p c k)
    | .alt a b =>
      match matchRe s a pos caps k with
      | some r => some r
      | none   => matchRe s b pos caps k
    | .group idx r =>
      let caps1 := caps.set! (2 * idx) (some pos)
      matchRe s r pos caps1 (fun p c => k p (c.set! (2 * idx + 1) (some p)))
    | .opt greedy r =>
      if greedy then
        match matchRe s r pos caps k with
        | some x => some x
        | none   => k pos caps
      else
        match k pos caps with
        | some x => some x
        | none   => matchRe s r pos caps k
    | .star greedy r => matchStar s greedy r pos caps k
    | .plus greedy r => matchRe s r pos caps (fun p c => matchStar s greedy r p c k)

  /-- Greedy/lazy Kleene star. The `p > pos` guard stops infinite recursion on
  sub-patterns that can match the empty string. -/
  partial def matchStar (s : Array Char) (greedy : Bool) (r : Re) (pos : Nat) (caps : Caps)
      (k : Nat → Caps → Option Caps) : Option Caps :=
    if greedy then
      match matchRe s r pos caps (fun p c => if p > pos then matchStar s greedy r p c k else none) with
      | some x => some x
      | none   => k pos caps
    else
      match k pos caps with
      | some x => some x
      | none   => matchRe s r pos caps (fun p c => if p > pos then matchStar s greedy r p c k else none)
end

/-- Parse a regex string into a `Regex`. -/
def Regex.parse (pat : String) : Except Error Regex := do
  let (re, rest, g) ← pAlt pat.toList 0
  match rest with
  | []     => return { node := re, numGroups := g }
  | c :: _ => throw (.trailingInput c)

/-- Parse a regex string, panicking on a parse error. Use `Regex.parse` to
handle errors instead. -/
def Regex.parse! (pat : String) : Regex :=
  match Regex.parse pat with
  | .ok r    => r
  | .error _ => panic! s!"MiniRegex: failed to parse regex: {pat}"

/-- Try to match `re` starting at exactly `start` or any later position
(leftmost match), returning the filled capture buffer. -/
partial def searchSlots (re : Regex) (s : Array Char) (nSlots start : Nat) : Option Caps :=
  let init := ((List.replicate nSlots (none : Option Nat)).toArray).set! 0 (some start)
  match matchRe s re.node start init (fun p c => some (c.set! 1 (some p))) with
  | some caps => some caps
  | none      => if start < s.size then searchSlots re s nSlots (start + 1) else none

/-- Capture the first (leftmost) match of `re` in `haystack`, with its groups. -/
def Regex.capture (re : Regex) (haystack : String) : Option Captures :=
  let s := haystack.toList.toArray
  let nSlots := 2 * (re.numGroups + 1)
  (searchSlots re s nSlots 0).map (fun caps => { chars := s, slots := caps })

/-- `true` iff `re` matches anywhere in `haystack`. -/
def Regex.test (re : Regex) (haystack : String) : Bool :=
  (re.capture haystack).isSome

/-- Collect all non-overlapping matches of `re` in `s`, as strings. -/
partial def findAllAux (re : Regex) (s : Array Char) (nSlots pos : Nat) (acc : Array String) :
    Array String :=
  match searchSlots re s nSlots pos with
  | some caps =>
    let a := ((caps[0]?).join).getD pos
    let b := ((caps[1]?).join).getD a
    let str := mkStr s a b
    let next := if b > a then b else b + 1
    if next > s.size then acc.push str
    else findAllAux re s nSlots next (acc.push str)
  | none => acc

/-- All non-overlapping matches of `re` in `haystack`, as strings. -/
def Regex.findAll (re : Regex) (haystack : String) : Array String :=
  let s := haystack.toList.toArray
  let nSlots := 2 * (re.numGroups + 1)
  findAllAux re s nSlots 0 #[]

end PastaLeanTest.MiniRegex
