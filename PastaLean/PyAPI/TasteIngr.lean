import Mathlib

open Lean Meta

/-- `@[taste_ingr]` is `taste?`'s ingredient set. Applying it both (a) adds the declaration to the
`taste_ingr` simp set — a proposition becomes a simp lemma, a definition is unfolded — so `taste?`
can `simp [taste_ingr]` without full `simp` choking on the `*ₚ` operators, and (b) best-effort
registers it with `grind` (`grind =`). Both sides are best-effort: a theorem with no usable shape is
skipped, so a bad pattern never breaks the build. The codegen tags every pure prove-version function
and every proved assert-theorem, so the prove pass reuses earlier results (leaf-first composition).
Registered in its own module since an attribute can't be used where it's registered. -/
initialize tasteIngrExt : SimpExtension ← do
  let ext ← mkSimpExt `taste_ingr
  simpExtensionMapRef.modify (·.insert `taste_ingr ext)
  registerBuiltinAttribute {
    name := `taste_ingr
    descr := "taste? ingredient: taste_ingr simp set + best-effort grind"
    applicationTime := .afterCompilation
    add := fun declName _stx attrKind => do
      -- simp side, best-effort
      try
        let go : MetaM Unit := do
          if (← isProp (← getConstInfo declName).type) then
            addSimpTheorem ext declName (post := true) (inv := false) attrKind (prio := 1000)
          else
            discard <| addDeclToUnfold ext declName (post := true) (inv := false) (prio := 1000) attrKind
        discard <| go.run {} {}
      catch _ => pure ()
      -- grind side, best-effort (patternless theorems are skipped)
      try Attribute.add declName `grind (← `(attr| grind =)) attrKind catch _ => pure ()
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      let s ← s.erase (.decl declName)
      modifyEnv fun env => ext.modifyState env fun _ => s
  }
  return ext
