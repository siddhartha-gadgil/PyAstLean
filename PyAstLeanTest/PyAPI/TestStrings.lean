import PyAstLean
import PyAstLean.PyAPI.Strings

open PyAstLean

/-- info: ["alpha", "beta", "gamma"] -/
#guard_msgs in
#eval pySplit "  alpha\tbeta\n gamma  "

/-- info: ["a", "", "b", ""] -/
#guard_msgs in
#eval pySplit "a,,b," ","

/-- info: ["line1", "line2", "line3"] -/
#guard_msgs in
#eval pyStringSplitLines "line1\nline2\nline3"

/-- info: "a-b-c" -/
#guard_msgs in
#eval pyJoin "-" ["a", "b", "c"]

/-- info: "" -/
#guard_msgs in
#eval pyJoin ":" []

 /-- info: "baaaaa" -/
#guard_msgs in
#eval pyReplace "banana" "n" "a"

/-- info: "bbb" -/
#guard_msgs in
#eval pyReplace "aaa" "a" "b"

/-- info: "trim me" -/
#guard_msgs in
#eval pyStrip "\n\t trim me \r "

 /-- info: "hello" -/
#guard_msgs in
#eval pyStrip "xyxhelloxy" "xy"

/-- info: 2 -/
#guard_msgs in
#eval pyFind "banana" "na"

/-- info: -1 -/
#guard_msgs in
#eval pyFind "banana" "zz"

/-- info: 2 -/
#guard_msgs in
#eval pyStringIndex "banana" "na"

/-- info: true -/
#guard_msgs in
#eval pyStringStartswith "analytics" "ana"

/-- info: false -/
#guard_msgs in
#eval pyStringStartswith "analytics" "lyt"

/-- info: true -/
#guard_msgs in
#eval pyStringEndswith "analytics" "ics"

/-- info: false -/
#guard_msgs in
#eval pyStringEndswith "analytics" "ana"

/-- info: "mixed" -/
#guard_msgs in
#eval pyStringLower "MiXeD"

/-- info: "MIXED" -/
#guard_msgs in
#eval pyStringUpper "MiXeD"

/-- info: "ell" -/
#guard_msgs in
#eval pyStringSlice "hello" (some 1) (some 4)

/-- info: "he" -/
#guard_msgs in
#eval pyStringSlice "hello" (some 0) (some 2)

/-- info: "lo" -/
#guard_msgs in
#eval pyStringSlice "hello" (some 3) none
