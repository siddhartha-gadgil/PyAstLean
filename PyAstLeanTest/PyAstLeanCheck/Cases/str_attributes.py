# PYASTLEANCHECK START
# TARGET: command
# CHECK: def l :=
# CHECK: PyAstLean.pyStringSplit "gh yy uu"
# CHECK: def t :=
# CHECK: PyAstLean.pyStringJoin " " l
# CHECK: def s :=
# CHECK: PyAstLean.pyStringStrip t "g"
# CHECK: def b1 :=
# CHECK: PyAstLean.pyStringStartswith s "h"
# CHECK: def b2 :=
# CHECK: PyAstLean.pyStringEndswith s "u"
# CHECK: def s1 :=
# CHECK: PyAstLean.pyStringUpper s
# CHECK: def s2 :=
# CHECK: PyAstLean.pyStringLower s
# PYASTLEANCHECK END

l = "gh yy uu".split()
t = " ".join(l)
s = t.strip('g')
b1 = s.startswith('h')
b2 = s.endswith('u')
s1 = s.upper()   
s2 = s.lower()
