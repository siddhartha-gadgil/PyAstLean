# PYASTLEANCHECK START
# TARGET: command
# CHECK: def l := PyAstLean.pySplit "gh yy uu"
# CHECK: def t := PyAstLean.pyJoin " " l
# CHECK: def s := PyAstLean.pyStrip t "g"
# CHECK: def b1 := PyAstLean.pyStartswith s "h"
# CHECK: def b2 := PyAstLean.pyEndswith s "u"
# CHECK: def s1 := PyAstLean.pyUpper s
# CHECK: def s2 := PyAstLean.pyLower s
# PYASTLEANCHECK END

l = "gh yy uu".split()
t = " ".join(l)
s = t.strip('g')
b1 = s.startswith('h')
b2 = s.endswith('u')
s1 = s.upper()   
s2 = s.lower()