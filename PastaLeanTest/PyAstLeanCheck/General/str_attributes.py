# PastaLeanCHECK START
# TARGET: command
# CHECK: def l :=
# CHECK: PastaLean.pyStringSplit "gh yy uu"
# CHECK: def t :=
# CHECK: PastaLean.pyStringJoin " " l
# CHECK: def s :=
# CHECK: PastaLean.pyStringStrip t "g"
# CHECK: def b1 :=
# CHECK: PastaLean.pyStringStartswith s "h"
# CHECK: def b2 :=
# CHECK: PastaLean.pyStringEndswith s "u"
# CHECK: def s1 :=
# CHECK: PastaLean.pyStringUpper s
# CHECK: def s2 :=
# CHECK: PastaLean.pyStringLower s
# PastaLeanCHECK END

l = "gh yy uu".split()
t = " ".join(l)
s = t.strip('g')
b1 = s.startswith('h')
b2 = s.endswith('u')
s1 = s.upper()   
s2 = s.lower()
