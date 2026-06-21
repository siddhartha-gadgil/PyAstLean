import PyAstLean
import Libraries

open PyAstLean
open Libraries


set_option linter.all false
def l :=
  PyAstLean.pyStringSplit "gh yy uu"

def t :=
  PyAstLean.pyStringJoin " " l

def s :=
  PyAstLean.pyStringStrip t "g"

def b1 :=
  PyAstLean.pyStringStartswith s "h"

def b2 :=
  PyAstLean.pyStringEndswith s "u"

def s1 :=
  PyAstLean.pyStringUpper s

def s2 :=
  PyAstLean.pyStringLower s
