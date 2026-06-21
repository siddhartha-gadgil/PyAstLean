import PastaLean
import Libraries

open PastaLean
open Libraries


set_option linter.all false
def l :=
  PastaLean.pyStringSplit "gh yy uu"

def t :=
  PastaLean.pyStringJoin " " l

def s :=
  PastaLean.pyStringStrip t "g"

def b1 :=
  PastaLean.pyStringStartswith s "h"

def b2 :=
  PastaLean.pyStringEndswith s "u"

def s1 :=
  PastaLean.pyStringUpper s

def s2 :=
  PastaLean.pyStringLower s
