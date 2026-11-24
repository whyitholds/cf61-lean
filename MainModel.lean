import MainBase
import MainBits
open OneAdd CF61

def cfEvenSeed (m t : ℕ) : Prop := t=4 ∨ t=8*K m+2 ∨ t=16*K m

def cfModel (m t : ℕ) : Prop :=
  cfEvenSeed m t ∨ ∃ d, t=b m+2*d ∧ cfOffset m d=1
