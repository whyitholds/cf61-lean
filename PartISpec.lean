import Statement
open OneAdd CF61

structure PICell where
  u : ℕ
  v : ℕ
  kind : Fin 6
deriving DecidableEq

def PITagShift : Fin 6 → ℕ := ![3,2,2,4,1,1]

def PITagResidue : Fin 6 → ℕ := ![1,2,0,0,1,3]

def PITagOK (u v : ℕ) (t : Fin 6) : Prop :=
  t.val ≤ 1 ∨ (t.val = 2 ∧ u ≤ v) ∨ (t.val = 3 ∧ u < v) ∨ (4 ≤ t.val ∧ v < u)

def PIValid (k : ℕ) (x : PICell) : Prop :=
  x.u < 2*k ∧ x.v < 2*k ∧ x.u &&& x.v = 0 ∧ PITagOK x.u x.v x.kind

def PICellValue (k : ℕ) (x : PICell) : ℕ :=
  16*k*x.u + 4*x.v + 4*k*PITagShift x.kind + PITagResidue x.kind
