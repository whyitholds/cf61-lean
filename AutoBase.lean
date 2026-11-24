import Std

structure AutoLin where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq

def autoVal (A : AutoLin) (k l t : Nat) : Int :=
  A.a * k + A.b * l + A.c * t + A.d

inductive AutoF where
  | yes | no | ge (A : AutoLin) | dis (A B : AutoLin) | pow
  | neg (f : AutoF) | con (f g : AutoF) | disj (f g : AutoF)

def autoDen : AutoF → Nat → Nat → Nat → Prop
  | .yes, _, _, _ => True
  | .no, _, _, _ => False
  | .ge A, k,l,t => 0 ≤ autoVal A k l t
  | .dis A B, k,l,t => 0 ≤ autoVal A k l t ∧ 0 ≤ autoVal B k l t ∧
      (autoVal A k l t).toNat &&& (autoVal B k l t).toNat = 0
  | .pow, k,_,_ => ∃ e : Nat, k = 2 ^ e
  | .neg f, k,l,t => ¬ autoDen f k l t
  | .con f g, k,l,t => autoDen f k l t ∧ autoDen g k l t
  | .disj f g, k,l,t => autoDen f k l t ∨ autoDen g k l t

def autoBit (j : Fin 8) (i : Nat) := j.val / 2^i % 2

def autoRead (i : Nat) : List (Fin 8) → Nat
  | [] => 0
  | j::w => 2 * autoRead i w + autoBit j i

theorem autoCover (k l t : Nat) : ∃ w, autoRead 0 w = k ∧ autoRead 1 w = l ∧ autoRead 2 w = t := by
  by_cases h : k + l + t = 0
  · exact ⟨[], by simp [autoRead]; omega⟩
  · obtain ⟨w, h0,h1,h2⟩ := autoCover (k/2) (l/2) (t/2)
    let j : Fin 8 := ⟨k%2 + 2*(l%2) + 4*(t%2), by omega⟩
    refine ⟨j :: w, ?_⟩
    simp only [autoRead, h0, h1, h2, autoBit, j]
    change 2*(k/2) + (k%2 + 2*(l%2)+4*(t%2))/1%2 = k ∧ 2*(l/2) + (k%2 + 2*(l%2)+4*(t%2))/2%2 = l ∧ 2*(t/2) + (k%2 + 2*(l%2)+4*(t%2))/4%2 = t
    omega
termination_by k+l+t
decreasing_by omega
