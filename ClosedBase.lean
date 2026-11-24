import Bits

open CF61

theorem cfClosedZLe (h l : ℤ) : z h l ≤ 1 := by
  unfold z
  split <;> omega

theorem cfClosedYLe (m : ℕ) (l c r : ℤ) : Y m l c r ≤ 1 := by
  unfold Y δ
  dsimp only
  repeat' first | exact cfClosedZLe _ _ | apply ite_le_one | decide
  all_goals omega

def cfClosedRow (k l t r : ℤ) : Prop :=
  (r = 1 ∧ k ≤ t ∧ t < 3*k ∧ z (t-k) l = 1) ∨
  ((r = 1 ∨ r = 3) ∧ 3*k ≤ t ∧ t ≤ 3*k+l ∧ z (t-3*k) (l+1) = 1) ∨
  (r = 2 ∧ t < 2*k ∧ z t l = 1) ∨
  (r = 4 ∧ l ≤ t ∧ t < 2*k-1 ∧ z (t+1) l = 1) ∨
  (r = 4 ∧ 2*k+l ≤ t ∧ t < 4*k-1 ∧ z (t-2*k+1) l = 1) ∨
  (r = 4 ∧ t = 4*k-1 ∧ l = -1)

theorem cfClosedRowIff (m : ℕ) (l t r : ℤ)
    (hl : -1 ≤ l) (hu : l < 2*(K m:ℤ))
    (ht : 0 ≤ t) (ht' : t < 4*(K m:ℤ)) :
    Y m l (2*(K m:ℤ)+t) r = 1 ↔ cfClosedRow (K m) l t r := by
  have hk : 0 < (K m : ℤ) := by exact_mod_cast (Nat.pow_pos (by decide : 0 < 2) : 0 < K m)
  let k : ℤ := K m
  have e1 : 2*k+t-3*k=t-k := by ring
  have e2 : 2*k+t-5*k=t-3*k := by ring
  have e3 : 2*k+t-2*k=t := by ring
  have e4 : 2*k+t-4*k+1=t-2*k+1 := by ring
  change Y m l (2*k+t) r = 1 ↔ cfClosedRow k l t r
  unfold Y cfClosedRow δ
  change (if _ then _ else _) = 1 ↔ _
  change -1 ≤ l at hl
  change l < 2*k at hu
  change t < 4*k at ht'
  simp only [← show k = (K m:ℤ) from rfl,e1,e2,e3,e4]
  by_cases h1 : r=1
  · subst r
    norm_num only [ite_eq_iff,true_and,false_and,and_true,and_false,true_or,false_or,or_true,or_false]
    omega
  by_cases h2 : r=2
  · subst r
    norm_num only [ite_eq_iff,true_and,false_and,and_true,and_false,true_or,false_or,or_true,or_false]
    omega
  by_cases h3 : r=3
  · subst r
    norm_num only [ite_eq_iff,true_and,false_and,and_true,and_false,true_or,false_or,or_true,or_false]
    omega
  by_cases h4 : r=4
  · subst r
    norm_num only [ite_eq_iff,true_and,false_and,and_true,and_false,true_or,false_or,or_true,or_false]
    omega
  simp [h1,h2,h3,h4]


def cfClosedPrev (k l t d r : ℤ) : Prop :=
  if t < d then cfClosedRow k (l-1) (t+4*k-d) r
  else cfClosedRow k l (t-d) r

def cfClosedOne (a b c : Prop) : Prop :=
  (a ∧ ¬b ∧ ¬c) ∨ (¬a ∧ b ∧ ¬c) ∨ (¬a ∧ ¬b ∧ c)

def cfClosedLocal (m : ℕ) : Prop :=
  let k : ℤ := K m
  ∀ l t r : ℤ, 0 ≤ l → l < 2*k → 0 ≤ t → t < 4*k → 1 ≤ r → r ≤ 4 →
    (cfClosedRow k l t r ↔ cfClosedOne
      (cfClosedPrev k l t (if r ≤ 2 then 1 else 0) (if r ≤ 2 then r+2 else r-2))
      (cfClosedPrev k l t (if r = 1 then k+1 else k) (if r = 1 then 4 else r-1))
      (cfClosedPrev k l t (2*k) r))

theorem cfClosedInitialRow (m : ℕ) (t r : ℤ) :
    cfClosedRow (K m) (-1) t r ↔ r = 4 ∧ t = 4*(K m:ℤ)-1 := by
  unfold cfClosedRow
  have hz : ∀ u : ℤ, z u (-1) = 0 := by intro u; simp [z]
  simp only [hz, Nat.zero_ne_one, and_false, false_or, eq_self, and_true]
  omega
