import CoordsBase
import NumBits
open OneAdd CF61

theorem cfKPos (m : ℕ) : 0 < K m := by unfold K; positivity

theorem cfZBoundaryOne (m : ℕ) :
    z ((K m : ℤ)-1) (2*(K m : ℤ)) = 1 := by
  have hp := cfKPos m
  have hcast : ((K m - 1 : ℕ) : ℤ) = (K m:ℤ)-1 := by omega
  have hc : ((2 * K m : ℕ) : ℤ) = 2*(K m:ℤ) := by push_cast; rfl
  rw [← hcast, ← hc, cfZBit]
  apply if_pos
  have he : 2*K m = 2^(m-2+1) := by simp [K,pow_succ,Nat.mul_comm]
  rw [he]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : m-2+1 = i
  · subst i
    have hh : K m-1 < 2^(m-2+1) := by rw [← he]; omega
    simp [Nat.testBit_lt_two_pow hh]
  · simp [Nat.testBit_two_pow,hi]

theorem cfZBoundaryZero (m : ℕ) :
    z (K m : ℤ) (2*(K m : ℤ)-1) = 0 := by
  have hp := cfKPos m
  have hc : ((2*K m - 1 : ℕ) : ℤ) = 2*(K m:ℤ)-1 := by omega
  rw [← hc, cfZBit]
  apply if_neg
  have he : 2*K m = 2^(m-2+1) := by simp [K,pow_succ,Nat.mul_comm]
  rw [he, Nat.and_two_pow_sub_one_of_lt_two_pow (by rw [← he]; omega)]
  omega

theorem cfSharpTable (m : ℕ) (hm : 3 ≤ m) :
    ∀ l c r, Coords m (n₀ m+8*K m+1) l c r → Y m l c r = 0 := by
  let k : ℤ := K m
  have hk : 0 < k := by dsimp [k]; exact_mod_cast cfKPos m
  have h : Coords m (n₀ m+8*K m+1) (2*k) (2*k) 1 := by
    unfold Coords n₀
    push_cast
    change _ = 16*k*(2*k)+4*(2*k)+1 ∧ _
    refine ⟨by dsimp only [k]; ring, ?_⟩
    change 2*k ≤ 2*k ∧ 2*k ≤ 6*k-1 ∧ True ∧ True
    exact ⟨by omega, by omega, trivial, trivial⟩
  intro l c r h'
  obtain ⟨rfl,rfl,rfl⟩ := (cfCoords m hm _ (by omega)).2 _ _ _ _ _ _ h' h
  simp [Y, show 2*k ≤ 3*k-1 by omega, k] at *

theorem cfSharpOfClosed (h : CF61_Closed) : CF61_Sharp := by
  refine ⟨h.1, ?_⟩
  intro m hm
  refine ⟨?_, cfSharpTable m hm⟩
  let k : ℤ := K m
  have hp := cfKPos m
  have hk : 0 < k := by dsimp [k]; exact_mod_cast hp
  have he : (n₀ m : ℤ) = 32*k^2 := by simp [n₀,k]
  have hn : 8*K m ≤ n₀ m := by unfold n₀; nlinarith [Nat.one_le_pow (m-2) 2 (by decide : 0 < 2),hp]
  have h1 : Coords m (n₀ m+8*K m-1) (2*k-1) (6*k-1) 3 := by
    unfold Coords
    rw [Nat.cast_sub (by omega : 1 ≤ n₀ m+8*K m)]
    push_cast
    change _ = 16*k*(2*k-1)+4*(6*k-1)+3 ∧ _
    rw [he]
    refine ⟨by dsimp only [k]; ring, ?_⟩
    change 2*k ≤ 6*k-1 ∧ 6*k-1 ≤ 6*k-1 ∧ True ∧ True
    exact ⟨by omega, by omega, trivial, trivial⟩
  have h2 : Coords m (n₀ m+4*K m) (2*k-1) (5*k-1) 4 := by
    unfold Coords
    push_cast
    rw [he]
    refine ⟨by dsimp only [k]; ring, ?_⟩
    change 2*k ≤ 5*k-1 ∧ 5*k-1 ≤ 6*k-1 ∧ True ∧ True
    exact ⟨by omega, by omega, trivial, trivial⟩
  have h3 : Coords m (n₀ m+1) (2*k-1) (4*k) 1 := by
    unfold Coords
    push_cast
    rw [he]
    refine ⟨by dsimp only [k]; ring, ?_⟩
    change 2*k ≤ 4*k ∧ 4*k ≤ 6*k-1 ∧ True ∧ True
    exact ⟨by omega, by omega, trivial, trivial⟩
  have v1 := h.2 m hm _ (by omega) (by omega) _ _ _ h1
  have v2 := h.2 m hm _ (by omega) (by omega) _ _ _ h2
  have v3 := h.2 m hm _ (by omega) (by omega) _ _ _ h3
  have t1 : Y m (2*k-1) (6*k-1) 3 = 1 := by
    unfold Y
    change (if _ then _ else _) = _
    dsimp only [k] at *
    simp only [show (3:ℤ) ≠ 1 by decide, show (3:ℤ) ≠ 2 by decide,
      false_and, if_false, true_and, reduceCtorEq]
    rw [if_neg (by omega), if_pos (by omega)]
    convert cfZBoundaryOne m using 2 <;> ring
  have t2 : Y m (2*k-1) (5*k-1) 4 = 0 := by
    unfold Y
    dsimp only [k] at *
    simp only [show (4:ℤ) ≠ 1 by decide, show (4:ℤ) ≠ 2 by decide,
      show (4:ℤ) ≠ 3 by decide, false_and, if_false, true_and]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have t3 : Y m (2*k-1) (4*k) 1 = 0 := by
    unfold Y
    dsimp only [k] at *
    rw [if_neg (by omega), if_pos (by omega)]
    convert cfZBoundaryZero m using 2 <;> ring
  rw [h.1 m hm |>.2.2 _ (by omega)]
  rw [show n₀ m+8*K m+1-2 = n₀ m+8*K m-1 by omega,
      show n₀ m+8*K m+1-4*K m-1 = n₀ m+4*K m by omega,
      show n₀ m+8*K m+1-8*K m = n₀ m+1 by omega, v1,v2,v3,t1,t2,t3]
  rfl
