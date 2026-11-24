import Statement
open OneAdd CF61

theorem cfCoords : CF61_Coords := by
  intro m hm n hn
  let k : ℤ := K m
  have hk : 0 < k := by dsimp [k, K]; positivity
  let u : ℤ := n - 8*k - 1
  let d := 16*k
  have hd : 0 < d := by dsimp [d]; omega
  let s := u % d
  have hs0 : 0 ≤ s := Int.emod_nonneg _ (by omega)
  have hs1 : s < d := Int.emod_lt_of_pos _ hd
  constructor
  · refine ⟨u / d, 2*k + s / 4, 1 + s % 4, ?_⟩
    change (n : ℤ) = d*(u/d) + 4*(2*k+s/4) + (1+s%4) ∧ _
    have hu : s + d * (u / d) = u := Int.emod_add_mul_ediv u d
    change _ ∧ 2*k ≤ 2*k+s/4 ∧ 2*k+s/4 ≤ 6*k-1 ∧ _
    have hnrel : (n:ℤ) = u+8*k+1 := by dsimp only [u]; ring
    dsimp only [d] at hs1
    omega
  · intro l c r l' c' r' h h'
    change (n : ℤ) = d*l+4*c+r ∧ 2*k ≤ c ∧ c ≤ 6*k-1 ∧ 1 ≤ r ∧ r ≤ 4 at h
    change (n : ℤ) = d*l'+4*c'+r' ∧ 2*k ≤ c' ∧ c' ≤ 6*k-1 ∧ 1 ≤ r' ∧ r' ≤ 4 at h'
    have hll : l = l' := by
      by_contra ne
      rcases lt_or_gt_of_ne ne with lt | gt
      · have e := mul_le_mul_of_nonneg_left (show l+1 ≤ l' by omega) hd.le
        rw [mul_add, mul_one] at e
        dsimp only [d] at *
        omega
      · have e := mul_le_mul_of_nonneg_left (show l'+1 ≤ l by omega) hd.le
        rw [mul_add, mul_one] at e
        dsimp only [d] at *
        omega
    subst l'
    exact ⟨rfl, by omega, by omega⟩
