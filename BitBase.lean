import Bits
open CF61

def cfHistory (m n : ℕ) := (bitsStep m)^[n] []

theorem cfHistoryStep (m n : ℕ) : cfHistory m (n+1) = bitsStep m (cfHistory m n) :=
  Function.iterate_succ_apply' _ _ _

theorem cfHistoryLength (m n : ℕ) : (cfHistory m n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cfHistoryStep, bitsStep, ih]

theorem cfHistoryRead (m n i : ℕ) (hi : i < n) : (cfHistory m n).getD i 0 = y m i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · rw [cfHistoryStep, bitsStep, List.getD_append]
      · exact ih h
      · simpa [cfHistoryLength] using h
    · have : i = n := by omega
      subst i
      rfl

theorem cfYRule (m n : ℕ) : y m n =
    if n < 8*K m then 0 else if n = 8*K m then 1 else
    if y m (n-2) + y m (n-4*K m-1) + y m (n-8*K m) = 1 then 1 else 0 := by
  change (cfHistory m (n+1)).getD n 0 = _
  rw [cfHistoryStep, bitsStep, List.getD_append_right _ _ _ _ (by simp [cfHistoryLength])]
  simp only [cfHistoryLength, Nat.sub_self, List.getD_cons_zero]
  by_cases h : n < 8*K m
  · simp [h]
  by_cases h' : n = 8*K m
  · simp [h,h']
  have hk : 0 < K m := by unfold K; positivity
  simp only [h,h',if_false]
  rw [cfHistoryRead _ _ _ (by omega), cfHistoryRead _ _ _ (by omega), cfHistoryRead _ _ _ (by omega)]

theorem cfBitsEquations : BitsEquations := by
  intro m hm
  refine ⟨?_, ?_, ?_⟩
  · intro n hn hn'
    simp [cfYRule m n, hn']
  · rw [cfYRule]; simp
  · intro n hn
    rw [cfYRule]
    simp [show ¬ n < 8 * K m by omega, show n ≠ 8*K m by omega]
