import Bits
open CF61

theorem cfChooseBit (h l : ℕ) :
    (h+l).choose l % 2 = if h &&& l = 0 then 1 else 0 := by
  by_cases hv : h + l = 0
  · have : h = 0 := by omega
    have : l = 0 := by omega
    simp_all
  have ih := cfChooseBit (h/2) (l/2)
  have hsum : h / 2 + l / 2 < h + l := by omega
  have hc : (h+l).choose l % 2 =
      ((Nat.choose ((h+l)%2) (l%2)) * (Nat.choose ((h+l)/2) (l/2))) % 2 :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have ha := Nat.and_mod_two_eq_one (a := h) (b := l)
  have hd := Nat.and_div_two (a := h) (b := l)
  by_cases a : h % 2 = 1 <;> by_cases b : l % 2 = 1
  · have hm : (h+l)%2 = 0 := by omega
    have hn : h &&& l ≠ 0 := by omega
    simpa [hm, b, hn] using hc
  all_goals
    have he : (h+l)/2 = h/2+l/2 := by omega
    have hn : h &&& l = 0 ↔ h/2 &&& (l/2) = 0 := by omega
    have hx : Nat.choose ((h+l)%2) (l%2) = 1 := by
      first | rw [show l%2 = 0 by omega]; simp | rw [show (h+l)%2 = 1 by omega,b]; decide
    rw [hc, hx, one_mul, he, ih]
    simp only [hn]
termination_by h+l
decreasing_by omega

theorem cfZBit (h l : ℕ) : z (h:ℤ) (l:ℤ) = (if h &&& l = 0 then 1 else 0) := by
  unfold z
  rw [if_pos ⟨by positivity,by positivity⟩]
  exact cfChooseBit h l
