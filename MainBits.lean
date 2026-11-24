import Bits
open CF61

def cfOffset (m d : ℕ) : ℕ := y m (8*K m+d)

theorem cfKTwo (m : ℕ) (hm : 3 ≤ m) : 2 ≤ K m := by
  unfold K
  apply le_trans (b := 2^1)
  · decide
  · exact Nat.pow_le_pow_right (by omega) (by omega)

theorem cfBFromK (m : ℕ) (hm : 3 ≤ m) : b m + 1 = 4*K m := by
  unfold b K
  have h : m = (m-2)+2 := by omega
  conv_lhs => rw [h, pow_add]
  have hp : 0 < 2^(m-2) := pow_pos (by decide) _
  omega

theorem cfBitAtMost (eqs : BitsEquations) (m : ℕ) (hm : 3 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    y m n ≤ 1 := by
  obtain ⟨lo,mid,hi⟩ := eqs m hm
  rcases lt_trichotomy n (8*K m) with lt|rfl|gt
  · rw [lo n hn lt]; decide
  · rw [mid]
  · rw [hi n gt]; split <;> decide

theorem cfEarlyBit (eqs : BitsEquations) (m : ℕ) (hm : 3 ≤ m) {d : ℕ}
    (hd : d < 8*K m) :
    (d%2=0 → cfOffset m d = 1) ∧
    (d < 4*K m+1 → d%2=1 → cfOffset m d = 0) := by
  have hk := cfKTwo m hm
  obtain ⟨lo,mid,hi⟩ := eqs m hm
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases dz : d=0
    · subst d; simp [cfOffset,mid]
    have hrec := hi (8*K m+d) (by omega)
    have last : y m (8*K m+d-8*K m) = 0 := lo _ (by omega) (by omega)
    rw [last,Nat.add_zero] at hrec
    change (d%2=0 → y m (8*K m+d) = 1) ∧ _
    constructor
    · intro he
      have step := (ih (d-2) (by omega) (by omega)).1 (by omega)
      have fst : y m (8*K m+d-2)=1 := by
        simpa [cfOffset,show 8*K m+d-2=8*K m+(d-2) by omega] using step
      have snd : y m (8*K m+d-4*K m-1) = 0 := by
        by_cases sm : d < 4*K m+1
        · exact lo _ (by omega) (by omega)
        have prev := (ih (d-(4*K m+1)) (by omega) (by omega)).2 (by omega) (by omega)
        simpa [cfOffset,show 8*K m+d-4*K m-1=8*K m+(d-(4*K m+1)) by omega] using prev
      simp [hrec,fst,snd]
    · intro sm odd
      have snd := lo (8*K m+d-4*K m-1) (by omega) (by omega)
      have fst : y m (8*K m+d-2)=0 := by
        by_cases one : d=1
        · apply lo <;> omega
        have prev := (ih (d-2) (by omega) (by omega)).2 (by omega) (by omega)
        simpa [cfOffset,show 8*K m+d-2=8*K m+(d-2) by omega] using prev
      simp [cfOffset,hrec,fst,snd]

theorem cfFirstOdd (eqs : BitsEquations) (m : ℕ) (hm : 3 ≤ m) :
    cfOffset m (4*K m+1)=1 ∧ cfOffset m (4*K m+3)=0 := by
  have hk := cfKTwo m hm
  obtain ⟨lo,mid,hi⟩ := eqs m hm
  have pre := (cfEarlyBit eqs m hm (d := 4*K m-1) (by omega)).2 (by omega) (by omega)
  have two := (cfEarlyBit eqs m hm (d := 2) (by omega)).1 (by omega)
  unfold cfOffset at *
  have h : y m (8*K m+(4*K m+1))=1 := by
    rw [hi _ (by omega),show 8*K m+(4*K m+1)-2=8*K m+(4*K m-1) by omega,pre,
      show 8*K m+(4*K m+1)-4*K m-1=8*K m by omega,mid,lo _ (by omega) (by omega)]
    decide
  refine ⟨h,?_⟩
  rw [hi _ (by omega),show 8*K m+(4*K m+3)-2=8*K m+(4*K m+1) by omega,h,
    show 8*K m+(4*K m+3)-4*K m-1=8*K m+2 by omega,two,lo _ (by omega) (by omega)]
  decide
