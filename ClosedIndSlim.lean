import ClosedStep
import Statement
open CF61

theorem cfClosedInitialValue (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) (t r : ℤ) (hr : 1 ≤ r)
    (hr' : r ≤ 4) (ht : t<4*(K m:ℤ)) (E : (n:ℤ)=16*(K m:ℤ)*(-1)+8*(K m:ℤ)+4*t+r) :
    y m n=1 ↔ cfClosedRow (K m) (-1) t r := by
  obtain ⟨hb,eq⟩ := cfClosedOrigin (K m) n t r ht hr hr' E
  have hbn : n ≤ 8*K m := by exact_mod_cast hb
  have e : (n:ℤ)=8*(K m:ℤ) ↔ n=8*K m := by norm_cast
  rw [e] at eq
  rw [cfClosedInitialRow,← eq]
  obtain ⟨base,seed,_⟩ := cfBitsEquations m hm
  by_cases he : n=8*K m
  · simp [he,seed]
  · rw [base n hn (by omega)]; omega

theorem cfClosedAgree (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) (h : a=1 ↔ b=1) : a=b := by omega

theorem cfClosedFromLocal (steps : ∀ m : ℕ, 3 ≤ m → cfClosedLocal m) : CF61_Closed := by
  refine ⟨cfBitsEquations, ?_⟩
  intro m hm n
  have kp : 0<K m := by unfold K; positivity
  have kp' : 0 < (K m:ℤ) := by exact_mod_cast kp
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn hmax l c r coords
    obtain ⟨en,hc,hc',hr,hr'⟩ := coords
    let t := c-2*(K m:ℤ)
    have E0 : 2*(K m:ℤ)+t=c := by dsimp [t]; ring
    have E := cfClosedNormCoord (K m) l c t r n en E0
    have ht : 0 ≤ t := by dsimp [t]; omega
    have ht' : t<4*(K m:ℤ) := by dsimp [t]; omega
    change n ≤ 32*(K m)^2+8*K m at hmax
    have H : (n:ℤ) ≤ 32*(K m:ℤ)^2+8*(K m:ℤ) := by exact_mod_cast hmax
    have npos : (1:ℤ) ≤ n := by exact_mod_cast hn
    obtain ⟨hl,hu⟩ := cfClosedBlock n (K m) l t r kp' npos H ht ht' hr hr' E
    have tab := cfClosedRowIff m l t r hl hu ht ht'
    rw [E0] at tab
    have hY := cfClosedYLe m l c r
    have hy := cfClosedBit m n hm hn
    apply cfClosedAgree _ _ hy hY
    rw [tab]
    by_cases he : l = -1
    · subst l
      exact cfClosedInitialValue _ _ hm hn _ _ hr hr' ht' E
    · have hl' : 0 ≤ l := by omega
      have hb := cfClosedPost n (K m) l t r kp' hl' ht hr E
      have hp : 8*K m<n := by exact_mod_cast hb
      apply cfClosedRunStep m n hm hp l t r hl' hu ht ht' hr hr' E _ (steps m hm)
      intro i hi h1
      exact ih i hi h1 (le_trans hi.le hmax)
