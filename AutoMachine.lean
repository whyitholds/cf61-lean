import AutoBase

structure AutoM (α : Type) where
  last : α → Bool
  step : α → Fin 8 → α

def autoRun (M : AutoM α) (s : α) : List (Fin 8) → Bool
  | [] => M.last s
  | j :: w => autoRun M (M.step s j) w

def autoGood (f : AutoF) (M : AutoM α) (s : α) := ∀ w,
  autoRun M s w = true ↔ autoDen f (autoRead 0 w) (autoRead 1 w) (autoRead 2 w)

def autoCombine (m n : AutoM Nat) (op : Bool → Bool → Bool) : AutoM (Nat × Nat) :=
  ⟨fun (i,j) => op (m.last i) (n.last j), fun (i,j) x => (m.step i x,n.step j x)⟩

def autoFlip (m : AutoM Nat) : AutoM Nat := ⟨fun i => !(m.last i), m.step⟩

theorem autoRunFlip (m : AutoM Nat) (s : Nat) (w) :
    autoRun (autoFlip m) s w = !(autoRun m s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons j w ih => exact ih _

theorem autoRunCombine (m n : AutoM Nat) (op : Bool → Bool → Bool) (i j : Nat) (w) :
    autoRun (autoCombine m n op) (i,j) w = op (autoRun m i w) (autoRun n j w) := by
  induction w generalizing i j with
  | nil => rfl
  | cons b w ih => exact ih _ _

theorem autoGoodNeg (m : AutoM Nat) (h : autoGood f m 0) :
    autoGood (.neg f) (autoFlip m) 0 := by
  intro w
  simp [autoRunFlip, autoDen, ← h w]

theorem autoGoodCon (m n : AutoM Nat) (h : autoGood f m 0) (g' : autoGood g n 0) :
    autoGood (.con f g) (autoCombine m n Bool.and) (0,0) := by
  intro w
  simp [autoRunCombine, autoDen, h w, g' w]

theorem autoGoodOr (m n : AutoM Nat) (h : autoGood f m 0) (g' : autoGood g n 0) :
    autoGood (.disj f g) (autoCombine m n Bool.or) (0,0) := by
  intro w
  simp [autoRunCombine, autoDen, h w, g' w]

theorem autoSim {α : Type} {N : Nat} (m : AutoM α) (n : AutoM Nat)
    (src : Fin (N+1) → α) (dst : Fin (N+1) → Nat)
    (tr : Fin (N+1) → Fin 8 → Fin (N+1))
    (hf : ∀ i, m.last (src i) = n.last (dst i))
    (ht : ∀ i j, m.step (src i) j = src (tr i j) ∧ n.step (dst i) j = dst (tr i j))
    (w : List (Fin 8)) (i : Fin (N+1)) : autoRun m (src i) w = autoRun n (dst i) w := by
  induction w generalizing i with
  | nil => exact hf i
  | cons j w ih =>
    simp only [autoRun, (ht i j).1, (ht i j).2]
    exact ih _

theorem autoTransfer {α : Type} {N : Nat} (m : AutoM α) (n : AutoM Nat)
    (src : Fin (N+1) → α) (dst : Fin (N+1) → Nat) (tr : Fin (N+1) → Fin 8 → Fin (N+1))
    (hf : ∀ i, m.last (src i) = n.last (dst i))
    (ht : ∀ i j, m.step (src i) j = src (tr i j) ∧ n.step (dst i) j = dst (tr i j))
    (h : autoGood f m (src 0)) (hd : dst 0 = 0) : autoGood f n 0 := by
  intro w
  have e := autoSim m n src dst tr hf ht w 0
  rw [hd] at e
  rw [← e]
  exact h w

def autoAlways : AutoM Nat := ⟨fun _ => true, fun _ _ => 0⟩

theorem autoAlwaysRun (w) : autoRun autoAlways 0 w = true := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

theorem autoFinish (h : autoGood f autoAlways 0) (k l t : Nat) : autoDen f k l t := by
  obtain ⟨w, h0,h1,h2⟩ := autoCover k l t
  simpa [h0,h1,h2] using (h w).mp (autoAlwaysRun w)

def autoLo (A : AutoLin) (j : Fin 8) : Int :=
  autoVal A (autoBit j 0) (autoBit j 1) (autoBit j 2)

def autoShift (A : AutoLin) (j : Fin 8) : AutoLin :=
  { A with d := autoLo A j / 2 }

theorem autoValShift (A : AutoLin) (j : Fin 8) (k l t : Nat) :
    autoVal A (2*k+autoBit j 0) (2*l+autoBit j 1) (2*t+autoBit j 2) =
    2*autoVal (autoShift A j) k l t + autoLo A j % 2 := by
  have p := Int.emod_add_mul_ediv (autoLo A j) 2
  simp only [autoShift, autoLo, autoVal, Int.natCast_add, Int.natCast_mul] at *
  grind

theorem autoDisHalf (a b u v : Int) (hu : 0 ≤ u) (hu' : u < 2) (hv : 0 ≤ v) (hv' : v < 2) :
    (0 ≤ 2*a+u ∧ 0 ≤ 2*b+v ∧ (2*a+u).toNat &&& (2*b+v).toNat = 0) ↔
    ¬(u=1 ∧ v=1) ∧ 0 ≤ a ∧ 0 ≤ b ∧ a.toNat &&& b.toNat = 0 := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · let x := (2*a+u).toNat
    let y := (2*b+v).toNat
    have H := @Nat.and_mod_two_eq_one x y
    have D := @Nat.and_div_two x y
    have dx : x/2 = a.toNat := by dsimp [x]; omega
    have dy : y/2 = b.toNat := by dsimp [y]; omega
    have ux : x%2 = u.toNat := by dsimp [x]; omega
    have uy : y%2 = v.toNat := by dsimp [y]; omega
    rw [dx,dy] at D
    rw [ux,uy] at H
    change (0 ≤ 2*a+u ∧ 0 ≤ 2*b+v ∧ x &&& y = 0) ↔ _
    omega
  all_goals omega

theorem autoPowEven (k : Nat) : (∃ e : Nat, 2*k = 2^e) ↔ ∃ e : Nat, k=2^e := by
  constructor
  · rintro ⟨_|e, h⟩
    · simp at h <;> omega
    · exact ⟨e, by rw [Nat.pow_succ] at h; omega⟩
  · rintro ⟨e,rfl⟩
    exact ⟨e+1, by simp [Nat.pow_succ, Nat.mul_comm]⟩

theorem autoPowOdd (k : Nat) : (∃ e : Nat, 2*k+1 = 2^e) ↔ k=0 := by
  constructor
  · rintro ⟨_|e,h⟩
    · simp at h <;> omega
    · rw [Nat.pow_succ] at h; omega
  · rintro rfl
    exact ⟨0,rfl⟩

inductive AutoLit where
  | yes | no | ge (A : AutoLin) | dis (A B : AutoLin) | pow
deriving DecidableEq, Inhabited

def autoLitF : AutoLit → AutoF
  | .yes => .yes
  | .no => .no
  | .ge A => .ge A
  | .dis A B => .dis A B
  | .pow => .pow

def autoAtom : AutoM AutoLit where
  last
    | .yes => true
    | .no => false
    | .ge A => decide (0 ≤ A.d)
    | .dis A B => decide (0 ≤ A.d ∧ 0 ≤ B.d ∧ A.d.toNat &&& B.d.toNat = 0)
    | .pow => false
  step s j := match s with
    | .yes => .yes
    | .no => .no
    | .ge A => .ge (autoShift A j)
    | .dis A B => if autoLo A j % 2 = 1 ∧ autoLo B j % 2 = 1 then .no
      else .dis (autoShift A j) (autoShift B j)
    | .pow => if autoBit j 0 = 1 then .ge ⟨-1,0,0,0⟩ else .pow

theorem autoLitGood (s : AutoLit) : autoGood (autoLitF s) autoAtom s := by
  intro w
  induction w generalizing s with
  | nil =>
    cases s <;> simp [autoRun, autoAtom, autoLitF, autoDen, autoVal, autoRead]
    exact fun e h => (Nat.ne_of_gt (Nat.two_pow_pos e)) h.symm
  | cons j w ih =>
    simp only [autoRead, autoRun, ih]
    cases s with
    | yes | no => rfl
    | ge A =>
      simp only [autoAtom, autoLitF, autoDen, autoValShift]
      omega
    | dis A B =>
      simp only [autoAtom, autoLitF, autoDen, autoValShift]
      rw [autoDisHalf _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases h : autoLo A j % 2 = 1 ∧ autoLo B j % 2 = 1
      · rw [if_pos h]; simp [autoDen, h.1,h.2]
      · rw [if_neg h]; simp only [autoDen, h, not_false_eq_true, true_and]
    | pow =>
      have hb : autoBit j 0 < 2 := Nat.mod_lt _ (by decide)
      by_cases h : autoBit j 0 = 1
      · simp [autoAtom, h, autoLitF, autoDen, autoVal, autoPowOdd]
      · have hh : autoBit j 0 = 0 := by omega
        simp [autoAtom, hh, autoLitF, autoDen, autoPowEven]

def autoPacked (n w i : Nat) := (n >>> (w*i)) % (2^w)

def autoPackedTab (n w : Nat) : AutoM Nat :=
  ⟨fun i => autoPacked n w (9*i) == 1, fun i j => autoPacked n w (9*i+1+j.val)⟩
