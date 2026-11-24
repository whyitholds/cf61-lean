import Statement

open OneAdd CF61

def cfIIBitRule : Prop :=
  ∀ a b : ℕ, z (a : ℤ) (b : ℤ) = if a &&& b = 0 then 1 else 0

theorem cfIIZnonneg {a b : ℤ} (h : z a b = 1) : 0 ≤ a ∧ 0 ≤ b := by
  unfold z at h
  split at h <;> simp_all

theorem cfIIUpper (H : cfIIBitRule) (m : ℕ) {u : ℤ}
    (hu : u < 2 * (K m : ℤ)) (hz : z u (u-1) = 1) : u ≤ (K m : ℤ) := by
  by_contra! h
  have hk : 0 < K m := by unfold K; positivity
  have hzn := cfIIZnonneg hz
  have hz' := H u.toNat (u-1).toNat
  rw [Int.toNat_of_nonneg hzn.1, Int.toNat_of_nonneg hzn.2, hz] at hz'
  have hzero : u.toNat &&& (u-1).toNat = 0 := by split at hz' <;> simp_all
  have hu1 : K m ≤ u.toNat := by omega
  have hu2 : K m ≤ (u-1).toNat := by omega
  have hu3 : u.toNat < 2 * K m := by omega
  have hu4 : (u-1).toNat < 2 * K m := by omega
  have a := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (i := m - 2)
    (n := u.toNat) hu1 (by simpa [K, pow_succ, mul_comm] using hu3)
  have b := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (i := m - 2)
    (n := (u-1).toNat) hu2 (by simpa [K, pow_succ, mul_comm] using hu4)
  have := congrArg (fun x : ℕ => x.testBit (m-2)) hzero
  change (u.toNat &&& (u-1).toNat).testBit (m-2) = (0 : ℕ).testBit (m-2) at this
  rw [Nat.testBit_and, a, b] at this
  simp at this

theorem cfIICenter (H : cfIIBitRule) (m : ℕ) : z (K m : ℤ) ((K m : ℤ)-1) = 1 := by
  have hk : 0 < K m := by unfold K; positivity
  have e : ((K m : ℤ) - 1) = ((K m - 1 : ℕ) : ℤ) := by omega
  rw [e, H]
  simp [K]

theorem cfIIResidues {m : ℕ} {l c r : ℤ} (h : Y m l c r = 1) :
    (r = 1 → 3*(K m : ℤ) ≤ c) ∧
    (r = 2 → c ≤ 4*(K m : ℤ)-1) ∧
    (r = 3 → 5*(K m : ℤ) ≤ c) := by
  have hk : 0 < (K m : ℤ) := by unfold K; positivity
  refine ⟨?_, ?_, ?_⟩
  all_goals rintro rfl
  all_goals simp only [Y, Int.reduceEq, false_and, ite_false, true_and] at h
  all_goals repeat' split at h
  all_goals omega

def cfIIFour (k l c : ℤ) : Prop :=
  (c ≤ 4*k-2 ∧ l < c-2*k+1 ∧ 0 ≤ l ∧ z (c-2*k+1) l = 1) ∨
  (4*k ≤ c ∧ c ≤ 6*k-2 ∧ l < c-4*k+1 ∧ 0 ≤ l ∧ z (c-4*k+1) l = 1) ∨
  (c = 6*k-1 ∧ l = -1)

theorem cfIIFourCells {m : ℕ} {l c : ℤ} (h : Y m l c 4 = 1) :
    cfIIFour (K m) l c := by
  simp [Y] at h
  unfold cfIIFour
  split at h
  · omega
  split at h
  · have hz := cfIIZnonneg h
    exact Or.inl ⟨by omega, by omega, hz.2, h⟩
  split at h
  · omega
  split at h
  · have hz := cfIIZnonneg h
    exact Or.inr (Or.inl ⟨by omega, by omega, by omega, hz.2, h⟩)
  split at h
  · unfold δ at h
    split at h <;> omega
  · omega

theorem cfIIGeometry {k l c r t d s : ℤ} (hk : 2 ≤ k)
    (hc : 2*k ≤ c) (hd : 2*k ≤ d) (hc' : c ≤ 6*k-1) (hd' : d ≤ 6*k-1)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hr' : r ≤ 4) (hs' : s ≤ 4)
    (h : 16*k*l + 4*c + r + (16*k*t + 4*d+s) = 32*k^2) :
    (l+t = 2*k-2 ∧ 4*(c+d) + r+s = 32*k) ∨
    (l+t = 2*k-3 ∧ c=6*k-1 ∧ d=6*k-1 ∧ r=4 ∧ s=4) := by
  have he : 16*k*(2*k-l-t) = 4*(c+d)+r+s := by linarith only [h]
  have hb : 2 ≤ 2*k-l-t := by
    by_contra! hh
    have hb' := mul_le_mul_of_nonneg_left (show 2*k-l-t ≤ 1 by omega) (show 0 ≤ 16*k by omega)
    linarith
  have hc2 : 2*k-l-t ≤ 3 := by
    by_contra! hh
    have hb' := mul_le_mul_of_nonneg_left (show 4 ≤ 2*k-l-t by omega) (show 0 ≤ 16*k by omega)
    linarith
  rcases (show 2*k-l-t = 2 ∨ 2*k-l-t = 3 by omega) with e | e
  · rw [e] at he
    exact Or.inl ⟨by omega, by omega⟩
  · rw [e] at he
    exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem cfIIDiag (H : cfIIBitRule) (m : ℕ) {l c t d : ℤ}
    (hc : 2*(K m : ℤ) ≤ c) (hd : 2*(K m : ℤ) ≤ d)
    (ht : l+t = 2*(K m : ℤ)-2) (he : c+d = 8*(K m : ℤ)-2)
    (hf : cfIIFour (K m) l c) (hg : cfIIFour (K m) t d) :
    l = (K m : ℤ)-1 ∧ t = (K m : ℤ)-1 ∧
    ((c = 3*(K m : ℤ)-1 ∧ d = 5*(K m : ℤ)-1) ∨
     (c = 5*(K m : ℤ)-1 ∧ d = 3*(K m : ℤ)-1)) := by
  have hcase (l c t d : ℤ) (hl : l+t = 2*(K m : ℤ)-2) (he : c+d = 8*(K m : ℤ)-2)
      (ha : c ≤ 4*(K m : ℤ)-2 ∧ l < c-2*(K m : ℤ)+1 ∧ 0 ≤ l ∧ z (c-2*(K m : ℤ)+1) l = 1)
      (hb : 4*(K m : ℤ) ≤ d ∧ d ≤ 6*(K m : ℤ)-2 ∧ t < d-4*(K m : ℤ)+1 ∧ 0 ≤ t ∧ z (d-4*(K m : ℤ)+1) t = 1) :
      l = (K m : ℤ)-1 ∧ t = (K m : ℤ)-1 ∧ c = 3*(K m : ℤ)-1 ∧ d = 5*(K m : ℤ)-1 := by
    have ha' : l ≤ (K m : ℤ)-1 := by
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      have h := cfIIUpper H m (u := c-2*(K m : ℤ)+1) (by omega)
        (by convert ha4 using 2; omega)
      omega
    have hb' : t ≤ (K m : ℤ)-1 := by
      obtain ⟨hb1,hb2,hb3,hb4,hb5⟩ := hb
      have h := cfIIUpper H m (u := d-4*(K m : ℤ)+1) (by omega)
        (by convert hb5 using 2; omega)
      omega
    omega
  rcases hf with ha | hb | hp <;> rcases hg with hd1 | hd2 | hd3
  all_goals first
    | omega
    | have hh := hcase l c t d ht he ha hd2; omega
    | have hh := hcase t d l c (by omega) (by omega) hd1 hb; omega

theorem cfIIPairOnly (H : cfIIBitRule) (hcoords : CF61_Coords) (hc : CF61_Closed)
    (m : ℕ) (hm : 3 ≤ m) {p q : ℕ} (hg : IsPair m (n₀ m) p q) :
    p = 16 * K m^2 - 4 * K m ∧ q = 16 * K m^2 + 4 * K m := by
  rcases hg with ⟨hp, hpq, hsum, ha, hb⟩
  have hk : 2 ≤ K m := by
    unfold K
    calc
      2 = 2^1 := by decide
      _ ≤ 2^(m-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hki : (2 : ℤ) ≤ (K m : ℤ) := by exact_mod_cast hk
  obtain ⟨l,c,r,hpcoords⟩ := (hcoords m hm p hp).1
  obtain ⟨t,d,s,hqcoords⟩ := (hcoords m hm q (by omega)).1
  have hap : Y m l c r = 1 := (hc.2 m hm p hp (by omega) l c r hpcoords).symm.trans ha
  have hbq : Y m t d s = 1 := (hc.2 m hm q (by omega) (by omega) t d s hqcoords).symm.trans hb
  obtain ⟨ep,ac,bc,ar,br⟩ := hpcoords
  obtain ⟨eq,ad,bd,as',bs⟩ := hqcoords
  have hsum' : (p : ℤ) + q = 32*(K m : ℤ)^2 := by
    unfold n₀ at hsum
    exact_mod_cast hsum
  have hg' := cfIIGeometry (l := l) (t := t) hki ac ad bc bd ar as' br bs (by linarith [ep,eq,hsum'])
  have ha' := cfIIResidues hap
  have hb' := cfIIResidues hbq
  rcases hg' with ⟨ht,he⟩ | ⟨ht,hci,hdi,rfl,rfl⟩
  · have hr4 : r = 4 ∧ s = 4 := by omega
    obtain ⟨rfl,rfl⟩ := hr4
    have hd' := cfIIDiag H m ac ad ht (by omega) (cfIIFourCells hap) (cfIIFourCells hbq)
    obtain ⟨h1,h2,h3⟩ := hd'
    subst l t
    have hsub : 4*K m ≤ 16*K m^2 := by nlinarith [Nat.mul_self_le_mul_self hk]
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sub hsub]
    push_cast
    rcases h3 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · constructor
      · linarith
      · exact_mod_cast (show (q : ℤ) = 16*(K m : ℤ)^2 + 4*(K m : ℤ) by linarith)
    · have hpq' : (p : ℤ) < q := by exact_mod_cast hpq
      exfalso
      linarith
  · have ha'' := cfIIFourCells hap
    have hb'' := cfIIFourCells hbq
    unfold cfIIFour at ha'' hb''
    omega

theorem cfIIExistsPair (H : cfIIBitRule) (hc : CF61_Closed) (m : ℕ) (hm : 3 ≤ m) :
    IsPair m (n₀ m) (16 * K m^2 - 4 * K m) (16 * K m^2 + 4 * K m) := by
  have hk : 2 ≤ K m := by
    unfold K
    calc
      2 = 2^1 := by decide
      _ ≤ 2^(m-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hki : (2 : ℤ) ≤ (K m : ℤ) := by exact_mod_cast hk
  have hk2 : K m ≤ K m^2 := Nat.le_self_pow (by decide) _
  have hsub : 4 * K m ≤ 16 * K m^2 := by omega
  have hc1 : Coords m (16*K m^2 - 4*K m) ((K m : ℤ)-1) (3*(K m : ℤ)-1) 4 := by
    unfold Coords
    dsimp only
    refine ⟨?_, ?_, ?_, by decide, by decide⟩
    · push_cast [Nat.cast_sub hsub]
      ring
    · linarith only [hki]
    · linarith only [hki]
  have hc2 : Coords m (16*K m^2 + 4*K m) ((K m : ℤ)-1) (5*(K m : ℤ)-1) 4 := by
    unfold Coords
    dsimp only
    refine ⟨?_, ?_, ?_, by decide, by decide⟩
    · push_cast
      ring
    · linarith only [hki]
    · linarith only [hki]
  have h1 := hc.2 m hm _ (by omega) (by unfold n₀; omega) _ _ _ hc1
  have h2 := hc.2 m hm _ (by omega) (by unfold n₀; omega) _ _ _ hc2
  have hval := cfIICenter H m
  refine ⟨by omega, by omega, by unfold n₀; omega, h1.trans ?_, h2.trans ?_⟩
  · simp only [Y, Int.reduceEq, false_and, ite_false, true_and]
    repeat' split
    all_goals first | omega | convert hval using 2 <;> omega
  · simp only [Y, Int.reduceEq, false_and, ite_false, true_and]
    repeat' split
    all_goals first | omega | convert hval using 2 <;> omega

theorem cfPartIIWithBits (H : cfIIBitRule) (hcoords : CF61_Coords) (hc : CF61_Closed) :
    CF61_PartII := by
  refine ⟨hc.1, ?_⟩
  intro m hm
  have hcan := cfIIExistsPair H hc m hm
  refine ⟨?_,hcan⟩
  unfold S
  apply Finset.card_eq_one.mpr
  refine ⟨(16*K m^2-4*K m,16*K m^2+4*K m), ?_⟩
  ext v
  obtain ⟨p,q⟩ := v
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · exact fun h => cfIIPairOnly H hcoords hc m hm h.2
  · rintro ⟨rfl,rfl⟩
    have hsum := hcan.2.2.1
    exact ⟨⟨by omega, by omega⟩,hcan⟩
