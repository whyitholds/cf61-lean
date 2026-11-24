import PartIInd

theorem piMinSumCong {α : Type*} (s : Finset α) (f g : α → ℕ)
    (h : ∀ i ∈ s, min 4 (f i) = min 4 (g i)) :
    min 4 (∑ i ∈ s, f i) = min 4 (∑ i ∈ s, g i) := by
  rw [← piClipSum s f, ← piClipSum s g]
  congr 1
  exact Finset.sum_congr rfl h

def piWeightRule : Prop :=
  ∀ row ah d r : ℕ, ah < 2 → d < 4 → r < 4 →
    piAcceptCount row ah d r =
    ∑ s ∈ Finset.range 72, ∑ t ∈ Finset.range 8, piDigit (piCol row s) t *
      (piTailChoices ah d r (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3)).card

theorem piAcceptedEq (wRule : piWeightRule) {k a v row ah d r : ℕ}
    (hh : ah < 2) (hd : d < 4) (hr : r < 4) (hRel : piLowRel k a v row) :
    min 4 (piAcceptCount row ah d r) = min 4 (piTrueCount k a v ah d r) := by
  rw [wRule _ _ _ _ hh hd hr, piTrueCount]
  apply piMinSumCong
  intro s hs
  simp only [Finset.mem_range] at hs
  let F := fun t : ℕ => piNumLow k a v (t/2) (t%2) s
  let W := fun t : ℕ => (piTailChoices ah d r (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3)).card
  calc
    _ = min 4 (∑ t ∈ Finset.range 8, min 4 (F t) * W t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [hRel.2.2 _ _ hs (Finset.mem_range.mp ht)]
    _ = _ := piClipMulSum (Finset.range 8) F W

theorem piGoodCount {row ah D r : ℕ} (hg : piGood row = true) (ha : ah < 2) (hd : D < 4)
    (hr : r < 4) (hw : piAllowed row ah D = true) :
    piAcceptCount row ah D r ≠ 2 ∧ piAcceptCount row ah D r ≠ 3 := by
  let z := 16*ah + 4*D + r
  have hz : z < 32 := by dsimp [z]; omega
  have h1 : z/16 = ah := by dsimp [z]; omega
  have h2 : z/4%4 = D := by dsimp [z]; omega
  have h3 : z%4 = r := by dsimp [z]; omega
  have h := List.all_eq_true.mp hg z (List.mem_range.mpr hz)
  simp [h1,h2,h3,hw] at h
  exact h

theorem piParamRange {k a v ah D r : ℕ} (hk : 2 ≤ k) (ha : a < k) (hv : v < k)
    (hD : D < 4) (hr : r < 4)
    (h : 20*k+3 < 16*k*(k*ah+a)+4*k*D+4*v+r) :
    0 < ah ∨ 1 < a ∨ (a = 1 ∧ (1 < D ∨ (D = 1 ∧ 0 < v))) := by
  by_contra hn
  push Not at hn
  have hsmall : a ≤ 1 := by omega
  have h0 : ah = 0 := by omega
  rw [h0, Nat.mul_zero, Nat.zero_add] at h
  interval_cases a <;> interval_cases D <;> simp_all <;> omega

theorem piTrueCountGood
    (liftRule : piLiftRule) (first : piVerifiedFirst) (step : piVerifiedStep)
    (wRule : piWeightRule) (stGood : ∀ i : ℕ, i < 683 → piGood piRowList[i]! = true)
    {d a v ah D r : ℕ} (hdp : 0 < d) (ha : a < 2^d) (hv : v < 2^d)
    (hah : ah < 2) (hD : D < 4) (hr : r < 4)
    (h : 20*2^d+3 < 16*2^d*(2^d*ah+a)+4*2^d*D+4*v+r) :
    piTrueCount (2^d) a v ah D r ≠ 2 ∧ piTrueCount (2^d) a v ah D r ≠ 3 := by
  obtain ⟨i,hi,hRel⟩ := piReach liftRule first step d hdp a v ha hv
  let vrow := piRowList[i]!
  have hk : 2 ≤ 2^d := calc
    2 = 2^1 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hpar := piParamRange hk ha hv hD hr h
  have hallow : piAllowed vrow ah D = true := by
    simp [piAllowed, vrow, hRel.1, hRel.2.1]
    omega
  obtain ⟨h2,h3⟩ := piGoodCount (stGood i hi) hah hD hr hallow
  have he := piAcceptedEq wRule hah hD hr hRel
  omega

theorem piDecomp {k n : ℕ} (hk : 2 ≤ k) (hmax : n < 32*k^2) :
    ∃ a v ah D r : ℕ, a < k ∧ v < k ∧ ah < 2 ∧ D < 4 ∧ r < 4 ∧
      n = 16*k*(k*ah+a)+4*k*D+4*v+r := by
  let A := n / (16*k)
  let R := n % (16*k)
  let D := R / (4*k)
  let t := R % (4*k)
  have hk0 : 0 < k := by omega
  have h16 : 0 < 16*k := by omega
  have h4 : 0 < 4*k := by omega
  have hA : A < 2*k := (Nat.div_lt_iff_lt_mul h16).mpr (by nlinarith)
  have hR : R < 16*k := Nat.mod_lt _ h16
  have hD : D < 4 := (Nat.div_lt_iff_lt_mul h4).mpr (by omega)
  have ht : t < 4*k := Nat.mod_lt _ h4
  have hv : t/4 < k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have hah : A/k < 2 := (Nat.div_lt_iff_lt_mul hk0).mpr hA
  have hAeq := Nat.div_add_mod A k
  have hneq := Nat.div_add_mod n (16*k)
  have hReq := Nat.div_add_mod R (4*k)
  have hteq := Nat.div_add_mod t 4
  refine ⟨A%k,t/4,A/k,D,t%4,Nat.mod_lt _ hk0,hv,hah,hD,by omega,?_⟩
  change k*(A/k)+A%k = A at hAeq
  change 16*k*A+R = n at hneq
  change 4*k*D+t = R at hReq
  rw [hAeq]
  omega
