import UlamDefs

open OneAdd

def cfHistoryPairs (k : ℕ) (f : ℕ → ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (k+1)) ×ˢ (Finset.range (k+1))).filter
    fun p => 1 ≤ p.1 ∧ p.1 < p.2 ∧ f p.1 + f p.2 = m

theorem cfMemHistoryPairs (k m i j : ℕ) (f : ℕ → ℕ) :
    (i,j) ∈ cfHistoryPairs k f m ↔ 1 ≤ i ∧ i < j ∧ j ≤ k ∧ f i + f j = m := by
  simp only [cfHistoryPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem cfHistoryPairsCongr {k : ℕ} {f g : ℕ → ℕ}
    (h : ∀ i, i ≤ k → f i = g i) (m : ℕ) :
    cfHistoryPairs k f m = cfHistoryPairs k g m := by
  ext ⟨i,j⟩
  simp only [cfMemHistoryPairs]
  constructor <;> rintro ⟨hai,hij,hj,he⟩ <;> refine ⟨hai,hij,hj,?_⟩
  · rwa [← h i (by omega), ← h j hj]
  · rwa [h i (by omega), h j hj]

noncomputable def cfUlamBuild (a b n : ℕ) : ℕ :=
  Nat.strongRecOn n fun t parts =>
    if t = 0 then 0 else if t = 1 then a else if t = 2 then b else
      let g := fun i => if hi : i < t then parts i hi else 0
      sInf {m : ℕ | g (t-1) < m ∧ (cfHistoryPairs (t-1) g m).card = 1}

theorem cfBuildZero (a b : ℕ) : cfUlamBuild a b 0 = 0 := by
  conv_lhs => rw [cfUlamBuild, Nat.strongRecOn_eq]
  rfl

theorem cfBuildOne (a b : ℕ) : cfUlamBuild a b 1 = a := by
  conv_lhs => rw [cfUlamBuild, Nat.strongRecOn_eq]
  rfl

theorem cfBuildTwo (a b : ℕ) : cfUlamBuild a b 2 = b := by
  conv_lhs => rw [cfUlamBuild, Nat.strongRecOn_eq]
  rfl

theorem cfBuildNext (a b k : ℕ) :
    cfUlamBuild a b (k+3) =
    sInf {m : ℕ | cfUlamBuild a b (k+2) < m ∧
        (cfHistoryPairs (k+2) (cfUlamBuild a b) m).card = 1} := by
  let f := cfUlamBuild a b
  let g := fun i => if i < k+3 then f i else 0
  have eq : cfUlamBuild a b (k+3) =
      sInf {m : ℕ | g (k+2) < m ∧ (cfHistoryPairs (k+2) g m).card = 1} := by
    conv_lhs => rw [cfUlamBuild, Nat.strongRecOn_eq]
    simp only [show ¬ k+3 = 0 by omega, show ¬ k+3 = 1 by omega,
      show ¬ k+3 = 2 by omega, ite_false]
    rfl
  rw [eq]
  have hg : ∀ i, i ≤ k+2 → g i = f i := by
    intro i hi
    simp [g,show i < k+3 by omega]
  congr 1
  ext m
  change (g (k+2) < m ∧ _ = 1) ↔ (f (k+2) < m ∧ _ = 1)
  rw [cfHistoryPairsCongr hg m,hg (k+2) le_rfl]

theorem cfGreatestPair (k : ℕ) (f : ℕ → ℕ)
    (h : ∀ i j, i ≤ j → j ≤ k+2 → f i ≤ f j)
    (hs : ∀ i j, i < j → j ≤ k+2 → f i < f j) :
    (cfHistoryPairs (k+2) f (f (k+1) + f (k+2))).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨(k+1,k+2), ?_⟩
  ext ⟨i,j⟩
  simp only [cfMemHistoryPairs, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨_,hij,hjk,he⟩
    have hi : i ≤ k+1 := by omega
    have hjle := h j (k+2) hjk (by omega)
    have hiEq : i = k+1 := by
      by_contra hc
      have := hs i (k+1) (by omega) (by omega)
      omega
    omega
  · rintro ⟨rfl,rfl⟩
    omega

theorem cfMonoUpTo {f : ℕ → ℕ} {k : ℕ}
    (hs : ∀ i, i < k → f i < f (i+1)) :
    ∀ i j, i ≤ j → j ≤ k → f i ≤ f j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro; rfl
  | succ j _ ih =>
    intro hj
    exact le_trans (ih (by omega)) (le_of_lt (hs j (by omega)))

theorem cfBuildHasStep (a b k : ℕ)
    (hs : ∀ i, i < k+2 → cfUlamBuild a b i < cfUlamBuild a b (i+1)) :
    cfUlamBuild a b (k+2) < cfUlamBuild a b (k+3) ∧
    (cfHistoryPairs (k+2) (cfUlamBuild a b) (cfUlamBuild a b (k+3))).card = 1 := by
  let f := cfUlamBuild a b
  have hle := cfMonoUpTo hs
  have hlt : ∀ i j, i < j → j ≤ k+2 → f i < f j := by
    intro i j hij hj
    exact lt_of_lt_of_le (hs i (by omega)) (hle (i+1) j (by omega) hj)
  let goals := {m : ℕ | f (k+2) < m ∧ (cfHistoryPairs (k+2) f m).card = 1}
  have hpos := hlt 0 (k+1) (by omega) (by omega)
  have hex : goals.Nonempty :=
    ⟨f (k+1) + f (k+2), by
      refine ⟨by omega,cfGreatestPair k f hle hlt⟩⟩
  have hm := Nat.sInf_mem hex
  change f (k+3) ∈ goals
  rw [show f (k+3) = sInf goals from cfBuildNext a b k]
  exact hm

theorem cfBuildStrict (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    StrictMono (cfUlamBuild a b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => change cfUlamBuild a b 0 < cfUlamBuild a b 1; simpa only [cfBuildZero, cfBuildOne] using ha
    | 1 => change cfUlamBuild a b 1 < cfUlamBuild a b 2; simpa only [cfBuildOne, cfBuildTwo] using hab
    | k+2 => exact (cfBuildHasStep a b k ih).1

theorem cfGlobalCount {f : ℕ → ℕ} (hf : StrictMono f) {k m : ℕ}
    (hm : m ≤ f (k+1)) : reps f m = (cfHistoryPairs k f m).card := by
  unfold reps
  congr 1
  ext ⟨i,j⟩
  simp only [cfMemHistoryPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, hi,hij,he⟩
    refine ⟨hi,hij,?_,he⟩
    by_contra hc
    have h1 := hf.monotone (show k+1 ≤ j by omega)
    have h2 := hf (show 0 < i by omega)
    omega
  · rintro ⟨hi,hij,_,he⟩
    have hj : j ≤ f j := hf.id_le j
    exact ⟨⟨by omega,by omega⟩,hi,hij,he⟩

theorem cfUlamExists : UlamExists := by
  intro a b ha hab
  let f := cfUlamBuild a b
  have hf : StrictMono f := cfBuildStrict a b ha hab
  refine ⟨f,cfBuildOne a b,cfBuildTwo a b,fun i _ => hf (by omega),?_,?_⟩
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
    rw [cfGlobalCount hf (le_refl (f (k+3)))]
    exact (cfBuildHasStep a b k (fun i _ => hf (by omega))).2
  · intro n m hn hl hr hcount
    obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
    rw [cfGlobalCount hf (le_of_lt hr)] at hcount
    have hmem : m ∈ {t : ℕ | f (k+2) < t ∧ (cfHistoryPairs (k+2) f t).card = 1} :=
      ⟨hl,hcount⟩
    have hmin := Nat.sInf_le hmem
    rw [← cfBuildNext a b k] at hmin
    exact (not_le.mpr hr) hmin
