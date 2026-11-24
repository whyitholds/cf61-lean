import UlamDefs
open OneAdd

def cfTerm (x : ℕ → ℕ) (t : ℕ) : Prop := ∃ i, 1 ≤ i ∧ x i = t

def cfValuePair (P : ℕ → Prop) (t v : ℕ) : Prop :=
  0 < v ∧ v < t-v ∧ P v ∧ P (t-v)

theorem cfStrictTail {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x) :
    StrictMono (fun i => x (i+1)) := strictMono_nat_of_lt_succ fun i => hx.2.2.1 (i+1) (by omega)

theorem cfValueLower {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x) (ha : 0 < a)
    {i : ℕ} (hi : 1 ≤ i) : i ≤ x i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  induction j with
  | zero => change 1 ≤ x 1; rw [hx.1]; omega
  | succ j ih =>
    have h := hx.2.2.1 (j+1) (by omega)
    have prev : j+1 ≤ x (j+1) := ih (by omega)
    change j+1+1 ≤ x (j+1+1)
    omega

theorem cfTermAbove {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x) (ha : 0 < a)
    {t : ℕ} (ht : b < t) : cfTerm x t ↔ reps x t = 1 := by
  constructor
  · rintro ⟨i,hi,rfl⟩
    have h2 : 2 < i := by
      by_contra! hf
      interval_cases i <;> simp_all [hx.1, hx.2.1] <;> first | omega | exact (not_lt_of_ge (le_of_lt (by simpa [hx.1, hx.2.1] using hx.2.2.1 1 (by omega)))) ht
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact hx.2.2.2.1 j (by omega)
  · intro hr
    by_contra hn
    have bound : ∃ j, t < x (j+1) := ⟨t,by have := cfValueLower hx ha (i := t+1) (by omega); omega⟩
    let j := Nat.find bound
    have hj : t < x (j+1) := Nat.find_spec bound
    have hj2 : 2 ≤ j := by
      have hab := hx.2.2.1 1 (by omega)
      by_contra! hf
      interval_cases j <;> simp_all [hx.1,hx.2.1] <;> omega
    have hprev : x j ≤ t := by
      have h := Nat.find_min bound (m := j-1) (show j-1 < j by omega)
      simpa [show j-1+1=j by omega] using h
    have hlt : x j < t := by
      by_contra! h
      exact hn ⟨j,by omega,by omega⟩
    exact hx.2.2.2.2 j t hj2 hlt hj hr

theorem cfValueInject {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h : x i = x j) : i = j := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact congrArg Nat.succ ((cfStrictTail hx).injective h)

theorem cfValueOrder {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) : i < j ↔ x i < x j := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact Nat.succ_lt_succ_iff.trans (cfStrictTail hx).lt_iff_lt.symm

theorem cfRepsOne {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x) (ha : 0 < a)
    (t : ℕ) : reps x t = 1 ↔ ∃! v, cfValuePair (cfTerm x) t v := by
  classical
  let A := ((Finset.range (t+1) ×ˢ Finset.range (t+1)).filter
    fun p => 1 ≤ p.1 ∧ p.1 < p.2 ∧ x p.1 + x p.2 = t)
  change A.card = 1 ↔ _
  have forwards {ij : ℕ × ℕ} (hp : ij ∈ A) : cfValuePair (cfTerm x) t (x ij.1) := by
    obtain ⟨_,i,ijlt,s⟩ := Finset.mem_filter.mp hp
    have j : 1 ≤ ij.2 := by omega
    have vlt := (cfValueOrder hx i j).1 ijlt
    have pos := cfValueLower hx ha i
    exact ⟨by omega,by omega,⟨_,i,rfl⟩,⟨_,j,by omega⟩⟩
  have backwards {v : ℕ} (h : cfValuePair (cfTerm x) t v) :
      ∃ ij ∈ A, x ij.1 = v := by
    rcases h with ⟨pv,lt,⟨i,hi,vi⟩,⟨j,hj,vj⟩⟩
    have i' := cfValueLower hx ha hi
    have j' := cfValueLower hx ha hj
    have ij := (cfValueOrder hx hi hj).2 (show x i < x j by omega)
    exact ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,hi,ij,by dsimp; omega⟩,vi⟩
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨ij,h⟩
    have hmem : ij ∈ A := by simp [h]
    refine ⟨x ij.1,forwards hmem,?_⟩
    intro v hv
    obtain ⟨kl,hkl,eq⟩ := backwards hv
    have eq' : kl=ij := by simpa [h] using hkl
    simpa [eq'] using eq.symm
  · rintro ⟨v,hv,uniq⟩
    obtain ⟨ij,hin,he⟩ := backwards hv
    refine ⟨ij, Finset.eq_singleton_iff_unique_mem.mpr ⟨hin,?_⟩⟩
    intro kl hk
    have eq := (uniq _ (forwards hk)).trans he.symm
    obtain ⟨_,ki,kh,ks⟩ := Finset.mem_filter.mp hk
    obtain ⟨_,ii,ih,is⟩ := Finset.mem_filter.mp hin
    have fst := cfValueInject hx ki ii eq
    have snd := cfValueInject hx (show 1 ≤ kl.2 by omega) (show 1 ≤ ij.2 by omega)
      (show x kl.2 = x ij.2 by omega)
    exact Prod.ext fst snd

theorem cfTermSmall {a b : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x)
    {t : ℕ} (ht : t ≤ b) : cfTerm x t ↔ t = a ∨ t = b := by
  constructor
  · rintro ⟨i,hi,rfl⟩
    have h : i ≤ 2 := by
      by_contra! h'
      have := (cfValueOrder hx (i := 2) (by omega) hi).1 h'
      rw [hx.2.1] at this
      omega
    interval_cases i <;> simp_all [hx.1,hx.2.1]
  · rintro (rfl|rfl)
    · exact ⟨1,by omega,hx.1⟩
    · exact ⟨2,by omega,hx.2.1⟩

theorem cfTermDetermined {a b T : ℕ} {x : ℕ → ℕ} (hx : IsUlam a b x) (ha : 0 < a)
    (P : ℕ → Prop) (hsmall : ∀ t ≤ b, P t ↔ t=a ∨ t=b)
    (hstep : ∀ t, b < t → t ≤ T → (P t ↔ ∃! v, cfValuePair P t v)) :
    ∀ t ≤ T, cfTerm x t ↔ P t := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htb : t ≤ b
    · exact (cfTermSmall hx htb).trans (hsmall _ htb).symm
    rw [cfTermAbove hx ha (by omega), cfRepsOne hx ha, hstep t (by omega) ht]
    apply existsUnique_congr
    intro v
    unfold cfValuePair
    by_cases h : 0 < v ∧ v < t-v
    · rw [ih v (by omega) (by omega),ih (t-v) (by omega) (by omega)]
    · tauto
