import CorOddCount

open OneAdd CF61

def corEvenValues (m : ℕ) : Finset ℕ := {4, 8*K m+2, 16*K m, Nb m}

theorem corEvenValuesMem {m N : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x) :
    N ∈ corEvenValues m ↔ N ≤ Nb m ∧ N % 2 = 0 ∧ cfTerm x N := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  obtain ⟨scale, lower⟩ := cfEndpointScale hm
  have list : N ∈ corEvenValues m ↔ cfEvenSeed m N ∨ N = Nb m := by
    simp [corEvenValues, cfEvenSeed, or_assoc]
  rw [list]
  constructor
  · intro h
    have bounds : N ≤ Nb m ∧ N % 2 = 0 := by
      rcases h with (h | h | h) | h <;> omega
    exact ⟨bounds.1, bounds.2, (corTermModel hm hx N bounds.1).mpr (h.imp Or.inl id)⟩
  · rintro ⟨hle,he,ht⟩
    rwa [corTermModel hm hx N hle, cfEvenModelIff hm he] at ht

theorem corEvenValuesCard {m : ℕ} (hm : 3 ≤ m) : (corEvenValues m).card = 4 := by
  have hb := cfBFromK m hm
  have hk := cfKTwo m hm
  obtain ⟨scale, lower⟩ := cfEndpointScale hm
  unfold corEvenValues
  rw [Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

theorem corAllValuesMem {m N : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x) :
    N ∈ corOddValues m x ∪ corEvenValues m ↔ N ≤ Nb m ∧ cfTerm x N := by
  have scale := (cfEndpointScale hm).1
  rw [Finset.mem_union, corOddValuesMem, corEvenValuesMem hm hx]
  constructor
  · rintro (⟨h,_,ht⟩ | ⟨h,_,ht⟩)
    · exact ⟨h.le,ht⟩
    · exact ⟨h,ht⟩
  · rintro ⟨h,ht⟩
    by_cases he : N % 2 = 0
    · exact Or.inr ⟨h,he,ht⟩
    · exact Or.inl ⟨by omega, by omega, ht⟩

def corIndices (m : ℕ) (x : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (Nb m + 1)).filter fun i => 1 ≤ i ∧ x i ≤ Nb m

theorem corIndicesMem {m i : ℕ} {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x) :
    i ∈ corIndices m x ↔ 1 ≤ i ∧ x i ≤ Nb m := by
  simp only [corIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    have := cfValueLower hx (by decide) h.1
    exact ⟨by omega, h⟩

theorem corRank {m : ℕ} (hm : 3 ≤ m) {x : ℕ → ℕ} (hx : IsUlam 4 (b m) x) :
    (corIndices m x).card = 4*3^(m-1)+2 ∧ x (4*3^(m-1)+2) = Nb m := by
  have disj : Disjoint (corOddValues m x) (corEvenValues m) := by
    apply Finset.disjoint_left.mpr
    intro N hodd heven
    have ho := (corOddValuesMem.mp hodd).2.1
    have he := ((corEvenValuesMem hm hx).mp heven).2.1
    omega
  have count : (corIndices m x).card = 4*3^(m-1)+2 := by
    calc
      _ = (corOddValues m x ∪ corEvenValues m).card := by
        apply Finset.card_bij (fun i _ => x i)
        · intro i hi
          obtain ⟨hi,hv⟩ := (corIndicesMem hx).mp hi
          exact (corAllValuesMem hm hx).mpr ⟨hv,i,hi,rfl⟩
        · intro i hi j hj he
          exact cfValueInject hx ((corIndicesMem hx).mp hi).1 ((corIndicesMem hx).mp hj).1 he
        · intro N h
          obtain ⟨hle,i,hi,he⟩ := (corAllValuesMem hm hx).mp h
          exact ⟨i,(corIndicesMem hx).mpr ⟨hi,by rwa [he]⟩,he⟩
      _ = _ := by
        rw [Finset.card_union_of_disjoint disj, corEvenValuesCard hm, corOddValuesCard hm hx]
        have := corOddCellsCard hm
        omega
  obtain ⟨last,hlast,hval⟩ : cfTerm x (Nb m) := (corTermModel hm hx _ le_rfl).mpr (Or.inr rfl)
  have interval : corIndices m x = Finset.Icc 1 last := by
    ext i
    rw [corIndicesMem hx, Finset.mem_Icc]
    constructor
    · rintro ⟨hi,hv⟩
      refine ⟨hi, ?_⟩
      by_contra! h
      have := (cfValueOrder hx hlast hi).mp h
      omega
    · rintro ⟨hi,hle⟩
      refine ⟨hi, ?_⟩
      by_contra! h
      have := (cfValueOrder hx hlast hi).mpr (show x last < x i by omega)
      omega
  have hcard : (corIndices m x).card = last := by rw [interval, Nat.card_Icc]; omega
  exact ⟨count, by rwa [← count, hcard]⟩
