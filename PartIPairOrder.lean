import PartISpec

open CF61

def piCellBox (k : ℕ) : Finset PICell :=
  (((Finset.range (2*k) ×ˢ Finset.range (2*k)) ×ˢ (Finset.univ : Finset (Fin 6))).image
    (fun p => ⟨p.1.1,p.1.2,p.2⟩))

noncomputable def piCellPairs (k n : ℕ) : Finset (PICell × PICell) := by
  classical
  exact ((piCellBox k) ×ˢ (piCellBox k)).filter
    (fun p => PIValid k p.1 ∧ PIValid k p.2 ∧ PICellValue k p.1 + PICellValue k p.2 = n)

theorem piCellInBox {k : ℕ} {x : PICell} (h : PIValid k x) : x ∈ piCellBox k := by
  apply Finset.mem_image.mpr
  exact ⟨((x.u,x.v),x.kind),by simp [h.1,h.2.1],rfl⟩

theorem piMemCellPairs {k n : ℕ} {x y : PICell} :
    (x,y) ∈ piCellPairs k n ↔ PIValid k x ∧ PIValid k y ∧ PICellValue k x+PICellValue k y=n := by
  classical
  simp only [piCellPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨piCellInBox h.1,piCellInBox h.2.1⟩,h⟩

theorem piPositiveOut (k : ℕ) (hk : 0 < k) (x : PICell) : 1 ≤ PICellValue k x := by
  rcases x with ⟨u,v,t⟩
  fin_cases t <;> simp [PICellValue, PITagShift, PITagResidue] <;> omega

def piOrderedBits (m n : ℕ) :=
  ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter
    fun ij => 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1+ij.2=n ∧ y m ij.1=1 ∧ y m ij.2=1)

theorem piMemOrderedBits {m n i j : ℕ} : (i,j) ∈ piOrderedBits m n ↔
    1 ≤ i ∧ 1 ≤ j ∧ i+j=n ∧ y m i=1 ∧ y m j=1 := by
  simp only [piOrderedBits, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨by omega,by omega⟩,h⟩

theorem piOrderedCard {m n : ℕ} (hS : S m n=1) :
    (piOrderedBits m n).card=2 ∨ (piOrderedBits m n).card=3 := by
  classical
  let D := ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun pq => IsPair m n pq.1 pq.2)
  change D.card=1 at hS
  obtain ⟨⟨a,b⟩,hD⟩ := Finset.card_eq_one.mp hS
  have haD : (a,b) ∈ D := by simp [hD]
  have hp : IsPair m n a b := (Finset.mem_filter.mp haD).2
  obtain ⟨ha,hab,hs,ya,yb⟩ := hp
  have unique {i j : ℕ} (h : IsPair m n i j) : (i,j)=(a,b) := by
    have h' : (i,j) ∈ D := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by obtain ⟨_,_,he,_,_⟩ := h; omega),
        Finset.mem_range.mpr (by obtain ⟨_,_,he,_,_⟩ := h; omega)⟩,h⟩
    simpa [hD] using h'
  have hlow : ({(a,b),(b,a)} : Finset (ℕ × ℕ)) ⊆ piOrderedBits m n := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact piMemOrderedBits.mpr ⟨ha,by omega,hs,ya,yb⟩
    · exact piMemOrderedBits.mpr ⟨by omega,ha,by omega,yb,ya⟩
  have htop : piOrderedBits m n ⊆ ({(a,b),(b,a),(n/2,n/2)} : Finset (ℕ × ℕ)) := by
    rintro ⟨i,j⟩ h
    obtain ⟨hi,hj,he,yi,yj⟩ := piMemOrderedBits.mp h
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases lt_trichotomy i j with hlt|heq|hgt
    · exact Or.inl (unique ⟨hi,hlt,he,yi,yj⟩)
    · exact Or.inr (Or.inr (Prod.ext (by dsimp; omega) (by dsimp; omega)))
    · have hu := unique (i:=j) (j:=i) ⟨hj,hgt,by omega,yj,yi⟩
      exact Or.inr (Or.inl (congrArg Prod.swap hu))
  have habp : (a,b) ≠ (b,a) := by intro h; have := congrArg Prod.fst h; dsimp at this; omega
  have hL := Finset.card_le_card hlow
  have hU := Finset.card_le_card htop
  have habq : (a,b) ≠ (n/2,n/2) := by rintro h; simp only [Prod.mk.injEq] at h; omega
  have hbaq : (b,a) ≠ (n/2,n/2) := by rintro h; simp only [Prod.mk.injEq] at h; omega
  simp [habp,habq,hbaq] at hL hU
  omega

theorem piCardOrderEq (m n : ℕ) (hn : n < n₀ m)
    (support : ∀ t, 1 ≤ t → t < n₀ m →
      (y m t=1 ↔ ∃ x, PIValid (K m) x ∧ PICellValue (K m) x=t))
    (inj : ∀ {x x'}, PIValid (K m) x → PIValid (K m) x' →
      PICellValue (K m) x=PICellValue (K m) x' → 1 ≤ PICellValue (K m) x → x=x') :
    (piCellPairs (K m) n).card=(piOrderedBits m n).card := by
  have hk : 0 < K m := by unfold K; positivity
  apply Finset.card_bij (fun p _ => (PICellValue (K m) p.1,PICellValue (K m) p.2))
  · rintro ⟨x,z⟩ h
    obtain ⟨hx,hz,he⟩ := piMemCellPairs.mp h
    have hx' := piPositiveOut (K m) hk x
    have hz' := piPositiveOut (K m) hk z
    exact piMemOrderedBits.mpr ⟨hx',hz',he,(support _ hx' (by omega)).2 ⟨x,hx,rfl⟩,
      (support _ hz' (by omega)).2 ⟨z,hz,rfl⟩⟩
  · rintro ⟨x,z⟩ hx ⟨x',z'⟩ hx' he
    obtain ⟨h1,h2,_⟩ := piMemCellPairs.mp hx
    obtain ⟨h3,h4,_⟩ := piMemCellPairs.mp hx'
    exact Prod.ext (inj h1 h3 (congrArg Prod.fst he) (piPositiveOut _ hk _))
      (inj h2 h4 (congrArg Prod.snd he) (piPositiveOut _ hk _))
  · rintro ⟨i,j⟩ h
    obtain ⟨hi,hj,he,yi,yj⟩ := piMemOrderedBits.mp h
    obtain ⟨x,hx,ex⟩ := (support i hi (by omega)).1 yi
    obtain ⟨z,hz,ez⟩ := (support j hj (by omega)).1 yj
    exact ⟨(x,z),piMemCellPairs.mpr ⟨hx,hz,by omega⟩,Prod.ext ex ez⟩

theorem piTwoOrThree (m n : ℕ) (hn : n < n₀ m)
    (support : ∀ t, 1 ≤ t → t < n₀ m →
      (y m t=1 ↔ ∃ x, PIValid (K m) x ∧ PICellValue (K m) x=t))
    (inj : ∀ {x x'}, PIValid (K m) x → PIValid (K m) x' →
      PICellValue (K m) x=PICellValue (K m) x' → 1 ≤ PICellValue (K m) x → x=x')
    (h : S m n=1) :
    (piCellPairs (K m) n).card=2 ∨ (piCellPairs (K m) n).card=3 := by
  rw [piCardOrderEq m n hn support inj]
  exact piOrderedCard h
