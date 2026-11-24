import MainBits
open CF61

def cfOffsetPair (m s d : ℕ) : Prop :=
  d < s-d ∧ cfOffset m d = 1 ∧ cfOffset m (s-d) = 1

theorem cfCountOffsets (eqs : BitsEquations) {m : ℕ} (hm : 3 ≤ m) (s : ℕ) :
    S m (16*K m+s)=1 ↔ ∃! d, cfOffsetPair m s d := by
  classical
  let n := 16*K m+s
  let A := ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun pq => IsPair m n pq.1 pq.2)
  change A.card = 1 ↔ _
  have hk := cfKTwo m hm
  have fg {ij : ℕ × ℕ} (hmem : ij ∈ A) :
      8*K m ≤ ij.1 ∧ 8*K m ≤ ij.2 ∧ cfOffsetPair m s (ij.1-8*K m) := by
    have h := (Finset.mem_filter.mp hmem).2
    rcases h with ⟨hi,lt,hs,li,lj⟩
    dsimp [n] at hs
    have e1 : 8*K m ≤ ij.1 := by
      by_contra! h
      have := (eqs m hm).1 _ hi h
      omega
    have e2 : 8*K m ≤ ij.2 := by omega
    refine ⟨e1,e2,?_⟩
    unfold cfOffsetPair cfOffset
    refine ⟨by omega,?_,?_⟩
    · simpa [show 8*K m+(ij.1-8*K m)=ij.1 by omega] using li
    · simpa [show 8*K m+(s-(ij.1-8*K m))=ij.2 by omega] using lj
  have gf {d : ℕ} (h : cfOffsetPair m s d) :
      (8*K m+d,8*K m+(s-d)) ∈ A := by
    rcases h with ⟨lt,h1,h2⟩
    apply Finset.mem_filter.mpr
    dsimp [n]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩,by omega,by omega,by omega,h1,h2⟩
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨ij,h⟩
    have hi : ij ∈ A := by simp [h]
    refine ⟨_,(fg hi).2.2,?_⟩
    intro d hd
    have hh := gf hd
    rw [h,Finset.mem_singleton] at hh
    have := congrArg Prod.fst hh
    dsimp at this
    omega
  · rintro ⟨d,hd,hu⟩
    refine ⟨_,Finset.eq_singleton_iff_unique_mem.mpr ⟨gf hd,?_⟩⟩
    intro ij h
    obtain ⟨hb1,hb2,hp⟩ := fg h
    have h1 := hu _ hp
    have h2 := (Finset.mem_filter.mp h).2.2.2.1
    dsimp [n] at h2
    apply Prod.ext <;> dsimp <;> omega

theorem cfEarlyOffsets (eqs : BitsEquations) {m s d : ℕ} (hm : 3 ≤ m)
    (hs : s ≤ 4*K m+3) (hd : d ≤ s) :
    cfOffset m d = 1 ↔ d%2=0 ∨ d=4*K m+1 := by
  have hk := cfKTwo m hm
  have hp := cfEarlyBit eqs m hm (d := d) (by omega)
  have odd := cfFirstOdd eqs m hm
  constructor
  · intro h
    by_contra! hn
    by_cases lt : d<4*K m+1
    · have := hp.2 lt (by omega); omega
    have eq : d=4*K m+3 := by omega
    rw [eq,odd.2] at h
    contradiction
  · rintro (he|he)
    · exact hp.1 he
    · simpa [he] using odd.1

theorem cfShortPairShape (eqs : BitsEquations) {m s d : ℕ} (hm : 3 ≤ m)
    (hs : s ≤ 4*K m+3) :
    cfOffsetPair m s d ↔ d<s-d ∧ (d%2=0 ∨ d=4*K m+1) ∧
      ((s-d)%2=0 ∨ s-d=4*K m+1) := by
  by_cases hd : d<s-d
  · simp only [cfOffsetPair,hd,true_and,cfEarlyOffsets eqs hm hs (show d ≤ s by omega),
      cfEarlyOffsets eqs hm hs (show s-d ≤ s by omega)]
  · simp [cfOffsetPair,hd]

theorem cfShortCount (eqs : BitsEquations) {m s : ℕ} (hm : 3 ≤ m) (hs : s ≤ 4*K m+3) :
    S m (16*K m+s)=1 ↔ s=2 ∨ s=4 ∨ s=4*K m+1 ∨ s=4*K m+3 := by
  have hk := cfKTwo m hm
  rw [cfCountOffsets eqs hm]
  have hpair := fun d => cfShortPairShape (d := d) eqs hm hs
  constructor
  · rintro ⟨d,hd,hu⟩
    by_contra! h
    have b1 := (hpair d).1 hd
    have h0 : cfOffsetPair m s 0 := (hpair 0).2 (by omega)
    have h2 : cfOffsetPair m s 2 := (hpair 2).2 (by omega)
    have := hu _ h0
    have := hu _ h2
    omega
  · rintro (he|he|he|he)
    · refine ⟨0,(hpair 0).2 (by omega),?_⟩
      intro d hd; have := (hpair d).1 hd; omega
    · refine ⟨0,(hpair 0).2 (by omega),?_⟩
      intro d hd; have := (hpair d).1 hd; omega
    · refine ⟨0,(hpair 0).2 (by omega),?_⟩
      intro d hd; have := (hpair d).1 hd; omega
    · refine ⟨2,(hpair 2).2 (by omega),?_⟩
      intro d hd; have := (hpair d).1 hd; omega

theorem cfLateException (eqs : BitsEquations) {m : ℕ} (hm : 3 ≤ m) :
    cfOffsetPair m (8*K m+2) 4 := by
  have hk := cfKTwo m hm
  exact ⟨by omega,(cfEarlyBit eqs m hm (d := 4) (by omega)).1 (by omega),
    (cfEarlyBit eqs m hm (d := 8*K m+2-4) (by omega)).1 (by omega)⟩
