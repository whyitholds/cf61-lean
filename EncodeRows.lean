import EncodeBase
open CF61

theorem cfPIMake {m p : ℕ} (a b : ℤ) (i : Fin 6)
    (hz : z b a = 1) (ha : a < 2*(K m:ℤ)) (hb : b < 2*(K m:ℤ))
    (ht : PITagOK a.toNat b.toNat i)
    (he : (p:ℤ) = 16*(K m:ℤ)*a+4*b+4*(K m:ℤ)*(PITagShift i:ℕ)+(PITagResidue i:ℕ)) :
    ∃ x, PIValid (K m) x ∧ PICellValue (K m) x = p := by
  obtain ⟨ha',hb',hd⟩ := cfPIZOne hz
  refine ⟨⟨a.toNat,b.toNat,i⟩, ⟨by change a.toNat < _; omega,by change b.toNat < _; omega, hd,ht⟩, ?_⟩
  apply Int.ofNat_inj.mp
  rw [cfPICellValueCast]
  simpa only [Int.toNat_of_nonneg ha', Int.toNat_of_nonneg hb'] using he.symm

theorem cfPIRowBounds {m p : ℕ} {l c r : ℤ} (hc : Coords m p l c r)
    (hp : 1 ≤ p) (hp' : p < n₀ m) : -1 ≤ l ∧ l < 2*(K m:ℤ) ∧
    (3*(K m:ℤ) ≤ c-2*(K m:ℤ) → l+1 < 2*(K m:ℤ)) := by
  let k : ℤ := K m
  change (p:ℤ) = 16*k*l+4*c+r ∧ 2*k ≤ c ∧ c ≤ 6*k-1 ∧ 1 ≤ r ∧ r ≤ 4 at hc
  have hk : 0 < k := by dsimp [k, K]; positivity
  have hh : (p:ℤ) < 32*k^2 := by
    dsimp only [k]
    unfold n₀ at hp'
    exact_mod_cast hp'
  change -1 ≤ l ∧ l < 2*k ∧ (3*k ≤ c-2*k → l+1 < 2*k)
  refine ⟨?_,?_,?_⟩
  · by_contra! h
    have q := mul_le_mul_of_nonneg_left (show l ≤ -2 by omega) (show 0 ≤ 16*k by omega)
    linarith [hc.1,hc.2.2.1,hc.2.2.2.2]
  · by_contra! h
    have q := mul_le_mul_of_nonneg_left h (show 0 ≤ 16*k by omega)
    nlinarith [hc.1,hc.2.1,hc.2.2.2.1]
  · intro hc'
    by_contra! h
    have q := mul_le_mul_of_nonneg_left (show 2*k-1 ≤ l by omega) (show 0 ≤ 16*k by omega)
    nlinarith [hc.1,hc.2.2.2.1]

theorem cfPISupport (h : CF61_Closed) (m : ℕ) (hm : 3 ≤ m) (p : ℕ)
    (hp : 1 ≤ p) (hp' : p < n₀ m) :
    y m p = 1 ↔ ∃ x, PIValid (K m) x ∧ PICellValue (K m) x = p := by
  constructor
  · intro hy
    obtain ⟨l,c,r,hc⟩ := (cfCoords m hm p hp).1
    obtain ⟨hl,hu,hbnd⟩ := cfPIRowBounds hc hp hp'
    let k : ℤ := K m
    let t := c-2*k
    have hk : 0 < k := by dsimp [k,K]; positivity
    have hc' : (p:ℤ) = 16*k*l+4*c+r ∧ 2*k ≤ c ∧ c ≤ 6*k-1 ∧ 1 ≤ r ∧ r ≤ 4 := hc
    have he : c = 2*k+t := by dsimp only [t]; ring
    have hrow := h.2 m hm p hp (by omega) _ _ _ hc
    rw [hy,he] at hrow
    have row := (cfClosedRowIff m l t r hl hu (by omega) (by omega)).1 hrow.symm
    have eqn : (p:ℤ) = 16*k*l + 4*(2*k+t)+r := by rw [← he]; exact hc'.1
    change 3*k ≤ t → l+1 < 2*k at hbnd
    change cfClosedRow k l t r at row
    rcases row with ⟨rfl,ht,ht',hz⟩ | ⟨(rfl|rfl),ht,ht',hz⟩ | ⟨rfl,ht,hz⟩ |
      ⟨rfl,ht,ht',hz⟩ | ⟨rfl,ht,ht',hz⟩ | ⟨rfl,ht,hl'⟩
    · apply cfPIMake (l) (t-k) 0 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · apply cfPIMake (l+1) (t-3*k) 4 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · apply cfPIMake (l+1) (t-3*k) 5 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · apply cfPIMake (l) (t) 1 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · apply cfPIMake (l) (t+1) 2 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · obtain ⟨hlz, htz, _⟩ := cfPIZOne hz
      apply cfPIMake (l) (t-2*k+1) 3 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> ring
    · have hz : z 0 0 = 1 := by decide
      apply cfPIMake (0) (0) 2 hz
      · change _ < 2*k; omega
      · change _ < 2*k; omega
      · norm_num [PITagOK] <;> omega
      · rw [eqn]
        change _ = 16*k*_ + 4*_ + 4*k*_ + _
        norm_num [PITagShift, PITagResidue] <;> rw [ht,hl']; ring
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨l,t,r,hc,hl,hu,ht,ht',hr,_⟩ := cfPIHit m x hx
    rw [h.2 m hm _ hp (by omega) _ _ _ hc]
    exact (cfClosedRowIff m l t r hl hu ht ht').2 hr

theorem cfPIInject (m : ℕ) (hm : 3 ≤ m) {x x' : PICell}
    (hx : PIValid (K m) x) (hx' : PIValid (K m) x')
    (hh : PICellValue (K m) x = PICellValue (K m) x') (hp : 1 ≤ PICellValue (K m) x) : x = x' := by
  obtain ⟨l,t,r,hc,_,_,_,_,_,he⟩ := cfPIHit m x hx
  obtain ⟨l',t',r',hc',_,_,_,_,_,he'⟩ := cfPIHit m x' hx'
  rw [← hh] at hc'
  obtain ⟨rfl,ht,rfl⟩ := (cfCoords m hm _ hp).2 _ _ _ _ _ _ hc hc'
  have : t = t' := by omega
  subst t'
  exact he.symm.trans he'
