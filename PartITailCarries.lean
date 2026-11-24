import PartITailCore

theorem piShiftBound (t : Fin 6) : PITagShift t ≤ 4 := by fin_cases t <;> decide

theorem piResBound (t : Fin 6) : PITagResidue t ≤ 3 := by fin_cases t <;> decide

theorem piHiVBound (t : Fin 3) : piHV t ≤ 1 := by fin_cases t <;> decide

theorem piCmpBound (a b : ℕ) : piCmp a b<3 := by unfold piCmp; split <;> (try split) <;> decide

theorem piDecCarries {k a V ah D r : ℕ} {q : PIQuad} {T : PITail}
    (hk : 2 ≤ k) (ha : a<k) (hV : V<k) (hD : D<4) (hr : r<4)
    (hgrid : q ∈ piLowGrid k)
    (hsum : PICellValue k (piJoinCell k q.1 T.1.1 T.2.1)+PICellValue k (piJoinCell k q.2 T.1.2 T.2.2)
      =16*k*(k*ah+a)+4*k*D+4*V+r) :
    ∃ j e c b : ℕ, j<4 ∧ e<2 ∧ c<4 ∧ b<2 ∧
      (q.1.1+q.2.1+j=a+k*c) ∧ (q.1.2+q.2.2+e=V+k*b) ∧
      (c+piHU T.1.1+piHU T.1.2=ah) ∧
      (b+piHV T.1.1+piHV T.1.2+PITagShift T.2.1+PITagShift T.2.2=D+4*j) ∧
      (PITagResidue T.2.1+PITagResidue T.2.2=r+4*e) := by
  simp only [piLowGrid,Finset.mem_product, Finset.mem_range] at hgrid
  let R := PITagResidue T.2.1+PITagResidue T.2.2
  let e := R/4
  let Z := q.1.2 + q.2.2 + e
  let b := Z/k
  let W := b+piHV T.1.1+piHV T.1.2+PITagShift T.2.1+PITagShift T.2.2
  let j := W/4
  let U := q.1.1+q.2.1+j
  let c := U/k
  have pos : 0<k := by omega
  have eB : e<2 := by
    dsimp [e,R]; have := piResBound T.2.1; have := piResBound T.2.2; omega
  have bB : b<2 := (Nat.div_lt_iff_lt_mul pos).2 (by dsimp [Z]; omega)
  have jB : j<4 := by
    dsimp [j,W]; have := piHiVBound T.1.1; have := piHiVBound T.1.2
    have := piShiftBound T.2.1; have := piShiftBound T.2.2; omega
  have cB : c<4 := (Nat.div_lt_iff_lt_mul pos).2 (by dsimp [U]; omega)
  have h1 : q.1.1+q.2.1+j=U%k+k*c := (Nat.mod_add_div U k).symm
  have h2 : q.1.2+q.2.2+e=Z%k+k*b := (Nat.mod_add_div Z k).symm
  have h3 : b+piHV T.1.1+piHV T.1.2+PITagShift T.2.1+PITagShift T.2.2 =
    W%4+4*j := (Nat.mod_add_div W 4).symm
  have h4 : PITagResidue T.2.1+PITagResidue T.2.2=R%4+4*e := (Nat.mod_add_div R 4).symm
  have hcalc := piSumFromCarries (q:=q) (T:=T) h1 h2 rfl h3 h4
  have un := piNormalUnique pos (Nat.mod_lt U pos) (Nat.mod_lt Z pos)
    (Nat.mod_lt W (by decide : 0<4)) (Nat.mod_lt R (by decide : 0<4)) ha hV hD hr
    (hcalc.symm.trans hsum)
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := un
  exact ⟨j,e,c,b,jB,eB,cB,bB,h1,h2,rfl,h3,h4⟩

theorem piKeysUnique {k a V ah D r s t s' t' : ℕ} {q : PIQuad} {T : PITail}
    (hk : 0<k) (hs : s<72) (hs' : s'<72)
    (l : piLowPred k a V (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3) q)
    (l' : piLowPred k a V (t'/2) (t'%2) (s'/18) (s'/9%2) (s'/3%3) (s'%3) q)
    (h : piTailPred ah D r (t/2) (t%2) (s/18) (s/9%2) (s/3%3) (s%3) T)
    (h' : piTailPred ah D r (t'/2) (t'%2) (s'/18) (s'/9%2) (s'/3%3) (s'%3) T) :
    s=s' ∧ t=t' := by
  rcases l with ⟨_,_,hu,hv,hf,hg⟩
  rcases l' with ⟨_,_,hu',hv',hf',hg'⟩
  rcases h with ⟨_,_,hc,hb,hr⟩
  rcases h' with ⟨_,_,hc',hb',hr'⟩
  have e : t%2=t'%2 := by omega
  have be : s/9%2=s'/9%2 := Nat.eq_of_mul_eq_mul_left hk (by omega)
  omega
