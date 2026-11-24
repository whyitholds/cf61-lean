import PartILowSpec

def piJoinCell (k : ℕ) (p : ℕ × ℕ) (h : Fin 3) (t : Fin 6) : PICell :=
  ⟨p.1+k*piHU h,p.2+k*piHV h,t⟩

theorem piRadixUnique {k a b x y : ℕ} (hk : 0<k) (ha : a<k) (hb : b<k)
    (h : a+k*x=b+k*y) : a=b ∧ x=y := by
  have hlow := congrArg (· % k) h
  simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hlow
  exact ⟨hlow,Nat.eq_of_mul_eq_mul_left hk (by omega)⟩

theorem piJoinMod {k p h : ℕ} (hp : p<k) : (p+k*h)%k=p := by
  simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hp]

theorem piJoinDiv {k p h : ℕ} (hp : p<k) : (p+k*h)/k=h := by
  simpa [Nat.div_eq_of_lt hp] using Nat.add_mul_div_left p h (show 0<k by omega)

theorem piJoinCmp {k : ℕ} {p : ℕ × ℕ} (h : Fin 3) (hu : p.1<k) (hv : p.2<k) :
    piCmp (p.1+k*piHU h) (p.2+k*piHV h) = piCmpUp (piCmp p.1 p.2) (piHU h) (piHV h) := by
  fin_cases h <;> norm_num [piHU,piHV,piCmpUp,piCmp] <;> split_ifs <;> omega

theorem piJoinBit {k d : ℕ} (hp : k=2^d) {p : ℕ × ℕ} (h : Fin 3)
    (hu : p.1<k) (hv : p.2<k) :
    (p.1+k*piHU h) &&& (p.2+k*piHV h)=0 ↔ p.1 &&& p.2=0 := by
  let w := (p.1+k*piHU h) &&& (p.2+k*piHV h)
  have lo : w%k = p.1 &&& p.2 := by
    dsimp [w]; rw [show ∀ a b : ℕ, (a &&& b)%k = a%k &&& (b%k) by
      intro a b; rw [hp]; exact Nat.and_mod_two_pow, piJoinMod hu, piJoinMod hv]
  have hi : w/k=0 := by
    dsimp [w]; rw [show ∀ a b : ℕ, (a &&& b)/k = a/k &&& (b/k) by
      intro a b; rw [hp]; exact Nat.and_div_two_pow,piJoinDiv hu,piJoinDiv hv]
    fin_cases h <;> decide
  change w=0 ↔ _
  have hval := Nat.mod_add_div w k
  rw [hi, Nat.mul_zero,Nat.add_zero] at hval
  rw [←lo,hval]

theorem piJoinValid {k d : ℕ} (hp : k=2^d) {p : ℕ × ℕ} (h : Fin 3)
    (t : Fin 6) (hu : p.1<k) (hv : p.2<k) :
    PIValid k (piJoinCell k p h t) ↔
      p.1 &&& p.2=0 ∧ piFits (piCmpUp (piCmp p.1 p.2) (piHU h) (piHV h)) t := by
  have hu1 : p.1+k*piHU h<2*k := by fin_cases h <;> simp [piHU] <;> omega
  have hv1 : p.2+k*piHV h<2*k := by fin_cases h <;> simp [piHV] <;> omega
  simp only [PIValid,piJoinCell,hu1,hv1,true_and,piJoinBit hp h hu hv,
    ← piFitsCmp,piJoinCmp h hu hv]

theorem piJoinUnique {k : ℕ} {p q : ℕ × ℕ} {i j : Fin 3} {u v : Fin 6}
    (hp : p.1<k ∧ p.2<k) (hq : q.1<k ∧ q.2<k)
    (he : piJoinCell k p i u=piJoinCell k q j v) : p=q ∧ i=j ∧ u=v := by
  have e1 := congrArg PICell.u he
  have e2 := congrArg PICell.v he
  have e3 := congrArg PICell.kind he
  obtain ⟨l1,h1⟩ := piRadixUnique (by omega : 0<k) hp.1 hq.1 (by exact e1)
  obtain ⟨l2,h2⟩ := piRadixUnique (by omega : 0<k) hp.2 hq.2 (by exact e2)
  refine ⟨Prod.ext l1 l2,?_,e3⟩
  fin_cases i <;> fin_cases j <;> simp_all [piHU,piHV]

theorem piJoinExists {k d : ℕ} (hp : k=2^d) {x : PICell} (hx : PIValid k x) :
    ∃ p : ℕ×ℕ, ∃ i : Fin 3, p.1<k ∧ p.2<k ∧ piJoinCell k p i x.kind=x := by
  have hk : 0<k := by rw [hp]; positivity
  rcases x with ⟨u,v,t⟩
  obtain ⟨hu,hv,hbit,htag⟩ := hx
  change u<2*k at hu
  change v<2*k at hv
  change u &&& v=0 at hbit
  let p : ℕ×ℕ := (u%k,v%k)
  have pl : p.1<k := Nat.mod_lt u hk
  have pr : p.2<k := Nat.mod_lt v hk
  have a : u/k<2 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
  have b : v/k<2 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
  have hvv : (u/k) &&& (v/k)=0 := by
    rw [hp] at *
    rw [←Nat.and_div_two_pow,hbit,Nat.zero_div]
  have rep (i : Fin 3) (h1 : u/k=piHU i) (h2 : v/k=piHV i) :
      piJoinCell k p i t=⟨u,v,t⟩ := by
    unfold piJoinCell
    simp only [p,←h1,←h2,Nat.mod_add_div]
  have decode (A B : ℕ) (hA : A<2) (hB : B<2) (hD : A &&& B=0) :
      ∃ i : Fin 3, A=piHU i ∧ B=piHV i := by
    interval_cases A <;> interval_cases B <;> first
      | exact ⟨0,rfl,rfl⟩ | exact ⟨1,rfl,rfl⟩ | exact ⟨2,rfl,rfl⟩ | contradiction
  obtain ⟨i,h1,h2⟩ := decode _ _ a b hvv
  exact ⟨p,i,pl,pr,rep i h1 h2⟩

theorem piSumFromCarries {k a V ah D r j e c b : ℕ} {q : PIQuad} {T : PITail}
    (hu : q.1.1+q.2.1+j=a+k*c) (hv : q.1.2+q.2.2+e=V+k*b)
    (hc : c+piHU T.1.1+piHU T.1.2=ah)
    (hb : b+piHV T.1.1+piHV T.1.2+PITagShift T.2.1+PITagShift T.2.2=D+4*j)
    (hr : PITagResidue T.2.1+PITagResidue T.2.2=r+4*e) :
    PICellValue k (piJoinCell k q.1 T.1.1 T.2.1) + PICellValue k (piJoinCell k q.2 T.1.2 T.2.2)
    =16*k*(k*ah+a)+4*k*D+4*V+r := by
  unfold PICellValue piJoinCell
  dsimp only
  zify at hu hv hc hb hr ⊢
  linear_combination hr+4*hv+4*(k:ℤ)*hb+16*(k:ℤ)*hu+16*(k:ℤ)^2*hc

theorem piNormalUnique {k a V ah D r a' V' ah' D' r' : ℕ} (hk : 0<k)
    (ha : a<k) (hV : V<k) (hD : D<4) (hr : r<4)
    (ha' : a'<k) (hV' : V'<k) (hD' : D'<4) (hr' : r'<4)
    (h : 16*k*(k*ah+a)+4*k*D+4*V+r=16*k*(k*ah'+a')+4*k*D'+4*V'+r') :
    r=r' ∧ V=V' ∧ D=D' ∧ a=a' ∧ ah=ah' := by
  have nrm (a V ah D r : ℕ) : 16*k*(k*ah+a)+4*k*D+4*V+r =
      r+4*(V+k*(D+4*(a+k*ah))) := by ring
  rw [nrm,nrm] at h
  obtain ⟨e1,h1⟩ := piRadixUnique (by decide) hr hr' h
  obtain ⟨e2,h2⟩ := piRadixUnique hk hV hV' h1
  obtain ⟨e3,h3⟩ := piRadixUnique (by decide) hD hD' h2
  obtain ⟨e4,e5⟩ := piRadixUnique hk ha ha' h3
  exact ⟨e1,e2,e3,e4,e5⟩
