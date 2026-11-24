import PartILiftCell

theorem piLiftTakePair {k d u v : ℕ} (hk : k=2^d) (hp : 0<k) (hu : u<2*k) (hv : v<2*k)
    (hd : u &&& v=0) :
    ∃ x : Fin 3, u%k+k*piHU x=u ∧ v%k+k*piHV x=v := by
  have h := ((piLiftBitAnd d u v).1 hd).2
  rw [← hk] at h
  have a := piLiftCodeBits (u/k) (v/k) ((Nat.div_lt_iff_lt_mul hp).2 hu)
    ((Nat.div_lt_iff_lt_mul hp).2 hv) h
  refine ⟨piLiftCode (u/k) (v/k),?_,?_⟩
  · rw [a.1]; exact Nat.mod_add_div _ _
  · rw [a.2]; exact Nat.mod_add_div _ _

theorem piLiftExtract {k d : ℕ} (hk : k=2^d) (Q : PIQuad) (sm : piLiftSmall (2*k) Q)
    (h₁ : Q.1.1 &&& Q.1.2=0) (h₂ : Q.2.1 &&& Q.2.2=0) :
    ∃ x y : Fin 3, ∃ q : PIQuad, piLiftSmall k q ∧ piLiftJoin k x y q=Q := by
  have hp : 0<k := by rw [hk]; positivity
  obtain ⟨x, xu,xv⟩ := piLiftTakePair hk hp sm.1.1 sm.1.2 h₁
  obtain ⟨y, yw,yz⟩ := piLiftTakePair hk hp sm.2.1 sm.2.2 h₂
  refine ⟨x,y,((Q.1.1%k,Q.1.2%k),(Q.2.1%k,Q.2.2%k)),?_,?_⟩
  · exact ⟨⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩,⟨Nat.mod_lt _ hp,Nat.mod_lt _ hp⟩⟩
  · simp only [piLiftJoin,xu,xv,yw,yz]

theorem piLiftJoinInj {k : ℕ} {x y x' y' : Fin 3} {q q' : PIQuad}
    (h : piLiftSmall k q) (h' : piLiftSmall k q') (E : piLiftJoin k x y q=piLiftJoin k x' y' q') :
    x=x' ∧ y=y' ∧ q=q' := by
  have a := piLiftBoth _ _ _ _ _ h.1.1 h'.1.1 (congrArg (fun p : PIQuad => p.1.1) E)
  have b := piLiftBoth _ _ _ _ _ h.1.2 h'.1.2 (congrArg (fun p : PIQuad => p.1.2) E)
  have c := piLiftBoth _ _ _ _ _ h.2.1 h'.2.1 (congrArg (fun p : PIQuad => p.2.1) E)
  have d := piLiftBoth _ _ _ _ _ h.2.2 h'.2.2 (congrArg (fun p : PIQuad => p.2.2) E)
  have tags (x x' : Fin 3) (a : piHU x=piHU x') (b : piHV x=piHV x') : x=x' := by
    calc x = piLiftCode (piHU x) (piHV x) := (piLiftCodeH x).symm
         _ = x' := by rw [a,b,piLiftCodeH]
  exact ⟨tags _ _ a.2 b.2,tags _ _ c.2 d.2,Prod.ext (Prod.ext a.1 b.1) (Prod.ext c.1 d.1)⟩

set_option maxRecDepth 8192 in
theorem piLiftCount (d k a v j e l sn : ℕ) (hk : k=2^d) (ha : a<k) (hv : v<k)
    (hj : j<4) (he : e<2) (hl : l<4) (hsn : sn<72) :
    piNumLow (2*k) (a+k*(l/2)) (v+k*(l%2)) j e sn =
      ∑ t ∈ piMoveSet l sn, piNumLow k a v j e t.1 := by
  let D : Finset PILiftEntry := (piMoveSet l sn).sigma (fun t => piLiftBucket k a v j e t.1)
  let H := piLiftBucket (2*k) (a+k*(l/2)) (v+k*(l%2)) j e sn
  have md (p : PILiftEntry) : p ∈ D ↔ p.1 ∈ piMoveSet l sn ∧ p.2 ∈ piLiftBucket k a v j e p.1.1 := by
    change p ∈ (piMoveSet l sn).sigma (fun z => piLiftBucket k a v j e z.1) ↔ _
    rw [Finset.mem_sigma]
  have E : D.card=H.card := by
    apply Finset.card_bij (fun p _ => piLiftJoin k p.1.2.1 p.1.2.2 p.2)
    · intro p m
      rw [md] at m
      obtain ⟨hm,hq⟩ := m
      exact piLiftForward (a:=a) (v:=v) (j:=j) (e:=e) (s:=p.1.1) hk hsn hl
        p.1.2.1 p.1.2.2 p.2 hm hq
    · rintro ⟨⟨s,x,y⟩,q⟩ m ⟨⟨s',x',y'⟩,q'⟩ m' eq
      rw [md] at m m'
      obtain ⟨_,hq⟩ := m
      obtain ⟨_,hq'⟩ := m'
      obtain ⟨ex,ey,eq'⟩ := piLiftJoinInj ((piLiftMem k a v j e s q).1 hq).1
        ((piLiftMem k a v j e s' q').1 hq').1 eq
      change x=x' at ex
      change y=y' at ey
      subst x'; subst y'; subst q'
      have leftState := piLiftStateBack (j:=j) (e:=e) (s:=s) ha hv q hq
      have rightState := piLiftStateBack (j:=j) (e:=e) (s:=s') ha hv q hq'
      have es : s=s' := leftState.symm.trans rightState
      exact congrArg (fun t : ℕ => (⟨(t,(x,y)),q⟩ : PILiftEntry)) es
    · intro Q m
      obtain ⟨sm,h₁,h₂,_⟩ := (piLiftMem (2*k) (a+k*(l/2)) (v+k*(l%2)) j e sn Q).1 m
      obtain ⟨x,y,q,hq,EQ⟩ := piLiftExtract hk Q sm h₁ h₂
      have down := piLiftDecode hk ha hv hj he hsn hl x y q hq (by simpa only [EQ] using m)
      refine ⟨⟨(piLiftState k j e q,(x,y)),q⟩,?_,EQ⟩
      rw [md]
      exact down
  change H.card = _
  rw [← E]
  exact Finset.card_sigma _ _
