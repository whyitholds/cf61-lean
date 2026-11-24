import PartILiftBase

def piLiftJoin (k : ℕ) (x y : Fin 3) (q : PIQuad) : PIQuad :=
  ((q.1.1+k*piHU x,q.1.2+k*piHV x),(q.2.1+k*piHU y,q.2.2+k*piHV y))

def piLiftState (k j e : ℕ) (q : PIQuad) : ℕ :=
  piLiftPack ((q.1.1+q.2.1+j)/k) ((q.1.2+q.2.2+e)/k) (piCmp q.1.1 q.1.2) (piCmp q.2.1 q.2.2)

def piLiftSmall (k : ℕ) (q : PIQuad) : Prop :=
  (q.1.1 < k ∧ q.1.2 < k) ∧ (q.2.1 < k ∧ q.2.2 < k)

set_option maxRecDepth 4096 in
theorem piLiftForward {d k a v j e s sn l : ℕ} (hk : k=2^d) (hsn : sn<72) (hl : l<4)
    (x y : Fin 3) (q : PIQuad) (hm : (s,(x,y)) ∈ piMoveSet l sn)
    (hq : q ∈ piLiftBucket k a v j e s) :
    piLiftJoin k x y q ∈ piLiftBucket (2*k) (a+k*(l/2)) (v+k*(l%2)) j e sn := by
  rw [piLiftMove (s:=s) (sn:=sn) (l:=l) hsn hl x y] at hm
  obtain ⟨_,e1,e2,e3,e4⟩ := hm
  obtain ⟨⟨⟨hu,hv⟩,⟨hw,hz⟩⟩,hd,hf,hA,hB,hF,hG⟩ := (piLiftMem _ _ _ _ _ _ _).1 hq
  obtain ⟨hxU,hxV,_⟩ := piLiftDigits x
  obtain ⟨hyU,hyV,_⟩ := piLiftDigits y
  have xu : k*piHU x ≤ k := by simpa using Nat.mul_le_mul_left k hxU
  have xv : k*piHV x ≤ k := by simpa using Nat.mul_le_mul_left k hxV
  have yu : k*piHU y ≤ k := by simpa using Nat.mul_le_mul_left k hyU
  have yv : k*piHV y ≤ k := by simpa using Nat.mul_le_mul_left k hyV
  apply (piLiftMem _ _ _ _ _ _ _).2
  dsimp only [piLiftJoin,piLowPred]
  refine ⟨⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩,
    piLiftAndJoin _ _ _ _ hk hu hv hd x,piLiftAndJoin _ _ _ _ hk hw hz hf y,?_,?_,?_,?_⟩
  · nlinarith only [hA,congrArg (fun n : ℕ => k*n) e1]
  · nlinarith only [hB,congrArg (fun n : ℕ => k*n) e2]
  · rwa [piLiftCmpJoin k _ _ hu hv x,hF]
  · rwa [piLiftCmpJoin k _ _ hw hz y,hG]

theorem piLiftStateBack {k a v j e s : ℕ} (ha : a<k) (hv : v<k)
    (q : PIQuad) (hq : q ∈ piLiftBucket k a v j e s) : piLiftState k j e q=s := by
  obtain ⟨_,_,_,hA,hB,hF,hG⟩ := (piLiftMem _ _ _ _ _ _ _).1 hq
  have hp : 0 < k := by omega
  simp only [piLiftState,hA,hB,hF,hG,piLiftDiv _ _ _ hp ha,piLiftDiv _ _ _ hp hv,piLiftPackBack]

theorem piLiftDecode {d k a v j e sn l : ℕ} (hk : k=2^d) (ha : a<k) (hv : v<k)
    (hj : j<4) (he : e<2) (hsn : sn<72) (hl : l<4)
    (x y : Fin 3) (q : PIQuad) (small : piLiftSmall k q)
    (hq : piLiftJoin k x y q ∈ piLiftBucket (2*k) (a+k*(l/2)) (v+k*(l%2)) j e sn) :
    (piLiftState k j e q,(x,y)) ∈ piMoveSet l sn ∧ q ∈ piLiftBucket k a v j e (piLiftState k j e q) := by
  obtain ⟨⟨hu,hv'⟩,⟨hw,hz⟩⟩ := small
  obtain ⟨_,hD,hE,hA,hB,hF,hG⟩ := (piLiftMem _ _ _ _ _ _ _).1 hq
  dsimp only [piLiftJoin] at hD hE hA hB hF hG
  have hp : 0 < k := by omega
  have lowAnd (u v : ℕ) (hu : u<k) (hv : v<k) (x : Fin 3)
      (h : (u+k*piHU x) &&& (v+k*piHV x)=0) : u &&& v=0 := by
    have eq := ((piLiftBitAnd d _ _).1 h).1
    rw [← hk,piLiftMod _ _ _ hu,piLiftMod _ _ _ hv] at eq
    exact eq
  have colA := piLiftColumn k a q.1.1 q.2.1 j _ _ _ _ hp ha hA
  have colB := piLiftColumn k v q.1.2 q.2.2 e _ _ _ _ hp hv hB
  have hc : (q.1.1+q.2.1+j)/k < 4 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  have hb : (q.1.2+q.2.2+e)/k < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  obtain ⟨hS,cS,bS,fS,gS⟩ := piLiftPackRead hc hb (piLiftCmpBound q.1.1 q.1.2) (piLiftCmpBound q.2.1 q.2.2)
  rw [piLiftCmpJoin k _ _ hu hv' x] at hF
  rw [piLiftCmpJoin k _ _ hw hz y] at hG
  unfold piLiftState
  constructor
  · rw [piLiftMove hsn hl x y]
    simp only [cS,bS,fS,gS]
    exact ⟨hS,colA.2,colB.2,hF,hG⟩
  · apply (piLiftMem _ _ _ _ _ _ _).2
    simp only [piLowPred,cS,bS,fS,gS]
    exact ⟨⟨⟨hu,hv'⟩,⟨hw,hz⟩⟩,lowAnd _ _ hu hv' x hD,lowAnd _ _ hw hz y hE,colA.1,colB.1,by simp,by simp⟩
