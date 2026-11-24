import PartITailCarries
import PartIPairOrder

set_option maxRecDepth 4096

abbrev PIChunk := Sigma fun _ : ℕ×ℕ => PIQuad × PITail

noncomputable def piChunks (k a V ah D r : ℕ) : Finset PIChunk := by
  classical
  exact (Finset.range 72 ×ˢ Finset.range 8).sigma fun w =>
    piLowBucket k a V (w.2/2) (w.2%2) (w.1/18) (w.1/9%2) (w.1/3%3) (w.1%3) ×ˢ
    piTailChoices ah D r (w.2/2) (w.2%2) (w.1/18) (w.1/9%2) (w.1/3%3) (w.1%3)

theorem piChunksCard (k a V ah D r : ℕ) :
    piTrueCount k a V ah D r=(piChunks k a V ah D r).card := by
  classical
  simp [piChunks,piTrueCount,Finset.card_sigma,Finset.sum_product]

theorem piChunkMem {k a V ah D r s t : ℕ} {q : PIQuad} {T : PITail} :
    (⟨(s,t),(q,T)⟩ : PIChunk) ∈ piChunks k a V ah D r ↔
    (s<72 ∧ t<8) ∧ (q ∈ piLowGrid k ∧ piLowPred k a V (t/2) (t%2) (s/18)
      (s/9%2) (s/3%3) (s%3) q) ∧ piTailPred ah D r (t/2) (t%2) (s/18)
      (s/9%2) (s/3%3) (s%3) T := by
  classical
  simp [piChunks,piLowBucket,piTailChoices]

def piChunkValues (k : ℕ) (x : PIChunk) : PICell × PICell :=
  let q := x.2.1
  let T := x.2.2
  (piJoinCell k q.1 T.1.1 T.2.1,piJoinCell k q.2 T.1.2 T.2.2)

theorem piChunkValuesMem {k a V ah D r d : ℕ} (hp : k=2^d) {x : PIChunk}
    (hx : x ∈ piChunks k a V ah D r) :
    piChunkValues k x ∈ piCellPairs k (16*k*(k*ah+a)+4*k*D+4*V+r) := by
  rcases x with ⟨⟨s,t⟩,⟨q,T⟩⟩
  obtain ⟨_,⟨grid,low⟩,tail⟩ := (@piChunkMem k a V ah D r s t q T).1 hx
  simp only [piLowGrid,Finset.mem_product,Finset.mem_range] at grid
  rcases low with ⟨b1,b2,hu,hv,f,g⟩
  rcases tail with ⟨ft,gt,fc,bc,rr⟩
  apply piMemCellPairs.2
  refine ⟨(piJoinValid hp _ _ grid.1.1 grid.1.2).2 ⟨b1,?_⟩,
          (piJoinValid hp _ _ grid.2.1 grid.2.2).2 ⟨b2,?_⟩,
          piSumFromCarries hu hv fc bc rr⟩
  · simpa [f] using ft
  · simpa [g] using gt

theorem piChunkValuesInj {k a V ah D r : ℕ} (hk : 0<k) {x y : PIChunk}
    (hx : x ∈ piChunks k a V ah D r) (hy : y ∈ piChunks k a V ah D r)
    (he : piChunkValues k x=piChunkValues k y) : x=y := by
  rcases x with ⟨⟨s,t⟩,⟨⟨p,q⟩,⟨⟨i,j⟩,⟨u,v⟩⟩⟩⟩
  rcases y with ⟨⟨s',t'⟩,⟨⟨p',q'⟩,⟨⟨i',j'⟩,⟨u',v'⟩⟩⟩⟩
  obtain ⟨bxy,⟨grid,low⟩,tail⟩ := (@piChunkMem k a V ah D r s t (p,q) ((i,j),(u,v))).1 hx
  obtain ⟨bxy',⟨grid',low'⟩,tail'⟩ := (@piChunkMem k a V ah D r s' t' (p',q') ((i',j'),(u',v'))).1 hy
  simp only [piLowGrid,Finset.mem_product,Finset.mem_range] at grid grid'
  obtain ⟨rfl,rfl,rfl⟩ := piJoinUnique grid.1 grid'.1 (congrArg Prod.fst he)
  obtain ⟨rfl,rfl,rfl⟩ := piJoinUnique grid.2 grid'.2 (congrArg Prod.snd he)
  obtain ⟨rfl,rfl⟩ := piKeysUnique hk bxy.1 bxy'.1 low low' tail tail'
  rfl

theorem piChunkValuesOnto {k a V ah D r d : ℕ} (hp : k=2^d) (hk : 2 ≤ k)
    (ha : a<k) (hV : V<k) (hD : D<4) (hr : r<4) {p : PICell×PICell}
    (h : p ∈ piCellPairs k (16*k*(k*ah+a)+4*k*D+4*V+r)) :
    ∃ x ∈ piChunks k a V ah D r, piChunkValues k x=p := by
  rcases p with ⟨x,y⟩
  obtain ⟨vx,vy,hsum⟩ := piMemCellPairs.1 h
  obtain ⟨p,i,hp1,hp2,hx⟩ := piJoinExists hp vx
  obtain ⟨q,j,hq1,hq2,hy⟩ := piJoinExists hp vy
  let Q : PIQuad := (p,q)
  let T : PITail := ((i,j),(x.kind,y.kind))
  have grid : Q ∈ piLowGrid k := by simp [Q,piLowGrid,hp1,hp2,hq1,hq2]
  have grade : PICellValue k (piJoinCell k Q.1 T.1.1 T.2.1)+PICellValue k (piJoinCell k Q.2 T.1.2 T.2.2)
      =16*k*(k*ah+a)+4*k*D+4*V+r := by simpa [Q,T,hx,hy] using hsum
  obtain ⟨J,E,C,B,hJ,hE,hC,hB,hu,hv,hc,hb,hres⟩ := piDecCarries hk ha hV hD hr grid grade
  obtain ⟨b1,t1⟩ := (piJoinValid hp i x.kind hp1 hp2).1 (by simpa [hx] using vx)
  obtain ⟨b2,t2⟩ := (piJoinValid hp j y.kind hq1 hq2).1 (by simpa [hy] using vy)
  let F := piCmp p.1 p.2
  let G := piCmp q.1 q.2
  have hF : F<3 := piCmpBound _ _
  have hG : G<3 := piCmpBound _ _
  let s := 18*C+9*B+3*F+G
  let t := 2*J+E
  have sC : s/18=C := by dsimp [s]; omega
  have sB : s/9%2=B := by dsimp [s]; omega
  have sF : s/3%3=F := by dsimp [s]; omega
  have sG : s%3=G := by dsimp [s]; omega
  have tJ : t/2=J := by dsimp [t]; omega
  have tE : t%2=E := by dsimp [t]; omega
  refine ⟨⟨(s,t),(Q,T)⟩,(@piChunkMem k a V ah D r s t Q T).2 ?_,?_⟩
  · simp only [sC,sB,sF,sG,tJ,tE]
    exact ⟨⟨by dsimp [s]; omega,by dsimp [t]; omega⟩,
      ⟨grid,b1,b2,hu,hv,rfl,rfl⟩,t1,t2,hc,hb,hres⟩
  · exact Prod.ext hx hy

theorem piTrueCountEqPairs {k d a V ah D r : ℕ} (hp : k=2^d) (hk : 2 ≤ k)
    (ha : a<k) (hV : V<k) (hD : D<4) (hr : r<4) :
    piTrueCount k a V ah D r=(piCellPairs k (16*k*(k*ah+a)+4*k*D+4*V+r)).card := by
  classical
  rw [piChunksCard]
  exact Finset.card_bij (fun x _ => piChunkValues k x)
    (fun x hx => @piChunkValuesMem k a V ah D r d hp x hx)
    (fun x hx y hy e => @piChunkValuesInj k a V ah D r (by omega) x y hx hy e)
    (fun p h => by
      obtain ⟨x,hx,e⟩ := @piChunkValuesOnto k a V ah D r d hp hk ha hV hD hr p h
      exact ⟨x,hx,e⟩)
