import ClosedForm
import ClosedBase
import NumBits
open CF61

theorem clZEq (h l : ℤ) : z h l = 1 ↔
    0 ≤ h ∧ 0 ≤ l ∧ h.toNat &&& l.toNat = 0 := by
  by_cases hh : 0 ≤ h <;> by_cases hl : 0 ≤ l
  · have eq := cfZBit h.toNat l.toNat
    rw [Int.toNat_of_nonneg hh, Int.toNat_of_nonneg hl] at eq
    rw [eq]
    simp [hh,hl]
  all_goals simp [z,hh,hl]

theorem clValK (k l t) : autoVal clK k l t = k := by simp [autoVal,clK]
theorem clValL (k l t) : autoVal clL k l t = l := by simp [autoVal,clL]
theorem clValT (k l t) : autoVal clT k l t = t := by simp [autoVal,clT]
theorem clValC (k l t) : autoVal clC k l t = 1 := by simp [autoVal,clC]
theorem clValO (k l t) : autoVal clO k l t = 0 := by simp [autoVal,clO]

theorem clValAdd (x y) (k l t) : autoVal (clAdd x y) k l t = autoVal x k l t + autoVal y k l t := by
  simp only [autoVal,clAdd]; ring
theorem clValSub (x y) (k l t) : autoVal (clSub x y) k l t = autoVal x k l t - autoVal y k l t := by
  simp only [autoVal,clSub]; ring
theorem clValMul (n x) (k l t) : autoVal (clMul n x) k l t = n * autoVal x k l t := by
  simp only [autoVal,clMul]; ring

theorem clDenCon (f g k l t) : autoDen (.con f g) k l t ↔ autoDen f k l t ∧ autoDen g k l t := Iff.rfl
theorem clDenOr (f g k l t) : autoDen (.disj f g) k l t ↔ autoDen f k l t ∨ autoDen g k l t := Iff.rfl
theorem clDenPow (k l t) : autoDen .pow k l t ↔ ∃ e : ℕ, k=2^e := Iff.rfl
theorem clDenLe (x y k l t) : autoDen (clLe x y) k l t ↔ autoVal x k l t ≤ autoVal y k l t := by
  change 0 ≤ autoVal (clSub y x) k l t ↔ _
  rw [clValSub]; omega
theorem clDenLt (x y k l t) : autoDen (clLt x y) k l t ↔ autoVal x k l t < autoVal y k l t := by
  change 0 ≤ autoVal (clSub (clSub y x) clC) k l t ↔ _
  rw [clValSub,clValSub,clValC]; omega
theorem clDenEq (x y k l t) : autoDen (clEq x y) k l t ↔ autoVal x k l t = autoVal y k l t := by
  simp only [clEq,clDenCon,clDenLe]; omega
theorem clDenDis (x y k l t) : autoDen (.dis x y) k l t ↔ z (autoVal x k l t) (autoVal y k l t) = 1 :=
  (clZEq _ _).symm

theorem clRowOk (r lell atail k L t) (hr : 1≤r) (hr' : r≤4) :
    autoDen (clRow r lell atail) k L t ↔
    cfClosedRow k (autoVal lell k L t) (autoVal atail k L t) r := by
  interval_cases r <;>
    norm_num [clRow,cfClosedRow,clDenCon,clDenOr,clDenLe,clDenEq,clDenLt,clDenDis,
      clValAdd,clValSub,clValMul,clValC,clValO,clValK]

theorem clPrevOk (r lell atail d k L t) (hr : 1≤r) (hr' : r≤4) :
    autoDen (clPrev r lell atail d) k L t ↔
    cfClosedPrev k (autoVal lell k L t) (autoVal atail k L t) (autoVal d k L t) r := by
  simp only [clPrev,clDenOr,clDenCon,clDenLt,clDenLe,clRowOk _ _ _ _ _ _ hr hr',
    clValAdd,clValSub,clValMul,clValC,clValK,cfClosedPrev]
  split <;> rename_i h
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

theorem clOneOk (a b c k L t) : autoDen (clOne a b c) k L t ↔
    cfClosedOne (autoDen a k L t) (autoDen b k L t) (autoDen c k L t) := Iff.rfl

theorem clCut (dom x y : AutoF) (k L t : ℕ) (d : autoDen dom k L t)
    (h : autoDen (.disj (.neg dom) (.con (.disj (.neg x) y) (.disj (.neg y) x))) k L t) :
    autoDen x k L t ↔ autoDen y k L t := by
  change ¬autoDen dom k L t ∨
    (¬autoDen x k L t ∨ autoDen y k L t) ∧ (¬autoDen y k L t ∨ autoDen x k L t) at h
  have p := h.resolve_left (fun hn => hn d)
  exact ⟨fun hx => p.1.resolve_left (fun hnx => hnx hx),fun hy => p.2.resolve_left (fun hny => hny hy)⟩

theorem clGoalToRow (r k L t : ℕ) (hr : 1 ≤ r) (hu : r ≤ 4)
    (hp : ∃ e : ℕ, k=2^e) (hd1 : 1 ≤ (L:ℤ)) (hd2 : (L:ℤ) ≤ 2*k) (hd3 : (t:ℤ) < 4*k)
    (pf : autoDen (clGoal r) k L t) :
    cfClosedRow k ((L:ℤ)-1) t r ↔ cfClosedOne
      (cfClosedPrev k ((L:ℤ)-1) t (if r ≤ 2 then 1 else 0) (if r ≤ 2 then (r:ℤ)+2 else (r:ℤ)-2))
      (cfClosedPrev k ((L:ℤ)-1) t (if r = 1 then (k:ℤ)+1 else k) (if r = 1 then 4 else (r:ℤ)-1))
      (cfClosedPrev k ((L:ℤ)-1) t (2*(k:ℤ)) r) := by
  let dom := AutoF.con .pow (.con (clLe clC clL) (.con (clLe clL (clMul 2 clK)) (clLt clT (clMul 4 clK))))
  have hd : autoDen dom k L t := by
    simp only [dom,clDenCon,clDenPow,clDenLe,clDenLt,clValL,clValC,clValK,clValT,clValMul]
    exact ⟨hp,hd1,hd2,hd3⟩
  let el := clSub clL clC
  let r1 := if r ≤ 2 then r+2 else r-2
  let r2 := if r = 1 then 4 else r-1
  let d1 := if r ≤ 2 then clC else clO
  let d2 := if r = 1 then clAdd clK clC else clK
  have x := clCut dom (clRow r el clT)
    (clOne (clPrev r1 el clT d1) (clPrev r2 el clT d2) (clPrev r el clT (clMul 2 clK))) k L t hd pf
  have hr1 : 1 ≤ r1 := by dsimp [r1]; split <;> omega
  have hu1 : r1 ≤ 4 := by dsimp [r1]; split <;> omega
  have hr2 : 1 ≤ r2 := by dsimp [r2]; split <;> omega
  have hu2 : r2 ≤ 4 := by dsimp [r2]; split <;> omega
  rw [clRowOk _ _ _ _ _ _ hr hu,clOneOk,clPrevOk _ _ _ _ _ _ _ hr1 hu1,
    clPrevOk _ _ _ _ _ _ _ hr2 hu2,clPrevOk _ _ _ _ _ _ _ hr hu] at x
  simp only [el,clValSub,clValL,clValC,clValT,clValMul,clValK] at x
  have er1 : (r1:ℤ) = if r≤2 then (r:ℤ)+2 else (r:ℤ)-2 := by dsimp [r1]; split <;> omega
  have er2 : (r2:ℤ) = if r=1 then 4 else (r:ℤ)-1 := by dsimp [r2]; split <;> omega
  have ed1 : autoVal d1 k L t = if r≤2 then 1 else 0 := by dsimp [d1]; split <;> simp [clValC,clValO]
  have ed2 : autoVal d2 k L t = if r=1 then (k:ℤ)+1 else k := by dsimp [d2]; split <;> simp [clValAdd,clValK,clValC]
  simpa only [er1,er2,ed1,ed2] using x

theorem clGoalsLocal (cert : ∀ r k L t : ℕ, 1 ≤ r → r ≤ 4 → autoDen (clGoal r) k L t)
    (m : ℕ) : cfClosedLocal m := by
  intro l t r hl hu ht ht' hr hr'
  let L := (l+1).toNat
  let T := t.toNat
  let R := r.toNat
  have eL : (L:ℤ)=l+1 := Int.toNat_of_nonneg (by omega)
  have eT : (T:ℤ)=t := Int.toNat_of_nonneg ht
  have eR : (R:ℤ)=r := Int.toNat_of_nonneg (by omega)
  have eLL : (L:ℤ)-1=l := by omega
  have hR : 1 ≤ R := by omega
  have hR' : R ≤ 4 := by omega
  have e1 : R ≤ 2 ↔ r ≤ 2 := by omega
  have e2 : R = 1 ↔ r = 1 := by omega
  have hz := clGoalToRow R (K m) L T hR hR' ⟨m-2,rfl⟩ (by omega) (by omega) (by omega)
    (cert R _ _ _ hR hR')
  simpa only [eLL,eT,eR,e1,e2] using hz
