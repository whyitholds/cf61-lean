import PartIAuto
import WeightAlgebra
import WeightBridge
import WeightBounds
import WAltMath

theorem waAcceptOfChecks (cols : ∀ s, s<72 → waPass s=true) (v ah d r : ℕ)
    (ha : ah<2) (hd : d<4) (hr : r<4) :
    piAcceptCount v ah d r =
    ∑ s ∈ Finset.range 72, ∑ t ∈ Finset.range 8,
      piDigit (piCol v s) t * (piTailChoices ah d r (t/2) (t%2)
        (s/18) (s/9%2) (s/3%3) (s%3)).card := by
  let q := 16*ah+4*d+r
  have hq : q < 32 := by dsimp [q]; omega
  change (piWeights[q]!).foldl _ _ = _
  rw [piWSparse 72 8 _ (fun s t => piDigit (piCol v s) t)]
  · apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    have hs' := Finset.mem_range.mp hs
    apply congrArg (fun z => piDigit (piCol v s) t * z)
    change pwWeight q s t = _
    have h := waWeightOfPass (t := t) hq (cols s hs')
    unfold pwCheck at h
    rw [beq_iff_eq] at h
    rw [h, ← pwCard]
    have a : q/16=ah := by dsimp [q]; omega
    have b : q/4%4=d := by dsimp [q]; omega
    have c : q%4=r := by dsimp [q]; omega
    rw [a,b,c]
  · intro p hp
    have h := pwBoundCheck ⟨q,hq⟩
    rw [pwTableEq] at hp
    exact of_decide_eq_true (List.all_eq_true.mp h p hp)
