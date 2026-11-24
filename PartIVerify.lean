import PartIInd
import PartIClamp
import PartIPred

set_option maxRecDepth 10000

theorem piLaneOfStep {v w a : ℕ} (first : Bool) (ha : a < 4) (hb : piBounded v)
    (h : piTransition first v a w = true) :
    piMovesAgree v a w ∧ piCol w 72 = piFlagA first a (piCol v 72) ∧
    piCol w 73 = piFlagV a (piCol v 73) := by
  simp only [piTransition, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hStep,hFlagA⟩,hFlagV⟩ := h
  refine ⟨?_,hFlagA.symm,hFlagV.symm⟩
  intro s t hs ht
  rw [← hStep s hs, piStepDigit v ha hs ht (fun i hi j hj => hb i j hi hj)]
  congr 1
  exact piPredSum (fun i => piDigit (piCol v i) t) ha hs

theorem piFirstOfPass (h : piFirstPass = true) : piVerifiedFirst := by
  intro l hl
  have h1 := List.all_eq_true.mp h l (List.mem_range.mpr hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨_,h1.1,piLaneOfStep true hl (piRelBounded piStartRel) h1.2⟩

theorem piStepOfPass (h : ∀ i : ℕ, i < 683 → piStatePass i = true) : piVerifiedStep := by
  intro i l hi hl hb
  have h1 := h i hi
  simp only [piStatePass, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h1
  obtain ⟨hj,htr⟩ := h1.2 l hl
  exact ⟨_,hj,piLaneOfStep false hl hb htr⟩

theorem piGoodOfPass (h : ∀ i : ℕ, i < 683 → piStatePass i = true) (i : ℕ) (hi : i < 683) :
    piGood piRowList[i]! = true := by
  have hh := h i hi
  simp only [piStatePass, Bool.and_eq_true] at hh
  exact hh.1
