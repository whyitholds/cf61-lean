import PartIPredPure
import PartIMoves
import PartIPacked

theorem piPredSum (F : ℕ → ℕ) {a s : ℕ} (ha : a < 4) (hs : s < 72) :
    (((piIncoming[a]!)[s]!).map F).sum = ∑ t ∈ piMoveSet a s, F t.1 := by
  have h := ppOK ⟨a,ha⟩ ⟨s,hs⟩
  change ppChecks a s = true at h
  simp only [ppChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hl,hn⟩,hv⟩ := h
  change (ppTagged a s).map Prod.fst = (piIncoming[a]!)[s]! at hl
  have e : piMoveSet a s = (ppTagged a s).toFinset := by
    ext t
    obtain ⟨i,x,y⟩ := t
    simp only [piMoveSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, List.mem_toFinset]
    constructor
    · rintro ⟨hi,hh,hh'⟩
      have hh0 := ppCover ⟨i,hi⟩ x y
      change (i,x,y) ∈ ppTagged (piNextLetter i x y) (piNextCol i x y) at hh0
      simpa only [hh,hh'] using hh0
    · exact fun ht => hv (i,x,y) ht
  rw [← hl, e, Finset.sum, List.toFinset_val, List.dedup_eq_self.mpr hn]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map, Function.comp_def]
