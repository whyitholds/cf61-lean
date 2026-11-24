import PartIFastBook
import PartIFastTableV
import PartIFastTableE
import PartIFastTreePass

theorem pfCertByTree (i : Nat) (hi : i < 683) (h : pfCheckTree i = true) : pfPass i = true := by
  let e := pfEntry i
  change (decide (e.j0 < 683 ∧ e.j1 < 683 ∧ e.j2 < 683 ∧ e.j3 < 683) &&
    pfEval e.v (pfEntry e.j0).v (pfEntry e.j1).v (pfEntry e.j2).v (pfEntry e.j3).v) = true at h
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h0,h1,h2,h3⟩ := of_decide_eq_true hb
  unfold pfPass
  rw [pfLookupV i hi, pfLookupE i hi]
  change (pfGood e.v && ((decide (e.j0 < 683) && pfTr0 false e.v pfRows[e.j0]!) &&
    ((decide (e.j1 < 683) && pfTr1 false e.v pfRows[e.j1]!) &&
    ((decide (e.j2 < 683) && pfTr2 false e.v pfRows[e.j2]!) &&
    ((decide (e.j3 < 683) && pfTr3 false e.v pfRows[e.j3]!) && true))))) = true
  simp only [h0,h1,h2,h3,decide_true,Bool.true_and,pfLookupV e.j0 h0,pfLookupV e.j1 h1,
    pfLookupV e.j2 h2,pfLookupV e.j3 h3]
  exact hc
