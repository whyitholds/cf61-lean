import PartIFastCore
import PartIFastMap

def pfTreeBounds (e : PFTEntry) := e.j0 < 683 ∧ e.j1 < 683 ∧ e.j2 < 683 ∧ e.j3 < 683

def pfCheckTree (i : Nat) : Bool :=
  let e := pfEntry i
  decide (e.j0 < 683 ∧ e.j1 < 683 ∧ e.j2 < 683 ∧ e.j3 < 683) &&
    pfEval e.v (pfEntry e.j0).v (pfEntry e.j1).v (pfEntry e.j2).v (pfEntry e.j3).v

theorem pfTreeLift (i : Nat) (e : PFTEntry) (w0 w1 w2 w3 : Nat)
    (h : pfEntry i = e) (hb : pfTreeBounds e)
    (h0 : (pfEntry e.j0).v = w0) (h1 : (pfEntry e.j1).v = w1)
    (h2 : (pfEntry e.j2).v = w2) (h3 : (pfEntry e.j3).v = w3)
    (hc : pfEval e.v w0 w1 w2 w3 = true) : pfCheckTree i = true := by
  unfold pfCheckTree
  rw [h]
  unfold pfTreeBounds at hb
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true hb, ?_⟩
  change pfEval e.v (pfEntry e.j0).v (pfEntry e.j1).v (pfEntry e.j2).v (pfEntry e.j3).v = true
  rw [h0, h1, h2, h3]
  exact hc

def pfTRange (s n : Nat) := ∀ i : Nat, s ≤ i → i < s+n → pfCheckTree i = true

theorem pfTOne (s : Nat) (h : pfCheckTree s = true) : pfTRange s 1 := by
  intro i hlo hhi
  have : i = s := by omega
  simpa [this] using h

theorem pfTJoin (s n m : Nat) (h : pfTRange s n) (g : pfTRange (s+n) m) : pfTRange s (n+m) := by
  intro i hlo hhi
  by_cases hmid : i < s+n
  · exact h i hlo hmid
  · exact g i (by omega) (by omega)
