import PartIAuto
import PartIFastBook
import PartIFastWire0
import PartIFastWire1
import PartIFastWire2
import PartIFastWire3
import PartIFastWireGood
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTransitionSame (b : Bool) (v a w : Nat) :
    piTransition b v a w = pfWTransition b v a w := rfl

theorem pfGoodSame (v : Nat) : piGood v = pfWGood v := rfl

theorem pfTrEq0 (b : Bool) (v w : Nat) : piTransition b v 0 w = pfTr0 b v w :=
  (pfTransitionSame b v 0 w).trans (pfWireTr0 b v w)

theorem pfTrEq1 (b : Bool) (v w : Nat) : piTransition b v 1 w = pfTr1 b v w :=
  (pfTransitionSame b v 1 w).trans (pfWireTr1 b v w)

theorem pfTrEq2 (b : Bool) (v w : Nat) : piTransition b v 2 w = pfTr2 b v w :=
  (pfTransitionSame b v 2 w).trans (pfWireTr2 b v w)

theorem pfTrEq3 (b : Bool) (v w : Nat) : piTransition b v 3 w = pfTr3 b v w :=
  (pfTransitionSame b v 3 w).trans (pfWireTr3 b v w)

theorem pfGoodEq (v : Nat) : piGood v = pfGood v := (pfGoodSame v).trans (pfWireGood v)

theorem pfDataEq : pfRows = piRowList := rfl

theorem pfEdgeEq : pfEdges = piEdges := rfl

theorem pfPassEq (i : Nat) : piStatePass i = pfPass i := by
  unfold piStatePass pfPass
  rw [pfDataEq, pfEdgeEq]
  change (piGood piRowList[i]! && ((decide ((piEdges[i]!)[0]! < 683) && piTransition false piRowList[i]! 0 piRowList[(piEdges[i]!)[0]!]!) && ((decide ((piEdges[i]!)[1]! < 683) && piTransition false piRowList[i]! 1 piRowList[(piEdges[i]!)[1]!]!) && ((decide ((piEdges[i]!)[2]! < 683) && piTransition false piRowList[i]! 2 piRowList[(piEdges[i]!)[2]!]!) && ((decide ((piEdges[i]!)[3]! < 683) && piTransition false piRowList[i]! 3 piRowList[(piEdges[i]!)[3]!]!) && true))))) = _
  rw [pfGoodEq, pfTrEq0, pfTrEq1, pfTrEq2, pfTrEq3]
