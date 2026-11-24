import PartIFastInit
import PartIFastLink
import PartIFastTableV

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem piFastFirst : piFirstPass = true := by
  have hrow (i : Nat) (hi : i < 683) : piRowList[i]! = (pfEntry i).v := by
    rw [← pfDataEq]
    exact pfLookupV i hi
  change ((decide (0 < 683) && piTransition true piStart 0 piRowList[0]!) && ((decide (1 < 683) && piTransition true piStart 1 piRowList[1]!) && ((decide (2 < 683) && piTransition true piStart 2 piRowList[2]!) && ((decide (3 < 683) && piTransition true piStart 3 piRowList[3]!) && true)))) = true
  rw [hrow 0 (by decide), hrow 1 (by decide), hrow 2 (by decide), hrow 3 (by decide),
    pfTrEq0, pfTrEq1, pfTrEq2, pfTrEq3]
  exact pfInitData
