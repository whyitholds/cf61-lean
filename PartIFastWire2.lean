import PartIFastRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfWireTr2 (b : Bool) (v w : Nat) : pfWTransition b v 2 w = pfTr2 b v w := rfl
