import PartIFastRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfWireTr3 (b : Bool) (v w : Nat) : pfWTransition b v 3 w = pfTr3 b v w := rfl
