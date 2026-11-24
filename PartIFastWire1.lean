import PartIFastRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfWireTr1 (b : Bool) (v w : Nat) : pfWTransition b v 1 w = pfTr1 b v w := rfl
