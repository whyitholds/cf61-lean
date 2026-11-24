import PartIFastRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfWireTr0 (b : Bool) (v w : Nat) : pfWTransition b v 0 w = pfTr0 b v w := rfl
