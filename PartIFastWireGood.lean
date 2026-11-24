import PartIFastRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfWireGood (v : Nat) : pfWGood v = pfGood v := rfl
