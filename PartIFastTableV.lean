import PartIFastMap
import PartIFastData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfOriginalV : pfProjected PFTEntry.v pfKnownTree 683 = pfRows := rfl

theorem pfLookupV (i : Nat) (hi : i < 683) : pfRows[i]! = PFTEntry.v (pfEntry i) := by
  rw [← pfOriginalV]
  exact pfProjectedGet PFTEntry.v pfKnownTree 683 i (by decide) hi
