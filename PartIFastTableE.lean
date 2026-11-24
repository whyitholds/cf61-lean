import PartIFastMap
import PartIFastData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfOriginalE : pfProjected pfAsEdges pfKnownTree 683 = pfEdges := rfl

theorem pfLookupE (i : Nat) (hi : i < 683) : pfEdges[i]! = pfAsEdges (pfEntry i) := by
  rw [← pfOriginalE]
  exact pfProjectedGet pfAsEdges pfKnownTree 683 i (by decide) hi
