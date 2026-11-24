import PartIFastTAll
import PartIFastInitLink
import PartIFastTreeLink

theorem piFastAll (i : Nat) (hi : i < 683) : piStatePass i = true := by
  rw [pfPassEq]
  exact pfCertByTree i hi (pfTAll i (Nat.zero_le i) hi)

