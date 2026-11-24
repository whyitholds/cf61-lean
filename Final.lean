import Statement
import StatementCor1
import Proof
import ProofCor1
-- All eight named statements in one conjunction.
theorem final : _root_.CF61_Main ∧ _root_.CF61_PartII ∧ _root_.CF61_PartI ∧ _root_.CF61_Closed ∧ _root_.CF61_Sharp ∧ _root_.CF61_Coords ∧ _root_.CF61_Cor1_i ∧ _root_.CF61_Cor1_ii :=
  ⟨_root_.proof_main, _root_.proof_partII, _root_.proof_partI, _root_.proof_closed, _root_.proof_sharp, _root_.proof_coords, _root_.proof_cor1_i, _root_.proof_cor1_ii⟩
#print axioms final
