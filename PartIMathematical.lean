import PartICombo
import PartIVerify
import PartILift
import PartITail
import PartIWeight

theorem piPartIByGraph (closed : CF61_Closed) (atStart : piFirstPass = true)
    (atState : ∀ i : ℕ, i < 683 → piStatePass i = true) : CF61_PartI := by
  apply piPartIFromRules closed
  · intro d a v l s j e ha hv hl hs hj he
    exact piLiftCount d (2^d) a v j e l s rfl ha hv hj he hl hs
  · exact piFirstOfPass atStart
  · exact piStepOfPass atState
  · exact piAcceptWeight
  · exact piGoodOfPass atState
  · intro k d a v ah D r hp hk ha hv hD hr
    exact piTrueCountEqPairs hp hk ha hv hD hr
