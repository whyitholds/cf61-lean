import StatementCor1
import UlamExist
import CorRank

open OneAdd CF61

theorem proof_cor1_i : CF61_Cor1_i := by
  refine ⟨cfUlamExists, ?_⟩
  intro m hm
  dsimp only
  intro x hx N ho _ hN l c r hc
  exact corOddTable hm hx ho hN hc

theorem proof_cor1_ii : CF61_Cor1_ii := by
  refine ⟨cfUlamExists, ?_⟩
  intro m hm
  dsimp only
  intro x hx
  exact corRank hm hx
