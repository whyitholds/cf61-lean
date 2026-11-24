import WeightPure
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

theorem pwBoundCheck : ∀ q : Fin 32, (pwTable[q.val]!).all
    (fun p => decide (p.1 < 72 ∧ p.2.1 < 8)) = true := by decide +kernel
