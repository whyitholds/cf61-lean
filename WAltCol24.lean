import WAltPure

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem waCol24 : (List.range 4).all (fun i => waPass (24+i)) = true := by
  decide +kernel
