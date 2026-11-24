import WAltPure

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem waCol0 : (List.range 4).all (fun i => waPass (0+i)) = true := by
  decide +kernel
