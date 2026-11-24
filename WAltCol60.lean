import WAltPure

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem waCol60 : (List.range 4).all (fun i => waPass (60+i)) = true := by
  decide +kernel
