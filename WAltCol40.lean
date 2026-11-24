import WAltPure

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem waCol40 : (List.range 4).all (fun i => waPass (40+i)) = true := by
  decide +kernel
