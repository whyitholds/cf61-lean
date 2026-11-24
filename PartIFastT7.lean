import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase224 : pfCheckTree 224 = true := by
  apply pfTreeLift 224 ⟨pfV224,509,510,224,238⟩ pfV509 pfV510 pfV224 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase225 : pfCheckTree 225 = true := by
  apply pfTreeLift 225 ⟨pfV225,511,107,144,130⟩ pfV511 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase226 : pfCheckTree 226 = true := by
  apply pfTreeLift 226 ⟨pfV226,226,512,430,130⟩ pfV226 pfV512 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase227 : pfCheckTree 227 = true := by
  apply pfTreeLift 227 ⟨pfV227,513,227,188,130⟩ pfV513 pfV227 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase228 : pfCheckTree 228 = true := by
  apply pfTreeLift 228 ⟨pfV228,228,514,515,316⟩ pfV228 pfV514 pfV515 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase229 : pfCheckTree 229 = true := by
  apply pfTreeLift 229 ⟨pfV229,317,516,229,144⟩ pfV317 pfV516 pfV229 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase230 : pfCheckTree 230 = true := by
  apply pfTreeLift 230 ⟨pfV230,517,240,188,130⟩ pfV517 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase231 : pfCheckTree 231 = true := by
  apply pfTreeLift 231 ⟨pfV231,231,514,518,234⟩ pfV231 pfV514 pfV518 pfV234 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase232 : pfCheckTree 232 = true := by
  apply pfTreeLift 232 ⟨pfV232,519,232,520,167⟩ pfV519 pfV232 pfV520 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase233 : pfCheckTree 233 = true := by
  apply pfTreeLift 233 ⟨pfV233,521,522,523,238⟩ pfV521 pfV522 pfV523 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase234 : pfCheckTree 234 = true := by
  apply pfTreeLift 234 ⟨pfV234,524,107,144,130⟩ pfV524 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase235 : pfCheckTree 235 = true := by
  apply pfTreeLift 235 ⟨pfV235,235,525,229,238⟩ pfV235 pfV525 pfV229 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase236 : pfCheckTree 236 = true := by
  apply pfTreeLift 236 ⟨pfV236,526,527,528,234⟩ pfV526 pfV527 pfV528 pfV234 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase237 : pfCheckTree 237 = true := by
  apply pfTreeLift 237 ⟨pfV237,529,236,237,238⟩ pfV529 pfV236 pfV237 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase238 : pfCheckTree 238 = true := by
  apply pfTreeLift 238 ⟨pfV238,530,107,144,130⟩ pfV530 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase239 : pfCheckTree 239 = true := by
  apply pfTreeLift 239 ⟨pfV239,239,531,532,130⟩ pfV239 pfV531 pfV532 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase240 : pfCheckTree 240 = true := by
  apply pfTreeLift 240 ⟨pfV240,533,240,188,130⟩ pfV533 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase241 : pfCheckTree 241 = true := by
  apply pfTreeLift 241 ⟨pfV241,534,240,241,130⟩ pfV534 pfV240 pfV241 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase242 : pfCheckTree 242 = true := by
  apply pfTreeLift 242 ⟨pfV242,242,242,535,107⟩ pfV242 pfV242 pfV535 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase243 : pfCheckTree 243 = true := by
  apply pfTreeLift 243 ⟨pfV243,243,536,243,144⟩ pfV243 pfV536 pfV243 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase244 : pfCheckTree 244 = true := by
  apply pfTreeLift 244 ⟨pfV244,244,242,535,194⟩ pfV244 pfV242 pfV535 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase245 : pfCheckTree 245 = true := by
  apply pfTreeLift 245 ⟨pfV245,537,245,246,194⟩ pfV537 pfV245 pfV246 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase246 : pfCheckTree 246 = true := by
  apply pfTreeLift 246 ⟨pfV246,538,539,540,250⟩ pfV538 pfV539 pfV540 pfV250 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase247 : pfCheckTree 247 = true := by
  apply pfTreeLift 247 ⟨pfV247,247,536,243,250⟩ pfV247 pfV536 pfV243 pfV250 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase248 : pfCheckTree 248 = true := by
  apply pfTreeLift 248 ⟨pfV248,541,539,540,194⟩ pfV541 pfV539 pfV540 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase249 : pfCheckTree 249 = true := by
  apply pfTreeLift 249 ⟨pfV249,542,248,249,410⟩ pfV542 pfV248 pfV249 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase250 : pfCheckTree 250 = true := by
  apply pfTreeLift 250 ⟨pfV250,543,107,144,130⟩ pfV543 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase251 : pfCheckTree 251 = true := by
  apply pfTreeLift 251 ⟨pfV251,251,544,390,130⟩ pfV251 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase252 : pfCheckTree 252 = true := by
  apply pfTreeLift 252 ⟨pfV252,252,253,545,255⟩ pfV252 pfV253 pfV545 pfV255 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase253 : pfCheckTree 253 = true := by
  apply pfTreeLift 253 ⟨pfV253,546,266,547,107⟩ pfV546 pfV266 pfV547 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase254 : pfCheckTree 254 = true := by
  apply pfTreeLift 254 ⟨pfV254,254,548,278,549⟩ pfV254 pfV548 pfV278 pfV549 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase255 : pfCheckTree 255 = true := by
  apply pfTreeLift 255 ⟨pfV255,550,551,552,83⟩ pfV550 pfV551 pfV552 pfV83 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup7 : pfTRange 224 32 :=
  (pfTJoin 224 16 16 (pfTJoin 224 8 8 (pfTJoin 224 4 4 (pfTJoin 224 2 2 (pfTJoin 224 1 1 (pfTOne 224 pfTCase224) (pfTOne 225 pfTCase225)) (pfTJoin 226 1 1 (pfTOne 226 pfTCase226) (pfTOne 227 pfTCase227))) (pfTJoin 228 2 2 (pfTJoin 228 1 1 (pfTOne 228 pfTCase228) (pfTOne 229 pfTCase229)) (pfTJoin 230 1 1 (pfTOne 230 pfTCase230) (pfTOne 231 pfTCase231)))) (pfTJoin 232 4 4 (pfTJoin 232 2 2 (pfTJoin 232 1 1 (pfTOne 232 pfTCase232) (pfTOne 233 pfTCase233)) (pfTJoin 234 1 1 (pfTOne 234 pfTCase234) (pfTOne 235 pfTCase235))) (pfTJoin 236 2 2 (pfTJoin 236 1 1 (pfTOne 236 pfTCase236) (pfTOne 237 pfTCase237)) (pfTJoin 238 1 1 (pfTOne 238 pfTCase238) (pfTOne 239 pfTCase239))))) (pfTJoin 240 8 8 (pfTJoin 240 4 4 (pfTJoin 240 2 2 (pfTJoin 240 1 1 (pfTOne 240 pfTCase240) (pfTOne 241 pfTCase241)) (pfTJoin 242 1 1 (pfTOne 242 pfTCase242) (pfTOne 243 pfTCase243))) (pfTJoin 244 2 2 (pfTJoin 244 1 1 (pfTOne 244 pfTCase244) (pfTOne 245 pfTCase245)) (pfTJoin 246 1 1 (pfTOne 246 pfTCase246) (pfTOne 247 pfTCase247)))) (pfTJoin 248 4 4 (pfTJoin 248 2 2 (pfTJoin 248 1 1 (pfTOne 248 pfTCase248) (pfTOne 249 pfTCase249)) (pfTJoin 250 1 1 (pfTOne 250 pfTCase250) (pfTOne 251 pfTCase251))) (pfTJoin 252 2 2 (pfTJoin 252 1 1 (pfTOne 252 pfTCase252) (pfTOne 253 pfTCase253)) (pfTJoin 254 1 1 (pfTOne 254 pfTCase254) (pfTOne 255 pfTCase255))))))
