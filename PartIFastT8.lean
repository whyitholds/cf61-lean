import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase256 : pfCheckTree 256 = true := by
  apply pfTreeLift 256 ⟨pfV256,256,266,553,107⟩ pfV256 pfV266 pfV553 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase257 : pfCheckTree 257 = true := by
  apply pfTreeLift 257 ⟨pfV257,546,257,554,107⟩ pfV546 pfV257 pfV554 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase258 : pfCheckTree 258 = true := by
  apply pfTreeLift 258 ⟨pfV258,258,555,556,484⟩ pfV258 pfV555 pfV556 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase259 : pfCheckTree 259 = true := by
  apply pfTreeLift 259 ⟨pfV259,259,557,278,262⟩ pfV259 pfV557 pfV278 pfV262 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase260 : pfCheckTree 260 = true := by
  apply pfTreeLift 260 ⟨pfV260,260,557,558,107⟩ pfV260 pfV557 pfV558 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase261 : pfCheckTree 261 = true := by
  apply pfTreeLift 261 ⟨pfV261,278,559,261,144⟩ pfV278 pfV559 pfV261 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase262 : pfCheckTree 262 = true := by
  apply pfTreeLift 262 ⟨pfV262,560,107,144,130⟩ pfV560 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase263 : pfCheckTree 263 = true := by
  apply pfTreeLift 263 ⟨pfV263,263,561,562,83⟩ pfV263 pfV561 pfV562 pfV83 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase264 : pfCheckTree 264 = true := by
  apply pfTreeLift 264 ⟨pfV264,563,264,265,115⟩ pfV563 pfV264 pfV265 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase265 : pfCheckTree 265 = true := by
  apply pfTreeLift 265 ⟨pfV265,564,551,552,346⟩ pfV564 pfV551 pfV552 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase266 : pfCheckTree 266 = true := by
  apply pfTreeLift 266 ⟨pfV266,546,266,565,107⟩ pfV546 pfV266 pfV565 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase267 : pfCheckTree 267 = true := by
  apply pfTreeLift 267 ⟨pfV267,267,555,566,484⟩ pfV267 pfV555 pfV566 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase268 : pfCheckTree 268 = true := by
  apply pfTreeLift 268 ⟨pfV268,567,107,144,130⟩ pfV567 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase269 : pfCheckTree 269 = true := by
  apply pfTreeLift 269 ⟨pfV269,269,266,553,137⟩ pfV269 pfV266 pfV553 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase270 : pfCheckTree 270 = true := by
  apply pfTreeLift 270 ⟨pfV270,568,270,271,137⟩ pfV568 pfV270 pfV271 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase271 : pfCheckTree 271 = true := by
  apply pfTreeLift 271 ⟨pfV271,569,570,571,79⟩ pfV569 pfV570 pfV571 pfV79 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase272 : pfCheckTree 272 = true := by
  apply pfTreeLift 272 ⟨pfV272,272,572,566,79⟩ pfV272 pfV572 pfV566 pfV79 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase273 : pfCheckTree 273 = true := by
  apply pfTreeLift 273 ⟨pfV273,573,574,571,137⟩ pfV573 pfV574 pfV571 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase274 : pfCheckTree 274 = true := by
  apply pfTreeLift 274 ⟨pfV274,575,576,274,285⟩ pfV575 pfV576 pfV274 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase275 : pfCheckTree 275 = true := by
  apply pfTreeLift 275 ⟨pfV275,275,577,390,130⟩ pfV275 pfV577 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase276 : pfCheckTree 276 = true := by
  apply pfTreeLift 276 ⟨pfV276,578,276,144,130⟩ pfV578 pfV276 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase277 : pfCheckTree 277 = true := by
  apply pfTreeLift 277 ⟨pfV277,277,277,558,107⟩ pfV277 pfV277 pfV558 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase278 : pfCheckTree 278 = true := by
  apply pfTreeLift 278 ⟨pfV278,278,548,278,144⟩ pfV278 pfV548 pfV278 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase279 : pfCheckTree 279 = true := by
  apply pfTreeLift 279 ⟨pfV279,279,277,558,268⟩ pfV279 pfV277 pfV558 pfV268 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase280 : pfCheckTree 280 = true := by
  apply pfTreeLift 280 ⟨pfV280,579,280,281,137⟩ pfV579 pfV280 pfV281 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase281 : pfCheckTree 281 = true := by
  apply pfTreeLift 281 ⟨pfV281,580,581,582,285⟩ pfV580 pfV581 pfV582 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase282 : pfCheckTree 282 = true := by
  apply pfTreeLift 282 ⟨pfV282,282,548,278,285⟩ pfV282 pfV548 pfV278 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase283 : pfCheckTree 283 = true := by
  apply pfTreeLift 283 ⟨pfV283,583,581,582,268⟩ pfV583 pfV581 pfV582 pfV268 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase284 : pfCheckTree 284 = true := by
  apply pfTreeLift 284 ⟨pfV284,584,283,284,285⟩ pfV584 pfV283 pfV284 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase285 : pfCheckTree 285 = true := by
  apply pfTreeLift 285 ⟨pfV285,585,107,144,130⟩ pfV585 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase286 : pfCheckTree 286 = true := by
  apply pfTreeLift 286 ⟨pfV286,286,544,390,130⟩ pfV286 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase287 : pfCheckTree 287 = true := by
  apply pfTreeLift 287 ⟨pfV287,287,287,562,107⟩ pfV287 pfV287 pfV562 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup8 : pfTRange 256 32 :=
  (pfTJoin 256 16 16 (pfTJoin 256 8 8 (pfTJoin 256 4 4 (pfTJoin 256 2 2 (pfTJoin 256 1 1 (pfTOne 256 pfTCase256) (pfTOne 257 pfTCase257)) (pfTJoin 258 1 1 (pfTOne 258 pfTCase258) (pfTOne 259 pfTCase259))) (pfTJoin 260 2 2 (pfTJoin 260 1 1 (pfTOne 260 pfTCase260) (pfTOne 261 pfTCase261)) (pfTJoin 262 1 1 (pfTOne 262 pfTCase262) (pfTOne 263 pfTCase263)))) (pfTJoin 264 4 4 (pfTJoin 264 2 2 (pfTJoin 264 1 1 (pfTOne 264 pfTCase264) (pfTOne 265 pfTCase265)) (pfTJoin 266 1 1 (pfTOne 266 pfTCase266) (pfTOne 267 pfTCase267))) (pfTJoin 268 2 2 (pfTJoin 268 1 1 (pfTOne 268 pfTCase268) (pfTOne 269 pfTCase269)) (pfTJoin 270 1 1 (pfTOne 270 pfTCase270) (pfTOne 271 pfTCase271))))) (pfTJoin 272 8 8 (pfTJoin 272 4 4 (pfTJoin 272 2 2 (pfTJoin 272 1 1 (pfTOne 272 pfTCase272) (pfTOne 273 pfTCase273)) (pfTJoin 274 1 1 (pfTOne 274 pfTCase274) (pfTOne 275 pfTCase275))) (pfTJoin 276 2 2 (pfTJoin 276 1 1 (pfTOne 276 pfTCase276) (pfTOne 277 pfTCase277)) (pfTJoin 278 1 1 (pfTOne 278 pfTCase278) (pfTOne 279 pfTCase279)))) (pfTJoin 280 4 4 (pfTJoin 280 2 2 (pfTJoin 280 1 1 (pfTOne 280 pfTCase280) (pfTOne 281 pfTCase281)) (pfTJoin 282 1 1 (pfTOne 282 pfTCase282) (pfTOne 283 pfTCase283))) (pfTJoin 284 2 2 (pfTJoin 284 1 1 (pfTOne 284 pfTCase284) (pfTOne 285 pfTCase285)) (pfTJoin 286 1 1 (pfTOne 286 pfTCase286) (pfTOne 287 pfTCase287))))))
