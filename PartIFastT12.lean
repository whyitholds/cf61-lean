import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase384 : pfCheckTree 384 = true := by
  apply pfTreeLift 384 ⟨pfV384,384,383,614,137⟩ pfV384 pfV383 pfV614 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase385 : pfCheckTree 385 = true := by
  apply pfTreeLift 385 ⟨pfV385,617,385,381,137⟩ pfV617 pfV385 pfV381 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase386 : pfCheckTree 386 = true := by
  apply pfTreeLift 386 ⟨pfV386,386,374,375,285⟩ pfV386 pfV374 pfV375 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase387 : pfCheckTree 387 = true := by
  apply pfTreeLift 387 ⟨pfV387,618,380,381,137⟩ pfV618 pfV380 pfV381 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase388 : pfCheckTree 388 = true := by
  apply pfTreeLift 388 ⟨pfV388,388,544,390,130⟩ pfV388 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase389 : pfCheckTree 389 = true := by
  apply pfTreeLift 389 ⟨pfV389,389,389,390,107⟩ pfV389 pfV389 pfV390 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase390 : pfCheckTree 390 = true := by
  apply pfTreeLift 390 ⟨pfV390,390,544,390,144⟩ pfV390 pfV544 pfV390 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase391 : pfCheckTree 391 = true := by
  apply pfTreeLift 391 ⟨pfV391,391,389,390,130⟩ pfV391 pfV389 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase392 : pfCheckTree 392 = true := by
  apply pfTreeLift 392 ⟨pfV392,392,544,390,130⟩ pfV392 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase393 : pfCheckTree 393 = true := by
  apply pfTreeLift 393 ⟨pfV393,393,395,396,397⟩ pfV393 pfV395 pfV396 pfV397 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase394 : pfCheckTree 394 = true := by
  apply pfTreeLift 394 ⟨pfV394,394,309,336,311⟩ pfV394 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase395 : pfCheckTree 395 = true := by
  apply pfTreeLift 395 ⟨pfV395,395,395,403,107⟩ pfV395 pfV395 pfV403 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase396 : pfCheckTree 396 = true := by
  apply pfTreeLift 396 ⟨pfV396,396,395,396,144⟩ pfV396 pfV395 pfV396 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase397 : pfCheckTree 397 = true := by
  apply pfTreeLift 397 ⟨pfV397,619,107,144,130⟩ pfV619 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase398 : pfCheckTree 398 = true := by
  apply pfTreeLift 398 ⟨pfV398,398,620,407,159⟩ pfV398 pfV620 pfV407 pfV159 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase399 : pfCheckTree 399 = true := by
  apply pfTreeLift 399 ⟨pfV399,621,399,400,194⟩ pfV621 pfV399 pfV400 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase400 : pfCheckTree 400 = true := by
  apply pfTreeLift 400 ⟨pfV400,622,399,400,410⟩ pfV622 pfV399 pfV400 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase401 : pfCheckTree 401 = true := by
  apply pfTreeLift 401 ⟨pfV401,401,309,336,311⟩ pfV401 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase402 : pfCheckTree 402 = true := by
  apply pfTreeLift 402 ⟨pfV402,402,402,403,107⟩ pfV402 pfV402 pfV403 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase403 : pfCheckTree 403 = true := by
  apply pfTreeLift 403 ⟨pfV403,403,395,403,144⟩ pfV403 pfV395 pfV403 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase404 : pfCheckTree 404 = true := by
  apply pfTreeLift 404 ⟨pfV404,404,395,403,107⟩ pfV404 pfV395 pfV403 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase405 : pfCheckTree 405 = true := by
  apply pfTreeLift 405 ⟨pfV405,405,544,390,130⟩ pfV405 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase406 : pfCheckTree 406 = true := by
  apply pfTreeLift 406 ⟨pfV406,406,406,407,107⟩ pfV406 pfV406 pfV407 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase407 : pfCheckTree 407 = true := by
  apply pfTreeLift 407 ⟨pfV407,407,620,407,144⟩ pfV407 pfV620 pfV407 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase408 : pfCheckTree 408 = true := by
  apply pfTreeLift 408 ⟨pfV408,408,406,407,194⟩ pfV408 pfV406 pfV407 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase409 : pfCheckTree 409 = true := by
  apply pfTreeLift 409 ⟨pfV409,409,620,407,410⟩ pfV409 pfV620 pfV407 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase410 : pfCheckTree 410 = true := by
  apply pfTreeLift 410 ⟨pfV410,623,107,144,130⟩ pfV623 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase411 : pfCheckTree 411 = true := by
  apply pfTreeLift 411 ⟨pfV411,411,544,390,130⟩ pfV411 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase412 : pfCheckTree 412 = true := by
  apply pfTreeLift 412 ⟨pfV412,412,414,415,311⟩ pfV412 pfV414 pfV415 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase413 : pfCheckTree 413 = true := by
  apply pfTreeLift 413 ⟨pfV413,413,309,336,311⟩ pfV413 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase414 : pfCheckTree 414 = true := by
  apply pfTreeLift 414 ⟨pfV414,414,414,624,107⟩ pfV414 pfV414 pfV624 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase415 : pfCheckTree 415 = true := by
  apply pfTreeLift 415 ⟨pfV415,415,414,415,144⟩ pfV415 pfV414 pfV415 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup12 : pfTRange 384 32 :=
  (pfTJoin 384 16 16 (pfTJoin 384 8 8 (pfTJoin 384 4 4 (pfTJoin 384 2 2 (pfTJoin 384 1 1 (pfTOne 384 pfTCase384) (pfTOne 385 pfTCase385)) (pfTJoin 386 1 1 (pfTOne 386 pfTCase386) (pfTOne 387 pfTCase387))) (pfTJoin 388 2 2 (pfTJoin 388 1 1 (pfTOne 388 pfTCase388) (pfTOne 389 pfTCase389)) (pfTJoin 390 1 1 (pfTOne 390 pfTCase390) (pfTOne 391 pfTCase391)))) (pfTJoin 392 4 4 (pfTJoin 392 2 2 (pfTJoin 392 1 1 (pfTOne 392 pfTCase392) (pfTOne 393 pfTCase393)) (pfTJoin 394 1 1 (pfTOne 394 pfTCase394) (pfTOne 395 pfTCase395))) (pfTJoin 396 2 2 (pfTJoin 396 1 1 (pfTOne 396 pfTCase396) (pfTOne 397 pfTCase397)) (pfTJoin 398 1 1 (pfTOne 398 pfTCase398) (pfTOne 399 pfTCase399))))) (pfTJoin 400 8 8 (pfTJoin 400 4 4 (pfTJoin 400 2 2 (pfTJoin 400 1 1 (pfTOne 400 pfTCase400) (pfTOne 401 pfTCase401)) (pfTJoin 402 1 1 (pfTOne 402 pfTCase402) (pfTOne 403 pfTCase403))) (pfTJoin 404 2 2 (pfTJoin 404 1 1 (pfTOne 404 pfTCase404) (pfTOne 405 pfTCase405)) (pfTJoin 406 1 1 (pfTOne 406 pfTCase406) (pfTOne 407 pfTCase407)))) (pfTJoin 408 4 4 (pfTJoin 408 2 2 (pfTJoin 408 1 1 (pfTOne 408 pfTCase408) (pfTOne 409 pfTCase409)) (pfTJoin 410 1 1 (pfTOne 410 pfTCase410) (pfTOne 411 pfTCase411))) (pfTJoin 412 2 2 (pfTJoin 412 1 1 (pfTOne 412 pfTCase412) (pfTOne 413 pfTCase413)) (pfTJoin 414 1 1 (pfTOne 414 pfTCase414) (pfTOne 415 pfTCase415))))))
