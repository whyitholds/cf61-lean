import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase512 : pfCheckTree 512 = true := by
  apply pfTreeLift 512 ⟨pfV512,512,512,430,107⟩ pfV512 pfV512 pfV430 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase513 : pfCheckTree 513 = true := by
  apply pfTreeLift 513 ⟨pfV513,513,512,430,130⟩ pfV513 pfV512 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase514 : pfCheckTree 514 = true := by
  apply pfTreeLift 514 ⟨pfV514,514,514,515,107⟩ pfV514 pfV514 pfV515 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase515 : pfCheckTree 515 = true := by
  apply pfTreeLift 515 ⟨pfV515,515,661,515,144⟩ pfV515 pfV661 pfV515 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase516 : pfCheckTree 516 = true := by
  apply pfTreeLift 516 ⟨pfV516,516,593,315,316⟩ pfV516 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase517 : pfCheckTree 517 = true := by
  apply pfTreeLift 517 ⟨pfV517,517,531,430,130⟩ pfV517 pfV531 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase518 : pfCheckTree 518 = true := by
  apply pfTreeLift 518 ⟨pfV518,518,661,518,144⟩ pfV518 pfV661 pfV518 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase519 : pfCheckTree 519 = true := by
  apply pfTreeLift 519 ⟨pfV519,519,514,515,167⟩ pfV519 pfV514 pfV515 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase520 : pfCheckTree 520 = true := by
  apply pfTreeLift 520 ⟨pfV520,662,522,663,238⟩ pfV662 pfV522 pfV663 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase521 : pfCheckTree 521 = true := by
  apply pfTreeLift 521 ⟨pfV521,521,661,518,238⟩ pfV521 pfV661 pfV518 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase522 : pfCheckTree 522 = true := by
  apply pfTreeLift 522 ⟨pfV522,664,522,663,167⟩ pfV664 pfV522 pfV663 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase523 : pfCheckTree 523 = true := by
  apply pfTreeLift 523 ⟨pfV523,665,522,523,238⟩ pfV665 pfV522 pfV523 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase524 : pfCheckTree 524 = true := by
  apply pfTreeLift 524 ⟨pfV524,524,544,390,130⟩ pfV524 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase525 : pfCheckTree 525 = true := by
  apply pfTreeLift 525 ⟨pfV525,525,593,315,316⟩ pfV525 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase526 : pfCheckTree 526 = true := by
  apply pfTreeLift 526 ⟨pfV526,526,593,315,234⟩ pfV526 pfV593 pfV315 pfV234 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase527 : pfCheckTree 527 = true := by
  apply pfTreeLift 527 ⟨pfV527,666,527,528,167⟩ pfV666 pfV527 pfV528 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase528 : pfCheckTree 528 = true := by
  apply pfTreeLift 528 ⟨pfV528,667,527,528,238⟩ pfV667 pfV527 pfV528 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase529 : pfCheckTree 529 = true := by
  apply pfTreeLift 529 ⟨pfV529,529,525,229,238⟩ pfV529 pfV525 pfV229 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase530 : pfCheckTree 530 = true := by
  apply pfTreeLift 530 ⟨pfV530,530,544,390,130⟩ pfV530 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase531 : pfCheckTree 531 = true := by
  apply pfTreeLift 531 ⟨pfV531,531,531,430,107⟩ pfV531 pfV531 pfV430 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase532 : pfCheckTree 532 = true := by
  apply pfTreeLift 532 ⟨pfV532,532,531,532,144⟩ pfV532 pfV531 pfV532 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase533 : pfCheckTree 533 = true := by
  apply pfTreeLift 533 ⟨pfV533,533,531,430,130⟩ pfV533 pfV531 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase534 : pfCheckTree 534 = true := by
  apply pfTreeLift 534 ⟨pfV534,534,531,532,130⟩ pfV534 pfV531 pfV532 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase535 : pfCheckTree 535 = true := by
  apply pfTreeLift 535 ⟨pfV535,535,536,535,144⟩ pfV535 pfV536 pfV535 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase536 : pfCheckTree 536 = true := by
  apply pfTreeLift 536 ⟨pfV536,536,536,535,107⟩ pfV536 pfV536 pfV535 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase537 : pfCheckTree 537 = true := by
  apply pfTreeLift 537 ⟨pfV537,537,242,535,194⟩ pfV537 pfV242 pfV535 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase538 : pfCheckTree 538 = true := by
  apply pfTreeLift 538 ⟨pfV538,538,536,535,250⟩ pfV538 pfV536 pfV535 pfV250 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase539 : pfCheckTree 539 = true := by
  apply pfTreeLift 539 ⟨pfV539,668,539,540,194⟩ pfV668 pfV539 pfV540 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase540 : pfCheckTree 540 = true := by
  apply pfTreeLift 540 ⟨pfV540,669,539,540,410⟩ pfV669 pfV539 pfV540 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase541 : pfCheckTree 541 = true := by
  apply pfTreeLift 541 ⟨pfV541,541,536,535,194⟩ pfV541 pfV536 pfV535 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase542 : pfCheckTree 542 = true := by
  apply pfTreeLift 542 ⟨pfV542,542,536,243,410⟩ pfV542 pfV536 pfV243 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase543 : pfCheckTree 543 = true := by
  apply pfTreeLift 543 ⟨pfV543,543,544,390,130⟩ pfV543 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup16 : pfTRange 512 32 :=
  (pfTJoin 512 16 16 (pfTJoin 512 8 8 (pfTJoin 512 4 4 (pfTJoin 512 2 2 (pfTJoin 512 1 1 (pfTOne 512 pfTCase512) (pfTOne 513 pfTCase513)) (pfTJoin 514 1 1 (pfTOne 514 pfTCase514) (pfTOne 515 pfTCase515))) (pfTJoin 516 2 2 (pfTJoin 516 1 1 (pfTOne 516 pfTCase516) (pfTOne 517 pfTCase517)) (pfTJoin 518 1 1 (pfTOne 518 pfTCase518) (pfTOne 519 pfTCase519)))) (pfTJoin 520 4 4 (pfTJoin 520 2 2 (pfTJoin 520 1 1 (pfTOne 520 pfTCase520) (pfTOne 521 pfTCase521)) (pfTJoin 522 1 1 (pfTOne 522 pfTCase522) (pfTOne 523 pfTCase523))) (pfTJoin 524 2 2 (pfTJoin 524 1 1 (pfTOne 524 pfTCase524) (pfTOne 525 pfTCase525)) (pfTJoin 526 1 1 (pfTOne 526 pfTCase526) (pfTOne 527 pfTCase527))))) (pfTJoin 528 8 8 (pfTJoin 528 4 4 (pfTJoin 528 2 2 (pfTJoin 528 1 1 (pfTOne 528 pfTCase528) (pfTOne 529 pfTCase529)) (pfTJoin 530 1 1 (pfTOne 530 pfTCase530) (pfTOne 531 pfTCase531))) (pfTJoin 532 2 2 (pfTJoin 532 1 1 (pfTOne 532 pfTCase532) (pfTOne 533 pfTCase533)) (pfTJoin 534 1 1 (pfTOne 534 pfTCase534) (pfTOne 535 pfTCase535)))) (pfTJoin 536 4 4 (pfTJoin 536 2 2 (pfTJoin 536 1 1 (pfTOne 536 pfTCase536) (pfTOne 537 pfTCase537)) (pfTJoin 538 1 1 (pfTOne 538 pfTCase538) (pfTOne 539 pfTCase539))) (pfTJoin 540 2 2 (pfTJoin 540 1 1 (pfTOne 540 pfTCase540) (pfTOne 541 pfTCase541)) (pfTJoin 542 1 1 (pfTOne 542 pfTCase542) (pfTOne 543 pfTCase543))))))
