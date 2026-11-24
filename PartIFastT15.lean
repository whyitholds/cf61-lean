import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase480 : pfCheckTree 480 = true := by
  apply pfTreeLift 480 ⟨pfV480,480,216,500,107⟩ pfV480 pfV216 pfV500 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase481 : pfCheckTree 481 = true := by
  apply pfTreeLift 481 ⟨pfV481,481,482,645,484⟩ pfV481 pfV482 pfV645 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase482 : pfCheckTree 482 = true := by
  apply pfTreeLift 482 ⟨pfV482,482,482,645,107⟩ pfV482 pfV482 pfV645 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase483 : pfCheckTree 483 = true := by
  apply pfTreeLift 483 ⟨pfV483,483,482,483,144⟩ pfV483 pfV482 pfV483 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase484 : pfCheckTree 484 = true := by
  apply pfTreeLift 484 ⟨pfV484,651,107,144,130⟩ pfV651 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase485 : pfCheckTree 485 = true := by
  apply pfTreeLift 485 ⟨pfV485,485,544,390,130⟩ pfV485 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase486 : pfCheckTree 486 = true := by
  apply pfTreeLift 486 ⟨pfV486,486,487,315,316⟩ pfV486 pfV487 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase487 : pfCheckTree 487 = true := by
  apply pfTreeLift 487 ⟨pfV487,487,487,315,107⟩ pfV487 pfV487 pfV315 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase488 : pfCheckTree 488 = true := by
  apply pfTreeLift 488 ⟨pfV488,488,593,315,316⟩ pfV488 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase489 : pfCheckTree 489 = true := by
  apply pfTreeLift 489 ⟨pfV489,489,544,390,130⟩ pfV489 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase490 : pfCheckTree 490 = true := by
  apply pfTreeLift 490 ⟨pfV490,490,490,648,107⟩ pfV490 pfV490 pfV648 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase491 : pfCheckTree 491 = true := by
  apply pfTreeLift 491 ⟨pfV491,491,647,491,144⟩ pfV491 pfV647 pfV491 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase492 : pfCheckTree 492 = true := by
  apply pfTreeLift 492 ⟨pfV492,492,490,648,194⟩ pfV492 pfV490 pfV648 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase493 : pfCheckTree 493 = true := by
  apply pfTreeLift 493 ⟨pfV493,652,477,478,410⟩ pfV652 pfV477 pfV478 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase494 : pfCheckTree 494 = true := by
  apply pfTreeLift 494 ⟨pfV494,494,647,491,410⟩ pfV494 pfV647 pfV491 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase495 : pfCheckTree 495 = true := by
  apply pfTreeLift 495 ⟨pfV495,653,477,495,410⟩ pfV653 pfV477 pfV495 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase496 : pfCheckTree 496 = true := by
  apply pfTreeLift 496 ⟨pfV496,496,482,645,484⟩ pfV496 pfV482 pfV645 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase497 : pfCheckTree 497 = true := by
  apply pfTreeLift 497 ⟨pfV497,497,497,654,107⟩ pfV497 pfV497 pfV654 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase498 : pfCheckTree 498 = true := by
  apply pfTreeLift 498 ⟨pfV498,498,497,498,144⟩ pfV498 pfV497 pfV498 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase499 : pfCheckTree 499 = true := by
  apply pfTreeLift 499 ⟨pfV499,499,531,430,130⟩ pfV499 pfV531 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase500 : pfCheckTree 500 = true := by
  apply pfTreeLift 500 ⟨pfV500,500,482,645,484⟩ pfV500 pfV482 pfV645 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase501 : pfCheckTree 501 = true := by
  apply pfTreeLift 501 ⟨pfV501,501,216,500,167⟩ pfV501 pfV216 pfV500 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase502 : pfCheckTree 502 = true := by
  apply pfTreeLift 502 ⟨pfV502,502,482,645,225⟩ pfV502 pfV482 pfV645 pfV225 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase503 : pfCheckTree 503 = true := by
  apply pfTreeLift 503 ⟨pfV503,655,503,504,167⟩ pfV655 pfV503 pfV504 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase504 : pfCheckTree 504 = true := by
  apply pfTreeLift 504 ⟨pfV504,656,503,504,238⟩ pfV656 pfV503 pfV504 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase505 : pfCheckTree 505 = true := by
  apply pfTreeLift 505 ⟨pfV505,505,505,654,107⟩ pfV505 pfV505 pfV654 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase506 : pfCheckTree 506 = true := by
  apply pfTreeLift 506 ⟨pfV506,506,505,654,167⟩ pfV506 pfV505 pfV654 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase507 : pfCheckTree 507 = true := by
  apply pfTreeLift 507 ⟨pfV507,657,507,508,167⟩ pfV657 pfV507 pfV508 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase508 : pfCheckTree 508 = true := by
  apply pfTreeLift 508 ⟨pfV508,658,659,508,238⟩ pfV658 pfV659 pfV508 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase509 : pfCheckTree 509 = true := by
  apply pfTreeLift 509 ⟨pfV509,509,497,498,238⟩ pfV509 pfV497 pfV498 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase510 : pfCheckTree 510 = true := by
  apply pfTreeLift 510 ⟨pfV510,660,659,508,167⟩ pfV660 pfV659 pfV508 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase511 : pfCheckTree 511 = true := by
  apply pfTreeLift 511 ⟨pfV511,511,544,390,130⟩ pfV511 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup15 : pfTRange 480 32 :=
  (pfTJoin 480 16 16 (pfTJoin 480 8 8 (pfTJoin 480 4 4 (pfTJoin 480 2 2 (pfTJoin 480 1 1 (pfTOne 480 pfTCase480) (pfTOne 481 pfTCase481)) (pfTJoin 482 1 1 (pfTOne 482 pfTCase482) (pfTOne 483 pfTCase483))) (pfTJoin 484 2 2 (pfTJoin 484 1 1 (pfTOne 484 pfTCase484) (pfTOne 485 pfTCase485)) (pfTJoin 486 1 1 (pfTOne 486 pfTCase486) (pfTOne 487 pfTCase487)))) (pfTJoin 488 4 4 (pfTJoin 488 2 2 (pfTJoin 488 1 1 (pfTOne 488 pfTCase488) (pfTOne 489 pfTCase489)) (pfTJoin 490 1 1 (pfTOne 490 pfTCase490) (pfTOne 491 pfTCase491))) (pfTJoin 492 2 2 (pfTJoin 492 1 1 (pfTOne 492 pfTCase492) (pfTOne 493 pfTCase493)) (pfTJoin 494 1 1 (pfTOne 494 pfTCase494) (pfTOne 495 pfTCase495))))) (pfTJoin 496 8 8 (pfTJoin 496 4 4 (pfTJoin 496 2 2 (pfTJoin 496 1 1 (pfTOne 496 pfTCase496) (pfTOne 497 pfTCase497)) (pfTJoin 498 1 1 (pfTOne 498 pfTCase498) (pfTOne 499 pfTCase499))) (pfTJoin 500 2 2 (pfTJoin 500 1 1 (pfTOne 500 pfTCase500) (pfTOne 501 pfTCase501)) (pfTJoin 502 1 1 (pfTOne 502 pfTCase502) (pfTOne 503 pfTCase503)))) (pfTJoin 504 4 4 (pfTJoin 504 2 2 (pfTJoin 504 1 1 (pfTOne 504 pfTCase504) (pfTOne 505 pfTCase505)) (pfTJoin 506 1 1 (pfTOne 506 pfTCase506) (pfTOne 507 pfTCase507))) (pfTJoin 508 2 2 (pfTJoin 508 1 1 (pfTOne 508 pfTCase508) (pfTOne 509 pfTCase509)) (pfTJoin 510 1 1 (pfTOne 510 pfTCase510) (pfTOne 511 pfTCase511))))))
