import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase448 : pfCheckTree 448 = true := by
  apply pfTreeLift 448 ⟨pfV448,448,544,390,130⟩ pfV448 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase449 : pfCheckTree 449 = true := by
  apply pfTreeLift 449 ⟨pfV449,449,449,430,107⟩ pfV449 pfV449 pfV430 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase450 : pfCheckTree 450 = true := by
  apply pfTreeLift 450 ⟨pfV450,450,449,430,130⟩ pfV450 pfV449 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase451 : pfCheckTree 451 = true := by
  apply pfTreeLift 451 ⟨pfV451,451,531,430,130⟩ pfV451 pfV531 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase452 : pfCheckTree 452 = true := by
  apply pfTreeLift 452 ⟨pfV452,452,189,456,107⟩ pfV452 pfV189 pfV456 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase453 : pfCheckTree 453 = true := by
  apply pfTreeLift 453 ⟨pfV453,453,454,639,360⟩ pfV453 pfV454 pfV639 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase454 : pfCheckTree 454 = true := by
  apply pfTreeLift 454 ⟨pfV454,454,454,639,107⟩ pfV454 pfV454 pfV639 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase455 : pfCheckTree 455 = true := by
  apply pfTreeLift 455 ⟨pfV455,455,454,455,144⟩ pfV455 pfV454 pfV455 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase456 : pfCheckTree 456 = true := by
  apply pfTreeLift 456 ⟨pfV456,456,454,639,360⟩ pfV456 pfV454 pfV639 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase457 : pfCheckTree 457 = true := by
  apply pfTreeLift 457 ⟨pfV457,457,189,456,194⟩ pfV457 pfV189 pfV456 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase458 : pfCheckTree 458 = true := by
  apply pfTreeLift 458 ⟨pfV458,458,454,639,198⟩ pfV458 pfV454 pfV639 pfV198 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase459 : pfCheckTree 459 = true := by
  apply pfTreeLift 459 ⟨pfV459,640,459,460,194⟩ pfV640 pfV459 pfV460 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase460 : pfCheckTree 460 = true := by
  apply pfTreeLift 460 ⟨pfV460,641,459,460,410⟩ pfV641 pfV459 pfV460 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase461 : pfCheckTree 461 = true := by
  apply pfTreeLift 461 ⟨pfV461,461,544,390,130⟩ pfV461 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase462 : pfCheckTree 462 = true := by
  apply pfTreeLift 462 ⟨pfV462,462,462,639,107⟩ pfV462 pfV462 pfV639 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase463 : pfCheckTree 463 = true := by
  apply pfTreeLift 463 ⟨pfV463,463,462,639,194⟩ pfV463 pfV462 pfV639 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase464 : pfCheckTree 464 = true := by
  apply pfTreeLift 464 ⟨pfV464,642,464,460,194⟩ pfV642 pfV464 pfV460 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase465 : pfCheckTree 465 = true := by
  apply pfTreeLift 465 ⟨pfV465,465,454,455,410⟩ pfV465 pfV454 pfV455 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase466 : pfCheckTree 466 = true := by
  apply pfTreeLift 466 ⟨pfV466,643,459,460,194⟩ pfV643 pfV459 pfV460 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase467 : pfCheckTree 467 = true := by
  apply pfTreeLift 467 ⟨pfV467,467,544,390,130⟩ pfV467 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase468 : pfCheckTree 468 = true := by
  apply pfTreeLift 468 ⟨pfV468,468,468,390,107⟩ pfV468 pfV468 pfV390 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase469 : pfCheckTree 469 = true := by
  apply pfTreeLift 469 ⟨pfV469,469,468,390,130⟩ pfV469 pfV468 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase470 : pfCheckTree 470 = true := by
  apply pfTreeLift 470 ⟨pfV470,644,474,229,475⟩ pfV644 pfV474 pfV229 pfV475 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase471 : pfCheckTree 471 = true := by
  apply pfTreeLift 471 ⟨pfV471,471,216,500,208⟩ pfV471 pfV216 pfV500 pfV208 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase472 : pfCheckTree 472 = true := by
  apply pfTreeLift 472 ⟨pfV472,472,482,645,484⟩ pfV472 pfV482 pfV645 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase473 : pfCheckTree 473 = true := by
  apply pfTreeLift 473 ⟨pfV473,473,525,229,475⟩ pfV473 pfV525 pfV229 pfV475 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase474 : pfCheckTree 474 = true := by
  apply pfTreeLift 474 ⟨pfV474,474,593,315,316⟩ pfV474 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase475 : pfCheckTree 475 = true := by
  apply pfTreeLift 475 ⟨pfV475,646,107,144,130⟩ pfV646 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase476 : pfCheckTree 476 = true := by
  apply pfTreeLift 476 ⟨pfV476,476,647,648,67⟩ pfV476 pfV647 pfV648 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase477 : pfCheckTree 477 = true := by
  apply pfTreeLift 477 ⟨pfV477,649,477,478,194⟩ pfV649 pfV477 pfV478 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase478 : pfCheckTree 478 = true := by
  apply pfTreeLift 478 ⟨pfV478,650,477,478,410⟩ pfV650 pfV477 pfV478 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase479 : pfCheckTree 479 = true := by
  apply pfTreeLift 479 ⟨pfV479,479,482,483,484⟩ pfV479 pfV482 pfV483 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup14 : pfTRange 448 32 :=
  (pfTJoin 448 16 16 (pfTJoin 448 8 8 (pfTJoin 448 4 4 (pfTJoin 448 2 2 (pfTJoin 448 1 1 (pfTOne 448 pfTCase448) (pfTOne 449 pfTCase449)) (pfTJoin 450 1 1 (pfTOne 450 pfTCase450) (pfTOne 451 pfTCase451))) (pfTJoin 452 2 2 (pfTJoin 452 1 1 (pfTOne 452 pfTCase452) (pfTOne 453 pfTCase453)) (pfTJoin 454 1 1 (pfTOne 454 pfTCase454) (pfTOne 455 pfTCase455)))) (pfTJoin 456 4 4 (pfTJoin 456 2 2 (pfTJoin 456 1 1 (pfTOne 456 pfTCase456) (pfTOne 457 pfTCase457)) (pfTJoin 458 1 1 (pfTOne 458 pfTCase458) (pfTOne 459 pfTCase459))) (pfTJoin 460 2 2 (pfTJoin 460 1 1 (pfTOne 460 pfTCase460) (pfTOne 461 pfTCase461)) (pfTJoin 462 1 1 (pfTOne 462 pfTCase462) (pfTOne 463 pfTCase463))))) (pfTJoin 464 8 8 (pfTJoin 464 4 4 (pfTJoin 464 2 2 (pfTJoin 464 1 1 (pfTOne 464 pfTCase464) (pfTOne 465 pfTCase465)) (pfTJoin 466 1 1 (pfTOne 466 pfTCase466) (pfTOne 467 pfTCase467))) (pfTJoin 468 2 2 (pfTJoin 468 1 1 (pfTOne 468 pfTCase468) (pfTOne 469 pfTCase469)) (pfTJoin 470 1 1 (pfTOne 470 pfTCase470) (pfTOne 471 pfTCase471)))) (pfTJoin 472 4 4 (pfTJoin 472 2 2 (pfTJoin 472 1 1 (pfTOne 472 pfTCase472) (pfTOne 473 pfTCase473)) (pfTJoin 474 1 1 (pfTOne 474 pfTCase474) (pfTOne 475 pfTCase475))) (pfTJoin 476 2 2 (pfTJoin 476 1 1 (pfTOne 476 pfTCase476) (pfTOne 477 pfTCase477)) (pfTJoin 478 1 1 (pfTOne 478 pfTCase478) (pfTOne 479 pfTCase479))))))
