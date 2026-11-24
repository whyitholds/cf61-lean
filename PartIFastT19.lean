import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase608 : pfCheckTree 608 = true := by
  apply pfTreeLift 608 ⟨pfV608,608,358,610,360⟩ pfV608 pfV358 pfV610 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase609 : pfCheckTree 609 = true := by
  apply pfTreeLift 609 ⟨pfV609,609,358,610,360⟩ pfV609 pfV358 pfV610 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase610 : pfCheckTree 610 = true := by
  apply pfTreeLift 610 ⟨pfV610,610,358,610,144⟩ pfV610 pfV358 pfV610 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase611 : pfCheckTree 611 = true := by
  apply pfTreeLift 611 ⟨pfV611,611,544,390,130⟩ pfV611 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase612 : pfCheckTree 612 = true := by
  apply pfTreeLift 612 ⟨pfV612,612,544,390,130⟩ pfV612 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase613 : pfCheckTree 613 = true := by
  apply pfTreeLift 613 ⟨pfV613,613,544,390,130⟩ pfV613 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase614 : pfCheckTree 614 = true := by
  apply pfTreeLift 614 ⟨pfV614,614,374,614,144⟩ pfV614 pfV374 pfV614 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase615 : pfCheckTree 615 = true := by
  apply pfTreeLift 615 ⟨pfV615,615,374,614,137⟩ pfV615 pfV374 pfV614 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase616 : pfCheckTree 616 = true := by
  apply pfTreeLift 616 ⟨pfV616,616,374,614,285⟩ pfV616 pfV374 pfV614 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase617 : pfCheckTree 617 = true := by
  apply pfTreeLift 617 ⟨pfV617,617,383,614,137⟩ pfV617 pfV383 pfV614 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase618 : pfCheckTree 618 = true := by
  apply pfTreeLift 618 ⟨pfV618,618,374,614,137⟩ pfV618 pfV374 pfV614 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase619 : pfCheckTree 619 = true := by
  apply pfTreeLift 619 ⟨pfV619,619,544,390,130⟩ pfV619 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase620 : pfCheckTree 620 = true := by
  apply pfTreeLift 620 ⟨pfV620,620,620,407,107⟩ pfV620 pfV620 pfV407 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase621 : pfCheckTree 621 = true := by
  apply pfTreeLift 621 ⟨pfV621,621,620,407,194⟩ pfV621 pfV620 pfV407 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase622 : pfCheckTree 622 = true := by
  apply pfTreeLift 622 ⟨pfV622,622,620,407,410⟩ pfV622 pfV620 pfV407 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase623 : pfCheckTree 623 = true := by
  apply pfTreeLift 623 ⟨pfV623,623,544,390,130⟩ pfV623 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase624 : pfCheckTree 624 = true := by
  apply pfTreeLift 624 ⟨pfV624,624,414,624,144⟩ pfV624 pfV414 pfV624 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase625 : pfCheckTree 625 = true := by
  apply pfTreeLift 625 ⟨pfV625,625,309,336,167⟩ pfV625 pfV309 pfV336 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase626 : pfCheckTree 626 = true := by
  apply pfTreeLift 626 ⟨pfV626,626,309,336,238⟩ pfV626 pfV309 pfV336 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase627 : pfCheckTree 627 = true := by
  apply pfTreeLift 627 ⟨pfV627,627,422,624,167⟩ pfV627 pfV422 pfV624 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase628 : pfCheckTree 628 = true := by
  apply pfTreeLift 628 ⟨pfV628,628,414,624,238⟩ pfV628 pfV414 pfV624 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase629 : pfCheckTree 629 = true := by
  apply pfTreeLift 629 ⟨pfV629,679,629,425,167⟩ pfV679 pfV629 pfV425 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase630 : pfCheckTree 630 = true := by
  apply pfTreeLift 630 ⟨pfV630,630,414,624,167⟩ pfV630 pfV414 pfV624 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase631 : pfCheckTree 631 = true := by
  apply pfTreeLift 631 ⟨pfV631,631,631,632,107⟩ pfV631 pfV631 pfV632 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase632 : pfCheckTree 632 = true := by
  apply pfTreeLift 632 ⟨pfV632,632,631,632,144⟩ pfV632 pfV631 pfV632 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase633 : pfCheckTree 633 = true := by
  apply pfTreeLift 633 ⟨pfV633,633,631,632,167⟩ pfV633 pfV631 pfV632 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase634 : pfCheckTree 634 = true := by
  apply pfTreeLift 634 ⟨pfV634,634,631,632,238⟩ pfV634 pfV631 pfV632 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase635 : pfCheckTree 635 = true := by
  apply pfTreeLift 635 ⟨pfV635,635,442,403,167⟩ pfV635 pfV442 pfV403 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase636 : pfCheckTree 636 = true := by
  apply pfTreeLift 636 ⟨pfV636,636,395,403,238⟩ pfV636 pfV395 pfV403 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase637 : pfCheckTree 637 = true := by
  apply pfTreeLift 637 ⟨pfV637,680,637,445,167⟩ pfV680 pfV637 pfV445 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase638 : pfCheckTree 638 = true := by
  apply pfTreeLift 638 ⟨pfV638,638,395,403,181⟩ pfV638 pfV395 pfV403 pfV181 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase639 : pfCheckTree 639 = true := by
  apply pfTreeLift 639 ⟨pfV639,639,454,639,144⟩ pfV639 pfV454 pfV639 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup19 : pfTRange 608 32 :=
  (pfTJoin 608 16 16 (pfTJoin 608 8 8 (pfTJoin 608 4 4 (pfTJoin 608 2 2 (pfTJoin 608 1 1 (pfTOne 608 pfTCase608) (pfTOne 609 pfTCase609)) (pfTJoin 610 1 1 (pfTOne 610 pfTCase610) (pfTOne 611 pfTCase611))) (pfTJoin 612 2 2 (pfTJoin 612 1 1 (pfTOne 612 pfTCase612) (pfTOne 613 pfTCase613)) (pfTJoin 614 1 1 (pfTOne 614 pfTCase614) (pfTOne 615 pfTCase615)))) (pfTJoin 616 4 4 (pfTJoin 616 2 2 (pfTJoin 616 1 1 (pfTOne 616 pfTCase616) (pfTOne 617 pfTCase617)) (pfTJoin 618 1 1 (pfTOne 618 pfTCase618) (pfTOne 619 pfTCase619))) (pfTJoin 620 2 2 (pfTJoin 620 1 1 (pfTOne 620 pfTCase620) (pfTOne 621 pfTCase621)) (pfTJoin 622 1 1 (pfTOne 622 pfTCase622) (pfTOne 623 pfTCase623))))) (pfTJoin 624 8 8 (pfTJoin 624 4 4 (pfTJoin 624 2 2 (pfTJoin 624 1 1 (pfTOne 624 pfTCase624) (pfTOne 625 pfTCase625)) (pfTJoin 626 1 1 (pfTOne 626 pfTCase626) (pfTOne 627 pfTCase627))) (pfTJoin 628 2 2 (pfTJoin 628 1 1 (pfTOne 628 pfTCase628) (pfTOne 629 pfTCase629)) (pfTJoin 630 1 1 (pfTOne 630 pfTCase630) (pfTOne 631 pfTCase631)))) (pfTJoin 632 4 4 (pfTJoin 632 2 2 (pfTJoin 632 1 1 (pfTOne 632 pfTCase632) (pfTOne 633 pfTCase633)) (pfTJoin 634 1 1 (pfTOne 634 pfTCase634) (pfTOne 635 pfTCase635))) (pfTJoin 636 2 2 (pfTJoin 636 1 1 (pfTOne 636 pfTCase636) (pfTOne 637 pfTCase637)) (pfTJoin 638 1 1 (pfTOne 638 pfTCase638) (pfTOne 639 pfTCase639))))))
