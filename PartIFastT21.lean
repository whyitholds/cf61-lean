import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase672 : pfCheckTree 672 = true := by
  apply pfTreeLift 672 ⟨pfV672,672,586,562,346⟩ pfV672 pfV586 pfV562 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase673 : pfCheckTree 673 = true := by
  apply pfTreeLift 673 ⟨pfV673,673,555,556,137⟩ pfV673 pfV555 pfV556 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase674 : pfCheckTree 674 = true := by
  apply pfTreeLift 674 ⟨pfV674,674,555,556,285⟩ pfV674 pfV555 pfV556 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase675 : pfCheckTree 675 = true := by
  apply pfTreeLift 675 ⟨pfV675,675,572,556,137⟩ pfV675 pfV572 pfV556 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase676 : pfCheckTree 676 = true := by
  apply pfTreeLift 676 ⟨pfV676,676,555,556,137⟩ pfV676 pfV555 pfV556 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase677 : pfCheckTree 677 = true := by
  apply pfTreeLift 677 ⟨pfV677,677,548,558,137⟩ pfV677 pfV548 pfV558 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase678 : pfCheckTree 678 = true := by
  apply pfTreeLift 678 ⟨pfV678,678,548,558,285⟩ pfV678 pfV548 pfV558 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase679 : pfCheckTree 679 = true := by
  apply pfTreeLift 679 ⟨pfV679,679,414,624,167⟩ pfV679 pfV414 pfV624 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase680 : pfCheckTree 680 = true := by
  apply pfTreeLift 680 ⟨pfV680,680,395,403,167⟩ pfV680 pfV395 pfV403 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase681 : pfCheckTree 681 = true := by
  apply pfTreeLift 681 ⟨pfV681,681,497,654,167⟩ pfV681 pfV497 pfV654 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase682 : pfCheckTree 682 = true := by
  apply pfTreeLift 682 ⟨pfV682,682,661,515,238⟩ pfV682 pfV661 pfV515 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup21 : pfTRange 672 11 :=
  (pfTJoin 672 5 6 (pfTJoin 672 2 3 (pfTJoin 672 1 1 (pfTOne 672 pfTCase672) (pfTOne 673 pfTCase673)) (pfTJoin 674 1 2 (pfTOne 674 pfTCase674) (pfTJoin 675 1 1 (pfTOne 675 pfTCase675) (pfTOne 676 pfTCase676)))) (pfTJoin 677 3 3 (pfTJoin 677 1 2 (pfTOne 677 pfTCase677) (pfTJoin 678 1 1 (pfTOne 678 pfTCase678) (pfTOne 679 pfTCase679))) (pfTJoin 680 1 2 (pfTOne 680 pfTCase680) (pfTJoin 681 1 1 (pfTOne 681 pfTCase681) (pfTOne 682 pfTCase682)))))
