import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase128 : pfCheckTree 128 = true := by
  apply pfTreeLift 128 ⟨pfV128,369,128,334,115⟩ pfV369 pfV128 pfV334 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase129 : pfCheckTree 129 = true := by
  apply pfTreeLift 129 ⟨pfV129,370,333,129,346⟩ pfV370 pfV333 pfV129 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase130 : pfCheckTree 130 = true := by
  apply pfTreeLift 130 ⟨pfV130,371,107,144,130⟩ pfV371 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase131 : pfCheckTree 131 = true := by
  apply pfTreeLift 131 ⟨pfV131,372,131,373,107⟩ pfV372 pfV131 pfV373 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase132 : pfCheckTree 132 = true := by
  apply pfTreeLift 132 ⟨pfV132,132,374,375,360⟩ pfV132 pfV374 pfV375 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase133 : pfCheckTree 133 = true := by
  apply pfTreeLift 133 ⟨pfV133,376,107,144,130⟩ pfV376 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase134 : pfCheckTree 134 = true := by
  apply pfTreeLift 134 ⟨pfV134,134,131,377,137⟩ pfV134 pfV131 pfV377 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase135 : pfCheckTree 135 = true := by
  apply pfTreeLift 135 ⟨pfV135,378,135,136,137⟩ pfV378 pfV135 pfV136 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase136 : pfCheckTree 136 = true := by
  apply pfTreeLift 136 ⟨pfV136,379,380,381,141⟩ pfV379 pfV380 pfV381 pfV141 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase137 : pfCheckTree 137 = true := by
  apply pfTreeLift 137 ⟨pfV137,382,107,144,130⟩ pfV382 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase138 : pfCheckTree 138 = true := by
  apply pfTreeLift 138 ⟨pfV138,138,383,375,141⟩ pfV138 pfV383 pfV375 pfV141 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase139 : pfCheckTree 139 = true := by
  apply pfTreeLift 139 ⟨pfV139,384,385,381,137⟩ pfV384 pfV385 pfV381 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase140 : pfCheckTree 140 = true := by
  apply pfTreeLift 140 ⟨pfV140,386,387,140,285⟩ pfV386 pfV387 pfV140 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase141 : pfCheckTree 141 = true := by
  apply pfTreeLift 141 ⟨pfV141,388,107,144,130⟩ pfV388 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase142 : pfCheckTree 142 = true := by
  apply pfTreeLift 142 ⟨pfV142,142,389,390,130⟩ pfV142 pfV389 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase143 : pfCheckTree 143 = true := by
  apply pfTreeLift 143 ⟨pfV143,391,143,144,130⟩ pfV391 pfV143 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase144 : pfCheckTree 144 = true := by
  apply pfTreeLift 144 ⟨pfV144,392,107,144,130⟩ pfV392 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase145 : pfCheckTree 145 = true := by
  apply pfTreeLift 145 ⟨pfV145,145,146,393,148⟩ pfV145 pfV146 pfV393 pfV148 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase146 : pfCheckTree 146 = true := by
  apply pfTreeLift 146 ⟨pfV146,307,161,394,107⟩ pfV307 pfV161 pfV394 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase147 : pfCheckTree 147 = true := by
  apply pfTreeLift 147 ⟨pfV147,147,395,396,397⟩ pfV147 pfV395 pfV396 pfV397 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase148 : pfCheckTree 148 = true := by
  apply pfTreeLift 148 ⟨pfV148,398,399,400,159⟩ pfV398 pfV399 pfV400 pfV159 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase149 : pfCheckTree 149 = true := by
  apply pfTreeLift 149 ⟨pfV149,149,161,335,107⟩ pfV149 pfV161 pfV335 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase150 : pfCheckTree 150 = true := by
  apply pfTreeLift 150 ⟨pfV150,307,150,401,107⟩ pfV307 pfV150 pfV401 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase151 : pfCheckTree 151 = true := by
  apply pfTreeLift 151 ⟨pfV151,151,309,336,311⟩ pfV151 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase152 : pfCheckTree 152 = true := by
  apply pfTreeLift 152 ⟨pfV152,152,402,396,155⟩ pfV152 pfV402 pfV396 pfV155 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase153 : pfCheckTree 153 = true := by
  apply pfTreeLift 153 ⟨pfV153,153,402,403,107⟩ pfV153 pfV402 pfV403 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase154 : pfCheckTree 154 = true := by
  apply pfTreeLift 154 ⟨pfV154,396,404,154,144⟩ pfV396 pfV404 pfV154 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase155 : pfCheckTree 155 = true := by
  apply pfTreeLift 155 ⟨pfV155,405,107,144,130⟩ pfV405 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase156 : pfCheckTree 156 = true := by
  apply pfTreeLift 156 ⟨pfV156,156,406,407,159⟩ pfV156 pfV406 pfV407 pfV159 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase157 : pfCheckTree 157 = true := by
  apply pfTreeLift 157 ⟨pfV157,408,157,158,194⟩ pfV408 pfV157 pfV158 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase158 : pfCheckTree 158 = true := by
  apply pfTreeLift 158 ⟨pfV158,409,399,400,410⟩ pfV409 pfV399 pfV400 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase159 : pfCheckTree 159 = true := by
  apply pfTreeLift 159 ⟨pfV159,411,107,144,130⟩ pfV411 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup4 : pfTRange 128 32 :=
  (pfTJoin 128 16 16 (pfTJoin 128 8 8 (pfTJoin 128 4 4 (pfTJoin 128 2 2 (pfTJoin 128 1 1 (pfTOne 128 pfTCase128) (pfTOne 129 pfTCase129)) (pfTJoin 130 1 1 (pfTOne 130 pfTCase130) (pfTOne 131 pfTCase131))) (pfTJoin 132 2 2 (pfTJoin 132 1 1 (pfTOne 132 pfTCase132) (pfTOne 133 pfTCase133)) (pfTJoin 134 1 1 (pfTOne 134 pfTCase134) (pfTOne 135 pfTCase135)))) (pfTJoin 136 4 4 (pfTJoin 136 2 2 (pfTJoin 136 1 1 (pfTOne 136 pfTCase136) (pfTOne 137 pfTCase137)) (pfTJoin 138 1 1 (pfTOne 138 pfTCase138) (pfTOne 139 pfTCase139))) (pfTJoin 140 2 2 (pfTJoin 140 1 1 (pfTOne 140 pfTCase140) (pfTOne 141 pfTCase141)) (pfTJoin 142 1 1 (pfTOne 142 pfTCase142) (pfTOne 143 pfTCase143))))) (pfTJoin 144 8 8 (pfTJoin 144 4 4 (pfTJoin 144 2 2 (pfTJoin 144 1 1 (pfTOne 144 pfTCase144) (pfTOne 145 pfTCase145)) (pfTJoin 146 1 1 (pfTOne 146 pfTCase146) (pfTOne 147 pfTCase147))) (pfTJoin 148 2 2 (pfTJoin 148 1 1 (pfTOne 148 pfTCase148) (pfTOne 149 pfTCase149)) (pfTJoin 150 1 1 (pfTOne 150 pfTCase150) (pfTOne 151 pfTCase151)))) (pfTJoin 152 4 4 (pfTJoin 152 2 2 (pfTJoin 152 1 1 (pfTOne 152 pfTCase152) (pfTOne 153 pfTCase153)) (pfTJoin 154 1 1 (pfTOne 154 pfTCase154) (pfTOne 155 pfTCase155))) (pfTJoin 156 2 2 (pfTJoin 156 1 1 (pfTOne 156 pfTCase156) (pfTOne 157 pfTCase157)) (pfTJoin 158 1 1 (pfTOne 158 pfTCase158) (pfTOne 159 pfTCase159))))))
