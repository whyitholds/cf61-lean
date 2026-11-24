import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase160 : pfCheckTree 160 = true := by
  apply pfTreeLift 160 ⟨pfV160,160,161,412,163⟩ pfV160 pfV161 pfV412 pfV163 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase161 : pfCheckTree 161 = true := by
  apply pfTreeLift 161 ⟨pfV161,307,161,413,107⟩ pfV307 pfV161 pfV413 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase162 : pfCheckTree 162 = true := by
  apply pfTreeLift 162 ⟨pfV162,162,414,415,311⟩ pfV162 pfV414 pfV415 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase163 : pfCheckTree 163 = true := by
  apply pfTreeLift 163 ⟨pfV163,416,240,188,130⟩ pfV416 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase164 : pfCheckTree 164 = true := by
  apply pfTreeLift 164 ⟨pfV164,164,161,335,167⟩ pfV164 pfV161 pfV335 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase165 : pfCheckTree 165 = true := by
  apply pfTreeLift 165 ⟨pfV165,417,165,166,167⟩ pfV417 pfV165 pfV166 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase166 : pfCheckTree 166 = true := by
  apply pfTreeLift 166 ⟨pfV166,418,419,420,171⟩ pfV418 pfV419 pfV420 pfV171 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase167 : pfCheckTree 167 = true := by
  apply pfTreeLift 167 ⟨pfV167,421,107,144,130⟩ pfV421 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase168 : pfCheckTree 168 = true := by
  apply pfTreeLift 168 ⟨pfV168,168,422,415,171⟩ pfV168 pfV422 pfV415 pfV171 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase169 : pfCheckTree 169 = true := by
  apply pfTreeLift 169 ⟨pfV169,423,424,425,167⟩ pfV423 pfV424 pfV425 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase170 : pfCheckTree 170 = true := by
  apply pfTreeLift 170 ⟨pfV170,426,427,170,238⟩ pfV426 pfV427 pfV170 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase171 : pfCheckTree 171 = true := by
  apply pfTreeLift 171 ⟨pfV171,428,107,144,130⟩ pfV428 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase172 : pfCheckTree 172 = true := by
  apply pfTreeLift 172 ⟨pfV172,172,429,430,130⟩ pfV172 pfV429 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase173 : pfCheckTree 173 = true := by
  apply pfTreeLift 173 ⟨pfV173,431,173,174,130⟩ pfV431 pfV173 pfV174 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase174 : pfCheckTree 174 = true := by
  apply pfTreeLift 174 ⟨pfV174,432,240,188,130⟩ pfV432 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase175 : pfCheckTree 175 = true := by
  apply pfTreeLift 175 ⟨pfV175,433,175,434,107⟩ pfV433 pfV175 pfV434 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase176 : pfCheckTree 176 = true := by
  apply pfTreeLift 176 ⟨pfV176,176,395,396,360⟩ pfV176 pfV395 pfV396 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase177 : pfCheckTree 177 = true := by
  apply pfTreeLift 177 ⟨pfV177,435,240,188,130⟩ pfV435 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase178 : pfCheckTree 178 = true := by
  apply pfTreeLift 178 ⟨pfV178,178,175,436,181⟩ pfV178 pfV175 pfV436 pfV181 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase179 : pfCheckTree 179 = true := by
  apply pfTreeLift 179 ⟨pfV179,437,179,180,167⟩ pfV437 pfV179 pfV180 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase180 : pfCheckTree 180 = true := by
  apply pfTreeLift 180 ⟨pfV180,438,439,440,185⟩ pfV438 pfV439 pfV440 pfV185 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase181 : pfCheckTree 181 = true := by
  apply pfTreeLift 181 ⟨pfV181,441,107,144,130⟩ pfV441 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase182 : pfCheckTree 182 = true := by
  apply pfTreeLift 182 ⟨pfV182,182,442,396,185⟩ pfV182 pfV442 pfV396 pfV185 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase183 : pfCheckTree 183 = true := by
  apply pfTreeLift 183 ⟨pfV183,443,444,445,181⟩ pfV443 pfV444 pfV445 pfV181 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase184 : pfCheckTree 184 = true := by
  apply pfTreeLift 184 ⟨pfV184,446,447,184,238⟩ pfV446 pfV447 pfV184 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase185 : pfCheckTree 185 = true := by
  apply pfTreeLift 185 ⟨pfV185,448,107,144,130⟩ pfV448 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase186 : pfCheckTree 186 = true := by
  apply pfTreeLift 186 ⟨pfV186,186,449,430,130⟩ pfV186 pfV449 pfV430 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase187 : pfCheckTree 187 = true := by
  apply pfTreeLift 187 ⟨pfV187,450,187,188,130⟩ pfV450 pfV187 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase188 : pfCheckTree 188 = true := by
  apply pfTreeLift 188 ⟨pfV188,451,240,188,130⟩ pfV451 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase189 : pfCheckTree 189 = true := by
  apply pfTreeLift 189 ⟨pfV189,452,189,453,107⟩ pfV452 pfV189 pfV453 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase190 : pfCheckTree 190 = true := by
  apply pfTreeLift 190 ⟨pfV190,190,454,455,360⟩ pfV190 pfV454 pfV455 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase191 : pfCheckTree 191 = true := by
  apply pfTreeLift 191 ⟨pfV191,191,189,456,194⟩ pfV191 pfV189 pfV456 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup5 : pfTRange 160 32 :=
  (pfTJoin 160 16 16 (pfTJoin 160 8 8 (pfTJoin 160 4 4 (pfTJoin 160 2 2 (pfTJoin 160 1 1 (pfTOne 160 pfTCase160) (pfTOne 161 pfTCase161)) (pfTJoin 162 1 1 (pfTOne 162 pfTCase162) (pfTOne 163 pfTCase163))) (pfTJoin 164 2 2 (pfTJoin 164 1 1 (pfTOne 164 pfTCase164) (pfTOne 165 pfTCase165)) (pfTJoin 166 1 1 (pfTOne 166 pfTCase166) (pfTOne 167 pfTCase167)))) (pfTJoin 168 4 4 (pfTJoin 168 2 2 (pfTJoin 168 1 1 (pfTOne 168 pfTCase168) (pfTOne 169 pfTCase169)) (pfTJoin 170 1 1 (pfTOne 170 pfTCase170) (pfTOne 171 pfTCase171))) (pfTJoin 172 2 2 (pfTJoin 172 1 1 (pfTOne 172 pfTCase172) (pfTOne 173 pfTCase173)) (pfTJoin 174 1 1 (pfTOne 174 pfTCase174) (pfTOne 175 pfTCase175))))) (pfTJoin 176 8 8 (pfTJoin 176 4 4 (pfTJoin 176 2 2 (pfTJoin 176 1 1 (pfTOne 176 pfTCase176) (pfTOne 177 pfTCase177)) (pfTJoin 178 1 1 (pfTOne 178 pfTCase178) (pfTOne 179 pfTCase179))) (pfTJoin 180 2 2 (pfTJoin 180 1 1 (pfTOne 180 pfTCase180) (pfTOne 181 pfTCase181)) (pfTJoin 182 1 1 (pfTOne 182 pfTCase182) (pfTOne 183 pfTCase183)))) (pfTJoin 184 4 4 (pfTJoin 184 2 2 (pfTJoin 184 1 1 (pfTOne 184 pfTCase184) (pfTOne 185 pfTCase185)) (pfTJoin 186 1 1 (pfTOne 186 pfTCase186) (pfTOne 187 pfTCase187))) (pfTJoin 188 2 2 (pfTJoin 188 1 1 (pfTOne 188 pfTCase188) (pfTOne 189 pfTCase189)) (pfTJoin 190 1 1 (pfTOne 190 pfTCase190) (pfTOne 191 pfTCase191))))))
