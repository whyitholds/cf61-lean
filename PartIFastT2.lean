import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase64 : pfCheckTree 64 = true := by
  apply pfTreeLift 64 ⟨pfV64,64,242,243,67⟩ pfV64 pfV242 pfV243 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase65 : pfCheckTree 65 = true := by
  apply pfTreeLift 65 ⟨pfV65,244,245,246,194⟩ pfV244 pfV245 pfV246 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase66 : pfCheckTree 66 = true := by
  apply pfTreeLift 66 ⟨pfV66,247,248,249,250⟩ pfV247 pfV248 pfV249 pfV250 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase67 : pfCheckTree 67 = true := by
  apply pfTreeLift 67 ⟨pfV67,251,107,144,130⟩ pfV251 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase68 : pfCheckTree 68 = true := by
  apply pfTreeLift 68 ⟨pfV68,252,253,254,255⟩ pfV252 pfV253 pfV254 pfV255 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase69 : pfCheckTree 69 = true := by
  apply pfTreeLift 69 ⟨pfV69,256,257,258,107⟩ pfV256 pfV257 pfV258 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase70 : pfCheckTree 70 = true := by
  apply pfTreeLift 70 ⟨pfV70,259,260,261,262⟩ pfV259 pfV260 pfV261 pfV262 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase71 : pfCheckTree 71 = true := by
  apply pfTreeLift 71 ⟨pfV71,263,264,265,83⟩ pfV263 pfV264 pfV265 pfV83 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase72 : pfCheckTree 72 = true := by
  apply pfTreeLift 72 ⟨pfV72,72,266,267,268⟩ pfV72 pfV266 pfV267 pfV268 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase73 : pfCheckTree 73 = true := by
  apply pfTreeLift 73 ⟨pfV73,269,270,271,137⟩ pfV269 pfV270 pfV271 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase74 : pfCheckTree 74 = true := by
  apply pfTreeLift 74 ⟨pfV74,272,273,274,79⟩ pfV272 pfV273 pfV274 pfV79 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase75 : pfCheckTree 75 = true := by
  apply pfTreeLift 75 ⟨pfV75,275,276,144,130⟩ pfV275 pfV276 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase76 : pfCheckTree 76 = true := by
  apply pfTreeLift 76 ⟨pfV76,76,277,278,79⟩ pfV76 pfV277 pfV278 pfV79 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase77 : pfCheckTree 77 = true := by
  apply pfTreeLift 77 ⟨pfV77,279,280,281,268⟩ pfV279 pfV280 pfV281 pfV268 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase78 : pfCheckTree 78 = true := by
  apply pfTreeLift 78 ⟨pfV78,282,283,284,285⟩ pfV282 pfV283 pfV284 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase79 : pfCheckTree 79 = true := by
  apply pfTreeLift 79 ⟨pfV79,286,107,144,130⟩ pfV286 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase80 : pfCheckTree 80 = true := by
  apply pfTreeLift 80 ⟨pfV80,80,287,288,83⟩ pfV80 pfV287 pfV288 pfV83 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase81 : pfCheckTree 81 = true := by
  apply pfTreeLift 81 ⟨pfV81,289,290,291,115⟩ pfV289 pfV290 pfV291 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase82 : pfCheckTree 82 = true := by
  apply pfTreeLift 82 ⟨pfV82,292,293,294,295⟩ pfV292 pfV293 pfV294 pfV295 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase83 : pfCheckTree 83 = true := by
  apply pfTreeLift 83 ⟨pfV83,296,107,144,130⟩ pfV296 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase84 : pfCheckTree 84 = true := by
  apply pfTreeLift 84 ⟨pfV84,84,85,297,87⟩ pfV84 pfV85 pfV297 pfV87 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase85 : pfCheckTree 85 = true := by
  apply pfTreeLift 85 ⟨pfV85,298,161,299,91⟩ pfV298 pfV161 pfV299 pfV91 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase86 : pfCheckTree 86 = true := by
  apply pfTreeLift 86 ⟨pfV86,300,301,229,302⟩ pfV300 pfV301 pfV229 pfV302 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase87 : pfCheckTree 87 = true := by
  apply pfTreeLift 87 ⟨pfV87,303,304,305,99⟩ pfV303 pfV304 pfV305 pfV99 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase88 : pfCheckTree 88 = true := by
  apply pfTreeLift 88 ⟨pfV88,88,161,306,91⟩ pfV88 pfV161 pfV306 pfV91 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase89 : pfCheckTree 89 = true := by
  apply pfTreeLift 89 ⟨pfV89,307,89,308,107⟩ pfV307 pfV89 pfV308 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase90 : pfCheckTree 90 = true := by
  apply pfTreeLift 90 ⟨pfV90,90,309,310,311⟩ pfV90 pfV309 pfV310 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase91 : pfCheckTree 91 = true := by
  apply pfTreeLift 91 ⟨pfV91,312,107,144,130⟩ pfV312 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase92 : pfCheckTree 92 = true := by
  apply pfTreeLift 92 ⟨pfV92,92,313,229,95⟩ pfV92 pfV313 pfV229 pfV95 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase93 : pfCheckTree 93 = true := by
  apply pfTreeLift 93 ⟨pfV93,93,314,315,316⟩ pfV93 pfV314 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase94 : pfCheckTree 94 = true := by
  apply pfTreeLift 94 ⟨pfV94,317,318,94,144⟩ pfV317 pfV318 pfV94 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase95 : pfCheckTree 95 = true := by
  apply pfTreeLift 95 ⟨pfV95,319,107,144,130⟩ pfV319 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup2 : pfTRange 64 32 :=
  (pfTJoin 64 16 16 (pfTJoin 64 8 8 (pfTJoin 64 4 4 (pfTJoin 64 2 2 (pfTJoin 64 1 1 (pfTOne 64 pfTCase64) (pfTOne 65 pfTCase65)) (pfTJoin 66 1 1 (pfTOne 66 pfTCase66) (pfTOne 67 pfTCase67))) (pfTJoin 68 2 2 (pfTJoin 68 1 1 (pfTOne 68 pfTCase68) (pfTOne 69 pfTCase69)) (pfTJoin 70 1 1 (pfTOne 70 pfTCase70) (pfTOne 71 pfTCase71)))) (pfTJoin 72 4 4 (pfTJoin 72 2 2 (pfTJoin 72 1 1 (pfTOne 72 pfTCase72) (pfTOne 73 pfTCase73)) (pfTJoin 74 1 1 (pfTOne 74 pfTCase74) (pfTOne 75 pfTCase75))) (pfTJoin 76 2 2 (pfTJoin 76 1 1 (pfTOne 76 pfTCase76) (pfTOne 77 pfTCase77)) (pfTJoin 78 1 1 (pfTOne 78 pfTCase78) (pfTOne 79 pfTCase79))))) (pfTJoin 80 8 8 (pfTJoin 80 4 4 (pfTJoin 80 2 2 (pfTJoin 80 1 1 (pfTOne 80 pfTCase80) (pfTOne 81 pfTCase81)) (pfTJoin 82 1 1 (pfTOne 82 pfTCase82) (pfTOne 83 pfTCase83))) (pfTJoin 84 2 2 (pfTJoin 84 1 1 (pfTOne 84 pfTCase84) (pfTOne 85 pfTCase85)) (pfTJoin 86 1 1 (pfTOne 86 pfTCase86) (pfTOne 87 pfTCase87)))) (pfTJoin 88 4 4 (pfTJoin 88 2 2 (pfTJoin 88 1 1 (pfTOne 88 pfTCase88) (pfTOne 89 pfTCase89)) (pfTJoin 90 1 1 (pfTOne 90 pfTCase90) (pfTOne 91 pfTCase91))) (pfTJoin 92 2 2 (pfTJoin 92 1 1 (pfTOne 92 pfTCase92) (pfTOne 93 pfTCase93)) (pfTJoin 94 1 1 (pfTOne 94 pfTCase94) (pfTOne 95 pfTCase95))))))
