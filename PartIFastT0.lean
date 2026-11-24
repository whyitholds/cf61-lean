import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase0 : pfCheckTree 0 = true := by
  apply pfTreeLift 0 ⟨pfV0,4,5,6,7⟩ pfV4 pfV5 pfV6 pfV7 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase1 : pfCheckTree 1 = true := by
  apply pfTreeLift 1 ⟨pfV1,8,9,10,11⟩ pfV8 pfV9 pfV10 pfV11 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase2 : pfCheckTree 2 = true := by
  apply pfTreeLift 2 ⟨pfV2,12,13,14,15⟩ pfV12 pfV13 pfV14 pfV15 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase3 : pfCheckTree 3 = true := by
  apply pfTreeLift 3 ⟨pfV3,16,17,18,19⟩ pfV16 pfV17 pfV18 pfV19 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase4 : pfCheckTree 4 = true := by
  apply pfTreeLift 4 ⟨pfV4,20,21,22,23⟩ pfV20 pfV21 pfV22 pfV23 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase5 : pfCheckTree 5 = true := by
  apply pfTreeLift 5 ⟨pfV5,24,25,26,27⟩ pfV24 pfV25 pfV26 pfV27 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase6 : pfCheckTree 6 = true := by
  apply pfTreeLift 6 ⟨pfV6,28,29,30,31⟩ pfV28 pfV29 pfV30 pfV31 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase7 : pfCheckTree 7 = true := by
  apply pfTreeLift 7 ⟨pfV7,32,33,34,35⟩ pfV32 pfV33 pfV34 pfV35 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase8 : pfCheckTree 8 = true := by
  apply pfTreeLift 8 ⟨pfV8,36,37,38,39⟩ pfV36 pfV37 pfV38 pfV39 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase9 : pfCheckTree 9 = true := by
  apply pfTreeLift 9 ⟨pfV9,40,41,42,43⟩ pfV40 pfV41 pfV42 pfV43 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase10 : pfCheckTree 10 = true := by
  apply pfTreeLift 10 ⟨pfV10,44,45,46,47⟩ pfV44 pfV45 pfV46 pfV47 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase11 : pfCheckTree 11 = true := by
  apply pfTreeLift 11 ⟨pfV11,48,49,50,51⟩ pfV48 pfV49 pfV50 pfV51 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase12 : pfCheckTree 12 = true := by
  apply pfTreeLift 12 ⟨pfV12,52,53,54,55⟩ pfV52 pfV53 pfV54 pfV55 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase13 : pfCheckTree 13 = true := by
  apply pfTreeLift 13 ⟨pfV13,56,57,58,59⟩ pfV56 pfV57 pfV58 pfV59 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase14 : pfCheckTree 14 = true := by
  apply pfTreeLift 14 ⟨pfV14,60,61,62,63⟩ pfV60 pfV61 pfV62 pfV63 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase15 : pfCheckTree 15 = true := by
  apply pfTreeLift 15 ⟨pfV15,64,65,66,67⟩ pfV64 pfV65 pfV66 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase16 : pfCheckTree 16 = true := by
  apply pfTreeLift 16 ⟨pfV16,68,69,70,71⟩ pfV68 pfV69 pfV70 pfV71 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase17 : pfCheckTree 17 = true := by
  apply pfTreeLift 17 ⟨pfV17,72,73,74,75⟩ pfV72 pfV73 pfV74 pfV75 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase18 : pfCheckTree 18 = true := by
  apply pfTreeLift 18 ⟨pfV18,76,77,78,79⟩ pfV76 pfV77 pfV78 pfV79 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase19 : pfCheckTree 19 = true := by
  apply pfTreeLift 19 ⟨pfV19,80,81,82,83⟩ pfV80 pfV81 pfV82 pfV83 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase20 : pfCheckTree 20 = true := by
  apply pfTreeLift 20 ⟨pfV20,84,85,86,87⟩ pfV84 pfV85 pfV86 pfV87 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase21 : pfCheckTree 21 = true := by
  apply pfTreeLift 21 ⟨pfV21,88,89,90,91⟩ pfV88 pfV89 pfV90 pfV91 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase22 : pfCheckTree 22 = true := by
  apply pfTreeLift 22 ⟨pfV22,92,93,94,95⟩ pfV92 pfV93 pfV94 pfV95 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase23 : pfCheckTree 23 = true := by
  apply pfTreeLift 23 ⟨pfV23,96,97,98,99⟩ pfV96 pfV97 pfV98 pfV99 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase24 : pfCheckTree 24 = true := by
  apply pfTreeLift 24 ⟨pfV24,100,101,102,103⟩ pfV100 pfV101 pfV102 pfV103 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase25 : pfCheckTree 25 = true := by
  apply pfTreeLift 25 ⟨pfV25,104,105,106,107⟩ pfV104 pfV105 pfV106 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase26 : pfCheckTree 26 = true := by
  apply pfTreeLift 26 ⟨pfV26,108,109,110,111⟩ pfV108 pfV109 pfV110 pfV111 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase27 : pfCheckTree 27 = true := by
  apply pfTreeLift 27 ⟨pfV27,112,113,114,115⟩ pfV112 pfV113 pfV114 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase28 : pfCheckTree 28 = true := by
  apply pfTreeLift 28 ⟨pfV28,28,116,117,118⟩ pfV28 pfV116 pfV117 pfV118 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase29 : pfCheckTree 29 = true := by
  apply pfTreeLift 29 ⟨pfV29,119,120,121,122⟩ pfV119 pfV120 pfV121 pfV122 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase30 : pfCheckTree 30 = true := by
  apply pfTreeLift 30 ⟨pfV30,123,124,125,126⟩ pfV123 pfV124 pfV125 pfV126 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase31 : pfCheckTree 31 = true := by
  apply pfTreeLift 31 ⟨pfV31,127,128,129,130⟩ pfV127 pfV128 pfV129 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup0 : pfTRange 0 32 :=
  (pfTJoin 0 16 16 (pfTJoin 0 8 8 (pfTJoin 0 4 4 (pfTJoin 0 2 2 (pfTJoin 0 1 1 (pfTOne 0 pfTCase0) (pfTOne 1 pfTCase1)) (pfTJoin 2 1 1 (pfTOne 2 pfTCase2) (pfTOne 3 pfTCase3))) (pfTJoin 4 2 2 (pfTJoin 4 1 1 (pfTOne 4 pfTCase4) (pfTOne 5 pfTCase5)) (pfTJoin 6 1 1 (pfTOne 6 pfTCase6) (pfTOne 7 pfTCase7)))) (pfTJoin 8 4 4 (pfTJoin 8 2 2 (pfTJoin 8 1 1 (pfTOne 8 pfTCase8) (pfTOne 9 pfTCase9)) (pfTJoin 10 1 1 (pfTOne 10 pfTCase10) (pfTOne 11 pfTCase11))) (pfTJoin 12 2 2 (pfTJoin 12 1 1 (pfTOne 12 pfTCase12) (pfTOne 13 pfTCase13)) (pfTJoin 14 1 1 (pfTOne 14 pfTCase14) (pfTOne 15 pfTCase15))))) (pfTJoin 16 8 8 (pfTJoin 16 4 4 (pfTJoin 16 2 2 (pfTJoin 16 1 1 (pfTOne 16 pfTCase16) (pfTOne 17 pfTCase17)) (pfTJoin 18 1 1 (pfTOne 18 pfTCase18) (pfTOne 19 pfTCase19))) (pfTJoin 20 2 2 (pfTJoin 20 1 1 (pfTOne 20 pfTCase20) (pfTOne 21 pfTCase21)) (pfTJoin 22 1 1 (pfTOne 22 pfTCase22) (pfTOne 23 pfTCase23)))) (pfTJoin 24 4 4 (pfTJoin 24 2 2 (pfTJoin 24 1 1 (pfTOne 24 pfTCase24) (pfTOne 25 pfTCase25)) (pfTJoin 26 1 1 (pfTOne 26 pfTCase26) (pfTOne 27 pfTCase27))) (pfTJoin 28 2 2 (pfTJoin 28 1 1 (pfTOne 28 pfTCase28) (pfTOne 29 pfTCase29)) (pfTJoin 30 1 1 (pfTOne 30 pfTCase30) (pfTOne 31 pfTCase31))))))
