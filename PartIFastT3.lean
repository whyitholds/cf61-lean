import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase96 : pfCheckTree 96 = true := by
  apply pfTreeLift 96 ⟨pfV96,96,320,321,99⟩ pfV96 pfV320 pfV321 pfV99 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase97 : pfCheckTree 97 = true := by
  apply pfTreeLift 97 ⟨pfV97,322,97,323,137⟩ pfV322 pfV97 pfV323 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase98 : pfCheckTree 98 = true := by
  apply pfTreeLift 98 ⟨pfV98,324,304,325,285⟩ pfV324 pfV304 pfV325 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase99 : pfCheckTree 99 = true := by
  apply pfTreeLift 99 ⟨pfV99,326,107,144,130⟩ pfV326 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase100 : pfCheckTree 100 = true := by
  apply pfTreeLift 100 ⟨pfV100,100,101,327,103⟩ pfV100 pfV101 pfV327 pfV103 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase101 : pfCheckTree 101 = true := by
  apply pfTreeLift 101 ⟨pfV101,307,161,328,107⟩ pfV307 pfV161 pfV328 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase102 : pfCheckTree 102 = true := by
  apply pfTreeLift 102 ⟨pfV102,102,329,330,331⟩ pfV102 pfV329 pfV330 pfV331 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase103 : pfCheckTree 103 = true := by
  apply pfTreeLift 103 ⟨pfV103,332,333,334,115⟩ pfV332 pfV333 pfV334 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase104 : pfCheckTree 104 = true := by
  apply pfTreeLift 104 ⟨pfV104,104,161,335,107⟩ pfV104 pfV161 pfV335 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase105 : pfCheckTree 105 = true := by
  apply pfTreeLift 105 ⟨pfV105,307,105,106,107⟩ pfV307 pfV105 pfV106 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase106 : pfCheckTree 106 = true := by
  apply pfTreeLift 106 ⟨pfV106,106,309,336,111⟩ pfV106 pfV309 pfV336 pfV111 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase107 : pfCheckTree 107 = true := by
  apply pfTreeLift 107 ⟨pfV107,337,107,144,130⟩ pfV337 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase108 : pfCheckTree 108 = true := by
  apply pfTreeLift 108 ⟨pfV108,108,338,330,111⟩ pfV108 pfV338 pfV330 pfV111 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase109 : pfCheckTree 109 = true := by
  apply pfTreeLift 109 ⟨pfV109,109,338,339,107⟩ pfV109 pfV338 pfV339 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase110 : pfCheckTree 110 = true := by
  apply pfTreeLift 110 ⟨pfV110,330,340,110,144⟩ pfV330 pfV340 pfV110 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase111 : pfCheckTree 111 = true := by
  apply pfTreeLift 111 ⟨pfV111,341,107,144,130⟩ pfV341 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase112 : pfCheckTree 112 = true := by
  apply pfTreeLift 112 ⟨pfV112,112,342,343,115⟩ pfV112 pfV342 pfV343 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase113 : pfCheckTree 113 = true := by
  apply pfTreeLift 113 ⟨pfV113,344,113,114,115⟩ pfV344 pfV113 pfV114 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase114 : pfCheckTree 114 = true := by
  apply pfTreeLift 114 ⟨pfV114,345,333,334,346⟩ pfV345 pfV333 pfV334 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase115 : pfCheckTree 115 = true := by
  apply pfTreeLift 115 ⟨pfV115,347,107,144,130⟩ pfV347 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase116 : pfCheckTree 116 = true := by
  apply pfTreeLift 116 ⟨pfV116,348,349,350,351⟩ pfV348 pfV349 pfV350 pfV351 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase117 : pfCheckTree 117 = true := by
  apply pfTreeLift 117 ⟨pfV117,352,353,229,126⟩ pfV352 pfV353 pfV229 pfV126 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase118 : pfCheckTree 118 = true := by
  apply pfTreeLift 118 ⟨pfV118,354,333,334,130⟩ pfV354 pfV333 pfV334 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase119 : pfCheckTree 119 = true := by
  apply pfTreeLift 119 ⟨pfV119,119,349,355,122⟩ pfV119 pfV349 pfV355 pfV122 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase120 : pfCheckTree 120 = true := by
  apply pfTreeLift 120 ⟨pfV120,356,120,357,107⟩ pfV356 pfV120 pfV357 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase121 : pfCheckTree 121 = true := by
  apply pfTreeLift 121 ⟨pfV121,121,358,359,360⟩ pfV121 pfV358 pfV359 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase122 : pfCheckTree 122 = true := by
  apply pfTreeLift 122 ⟨pfV122,361,107,144,130⟩ pfV361 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase123 : pfCheckTree 123 = true := by
  apply pfTreeLift 123 ⟨pfV123,123,362,229,126⟩ pfV123 pfV362 pfV229 pfV126 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase124 : pfCheckTree 124 = true := by
  apply pfTreeLift 124 ⟨pfV124,124,363,315,364⟩ pfV124 pfV363 pfV315 pfV364 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase125 : pfCheckTree 125 = true := by
  apply pfTreeLift 125 ⟨pfV125,317,365,125,144⟩ pfV317 pfV365 pfV125 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase126 : pfCheckTree 126 = true := by
  apply pfTreeLift 126 ⟨pfV126,366,107,144,130⟩ pfV366 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase127 : pfCheckTree 127 = true := by
  apply pfTreeLift 127 ⟨pfV127,127,367,368,130⟩ pfV127 pfV367 pfV368 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup3 : pfTRange 96 32 :=
  (pfTJoin 96 16 16 (pfTJoin 96 8 8 (pfTJoin 96 4 4 (pfTJoin 96 2 2 (pfTJoin 96 1 1 (pfTOne 96 pfTCase96) (pfTOne 97 pfTCase97)) (pfTJoin 98 1 1 (pfTOne 98 pfTCase98) (pfTOne 99 pfTCase99))) (pfTJoin 100 2 2 (pfTJoin 100 1 1 (pfTOne 100 pfTCase100) (pfTOne 101 pfTCase101)) (pfTJoin 102 1 1 (pfTOne 102 pfTCase102) (pfTOne 103 pfTCase103)))) (pfTJoin 104 4 4 (pfTJoin 104 2 2 (pfTJoin 104 1 1 (pfTOne 104 pfTCase104) (pfTOne 105 pfTCase105)) (pfTJoin 106 1 1 (pfTOne 106 pfTCase106) (pfTOne 107 pfTCase107))) (pfTJoin 108 2 2 (pfTJoin 108 1 1 (pfTOne 108 pfTCase108) (pfTOne 109 pfTCase109)) (pfTJoin 110 1 1 (pfTOne 110 pfTCase110) (pfTOne 111 pfTCase111))))) (pfTJoin 112 8 8 (pfTJoin 112 4 4 (pfTJoin 112 2 2 (pfTJoin 112 1 1 (pfTOne 112 pfTCase112) (pfTOne 113 pfTCase113)) (pfTJoin 114 1 1 (pfTOne 114 pfTCase114) (pfTOne 115 pfTCase115))) (pfTJoin 116 2 2 (pfTJoin 116 1 1 (pfTOne 116 pfTCase116) (pfTOne 117 pfTCase117)) (pfTJoin 118 1 1 (pfTOne 118 pfTCase118) (pfTOne 119 pfTCase119)))) (pfTJoin 120 4 4 (pfTJoin 120 2 2 (pfTJoin 120 1 1 (pfTOne 120 pfTCase120) (pfTOne 121 pfTCase121)) (pfTJoin 122 1 1 (pfTOne 122 pfTCase122) (pfTOne 123 pfTCase123))) (pfTJoin 124 2 2 (pfTJoin 124 1 1 (pfTOne 124 pfTCase124) (pfTOne 125 pfTCase125)) (pfTJoin 126 1 1 (pfTOne 126 pfTCase126) (pfTOne 127 pfTCase127))))))
