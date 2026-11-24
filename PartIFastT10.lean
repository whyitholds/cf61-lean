import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase320 : pfCheckTree 320 = true := by
  apply pfTreeLift 320 ⟨pfV320,320,320,596,107⟩ pfV320 pfV320 pfV596 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase321 : pfCheckTree 321 = true := by
  apply pfTreeLift 321 ⟨pfV321,321,595,321,144⟩ pfV321 pfV595 pfV321 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase322 : pfCheckTree 322 = true := by
  apply pfTreeLift 322 ⟨pfV322,322,320,596,137⟩ pfV322 pfV320 pfV596 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase323 : pfCheckTree 323 = true := by
  apply pfTreeLift 323 ⟨pfV323,601,304,305,285⟩ pfV601 pfV304 pfV305 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase324 : pfCheckTree 324 = true := by
  apply pfTreeLift 324 ⟨pfV324,324,595,321,285⟩ pfV324 pfV595 pfV321 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase325 : pfCheckTree 325 = true := by
  apply pfTreeLift 325 ⟨pfV325,602,304,325,285⟩ pfV602 pfV304 pfV325 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase326 : pfCheckTree 326 = true := by
  apply pfTreeLift 326 ⟨pfV326,326,544,390,130⟩ pfV326 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase327 : pfCheckTree 327 = true := by
  apply pfTreeLift 327 ⟨pfV327,327,329,330,331⟩ pfV327 pfV329 pfV330 pfV331 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase328 : pfCheckTree 328 = true := by
  apply pfTreeLift 328 ⟨pfV328,328,309,336,311⟩ pfV328 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase329 : pfCheckTree 329 = true := by
  apply pfTreeLift 329 ⟨pfV329,329,329,339,107⟩ pfV329 pfV329 pfV339 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase330 : pfCheckTree 330 = true := by
  apply pfTreeLift 330 ⟨pfV330,330,329,330,144⟩ pfV330 pfV329 pfV330 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase331 : pfCheckTree 331 = true := by
  apply pfTreeLift 331 ⟨pfV331,603,107,144,130⟩ pfV603 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase332 : pfCheckTree 332 = true := by
  apply pfTreeLift 332 ⟨pfV332,332,604,343,115⟩ pfV332 pfV604 pfV343 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase333 : pfCheckTree 333 = true := by
  apply pfTreeLift 333 ⟨pfV333,605,333,334,115⟩ pfV605 pfV333 pfV334 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase334 : pfCheckTree 334 = true := by
  apply pfTreeLift 334 ⟨pfV334,606,333,334,346⟩ pfV606 pfV333 pfV334 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase335 : pfCheckTree 335 = true := by
  apply pfTreeLift 335 ⟨pfV335,335,309,336,311⟩ pfV335 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase336 : pfCheckTree 336 = true := by
  apply pfTreeLift 336 ⟨pfV336,336,309,336,144⟩ pfV336 pfV309 pfV336 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase337 : pfCheckTree 337 = true := by
  apply pfTreeLift 337 ⟨pfV337,337,544,390,130⟩ pfV337 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase338 : pfCheckTree 338 = true := by
  apply pfTreeLift 338 ⟨pfV338,338,338,339,107⟩ pfV338 pfV338 pfV339 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase339 : pfCheckTree 339 = true := by
  apply pfTreeLift 339 ⟨pfV339,339,329,339,144⟩ pfV339 pfV329 pfV339 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase340 : pfCheckTree 340 = true := by
  apply pfTreeLift 340 ⟨pfV340,340,329,339,107⟩ pfV340 pfV329 pfV339 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase341 : pfCheckTree 341 = true := by
  apply pfTreeLift 341 ⟨pfV341,341,544,390,130⟩ pfV341 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase342 : pfCheckTree 342 = true := by
  apply pfTreeLift 342 ⟨pfV342,342,342,343,107⟩ pfV342 pfV342 pfV343 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase343 : pfCheckTree 343 = true := by
  apply pfTreeLift 343 ⟨pfV343,343,604,343,144⟩ pfV343 pfV604 pfV343 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase344 : pfCheckTree 344 = true := by
  apply pfTreeLift 344 ⟨pfV344,344,342,343,115⟩ pfV344 pfV342 pfV343 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase345 : pfCheckTree 345 = true := by
  apply pfTreeLift 345 ⟨pfV345,345,604,343,346⟩ pfV345 pfV604 pfV343 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase346 : pfCheckTree 346 = true := by
  apply pfTreeLift 346 ⟨pfV346,607,107,144,130⟩ pfV607 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase347 : pfCheckTree 347 = true := by
  apply pfTreeLift 347 ⟨pfV347,347,544,390,130⟩ pfV347 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase348 : pfCheckTree 348 = true := by
  apply pfTreeLift 348 ⟨pfV348,348,349,608,351⟩ pfV348 pfV349 pfV608 pfV351 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase349 : pfCheckTree 349 = true := by
  apply pfTreeLift 349 ⟨pfV349,356,349,609,107⟩ pfV356 pfV349 pfV609 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase350 : pfCheckTree 350 = true := by
  apply pfTreeLift 350 ⟨pfV350,350,358,610,360⟩ pfV350 pfV358 pfV610 pfV360 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase351 : pfCheckTree 351 = true := by
  apply pfTreeLift 351 ⟨pfV351,611,107,144,130⟩ pfV611 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup10 : pfTRange 320 32 :=
  (pfTJoin 320 16 16 (pfTJoin 320 8 8 (pfTJoin 320 4 4 (pfTJoin 320 2 2 (pfTJoin 320 1 1 (pfTOne 320 pfTCase320) (pfTOne 321 pfTCase321)) (pfTJoin 322 1 1 (pfTOne 322 pfTCase322) (pfTOne 323 pfTCase323))) (pfTJoin 324 2 2 (pfTJoin 324 1 1 (pfTOne 324 pfTCase324) (pfTOne 325 pfTCase325)) (pfTJoin 326 1 1 (pfTOne 326 pfTCase326) (pfTOne 327 pfTCase327)))) (pfTJoin 328 4 4 (pfTJoin 328 2 2 (pfTJoin 328 1 1 (pfTOne 328 pfTCase328) (pfTOne 329 pfTCase329)) (pfTJoin 330 1 1 (pfTOne 330 pfTCase330) (pfTOne 331 pfTCase331))) (pfTJoin 332 2 2 (pfTJoin 332 1 1 (pfTOne 332 pfTCase332) (pfTOne 333 pfTCase333)) (pfTJoin 334 1 1 (pfTOne 334 pfTCase334) (pfTOne 335 pfTCase335))))) (pfTJoin 336 8 8 (pfTJoin 336 4 4 (pfTJoin 336 2 2 (pfTJoin 336 1 1 (pfTOne 336 pfTCase336) (pfTOne 337 pfTCase337)) (pfTJoin 338 1 1 (pfTOne 338 pfTCase338) (pfTOne 339 pfTCase339))) (pfTJoin 340 2 2 (pfTJoin 340 1 1 (pfTOne 340 pfTCase340) (pfTOne 341 pfTCase341)) (pfTJoin 342 1 1 (pfTOne 342 pfTCase342) (pfTOne 343 pfTCase343)))) (pfTJoin 344 4 4 (pfTJoin 344 2 2 (pfTJoin 344 1 1 (pfTOne 344 pfTCase344) (pfTOne 345 pfTCase345)) (pfTJoin 346 1 1 (pfTOne 346 pfTCase346) (pfTOne 347 pfTCase347))) (pfTJoin 348 2 2 (pfTJoin 348 1 1 (pfTOne 348 pfTCase348) (pfTOne 349 pfTCase349)) (pfTJoin 350 1 1 (pfTOne 350 pfTCase350) (pfTOne 351 pfTCase351))))))
