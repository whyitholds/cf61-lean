import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase288 : pfCheckTree 288 = true := by
  apply pfTreeLift 288 ⟨pfV288,288,586,288,144⟩ pfV288 pfV586 pfV288 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase289 : pfCheckTree 289 = true := by
  apply pfTreeLift 289 ⟨pfV289,289,287,562,115⟩ pfV289 pfV287 pfV562 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase290 : pfCheckTree 290 = true := by
  apply pfTreeLift 290 ⟨pfV290,587,290,291,115⟩ pfV587 pfV290 pfV291 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase291 : pfCheckTree 291 = true := by
  apply pfTreeLift 291 ⟨pfV291,588,551,552,295⟩ pfV588 pfV551 pfV552 pfV295 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase292 : pfCheckTree 292 = true := by
  apply pfTreeLift 292 ⟨pfV292,292,586,288,295⟩ pfV292 pfV586 pfV288 pfV295 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase293 : pfCheckTree 293 = true := by
  apply pfTreeLift 293 ⟨pfV293,589,551,552,115⟩ pfV589 pfV551 pfV552 pfV115 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase294 : pfCheckTree 294 = true := by
  apply pfTreeLift 294 ⟨pfV294,590,293,294,346⟩ pfV590 pfV293 pfV294 pfV346 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase295 : pfCheckTree 295 = true := by
  apply pfTreeLift 295 ⟨pfV295,591,107,144,130⟩ pfV591 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase296 : pfCheckTree 296 = true := by
  apply pfTreeLift 296 ⟨pfV296,296,544,390,130⟩ pfV296 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase297 : pfCheckTree 297 = true := by
  apply pfTreeLift 297 ⟨pfV297,592,301,229,302⟩ pfV592 pfV301 pfV229 pfV302 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase298 : pfCheckTree 298 = true := by
  apply pfTreeLift 298 ⟨pfV298,298,161,335,91⟩ pfV298 pfV161 pfV335 pfV91 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase299 : pfCheckTree 299 = true := by
  apply pfTreeLift 299 ⟨pfV299,299,309,336,311⟩ pfV299 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase300 : pfCheckTree 300 = true := by
  apply pfTreeLift 300 ⟨pfV300,300,525,229,302⟩ pfV300 pfV525 pfV229 pfV302 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase301 : pfCheckTree 301 = true := by
  apply pfTreeLift 301 ⟨pfV301,301,593,315,316⟩ pfV301 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase302 : pfCheckTree 302 = true := by
  apply pfTreeLift 302 ⟨pfV302,594,107,144,130⟩ pfV594 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase303 : pfCheckTree 303 = true := by
  apply pfTreeLift 303 ⟨pfV303,303,595,596,99⟩ pfV303 pfV595 pfV596 pfV99 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase304 : pfCheckTree 304 = true := by
  apply pfTreeLift 304 ⟨pfV304,597,304,305,137⟩ pfV597 pfV304 pfV305 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase305 : pfCheckTree 305 = true := by
  apply pfTreeLift 305 ⟨pfV305,598,304,305,285⟩ pfV598 pfV304 pfV305 pfV285 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase306 : pfCheckTree 306 = true := by
  apply pfTreeLift 306 ⟨pfV306,306,309,310,311⟩ pfV306 pfV309 pfV310 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase307 : pfCheckTree 307 = true := by
  apply pfTreeLift 307 ⟨pfV307,307,161,335,107⟩ pfV307 pfV161 pfV335 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase308 : pfCheckTree 308 = true := by
  apply pfTreeLift 308 ⟨pfV308,308,309,336,311⟩ pfV308 pfV309 pfV336 pfV311 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase309 : pfCheckTree 309 = true := by
  apply pfTreeLift 309 ⟨pfV309,309,309,336,107⟩ pfV309 pfV309 pfV336 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase310 : pfCheckTree 310 = true := by
  apply pfTreeLift 310 ⟨pfV310,310,309,310,144⟩ pfV310 pfV309 pfV310 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase311 : pfCheckTree 311 = true := by
  apply pfTreeLift 311 ⟨pfV311,599,107,144,130⟩ pfV599 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase312 : pfCheckTree 312 = true := by
  apply pfTreeLift 312 ⟨pfV312,312,544,390,130⟩ pfV312 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase313 : pfCheckTree 313 = true := by
  apply pfTreeLift 313 ⟨pfV313,313,314,315,316⟩ pfV313 pfV314 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase314 : pfCheckTree 314 = true := by
  apply pfTreeLift 314 ⟨pfV314,314,314,315,107⟩ pfV314 pfV314 pfV315 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase315 : pfCheckTree 315 = true := by
  apply pfTreeLift 315 ⟨pfV315,315,593,315,144⟩ pfV315 pfV593 pfV315 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase316 : pfCheckTree 316 = true := by
  apply pfTreeLift 316 ⟨pfV316,600,107,144,130⟩ pfV600 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase317 : pfCheckTree 317 = true := by
  apply pfTreeLift 317 ⟨pfV317,317,525,229,144⟩ pfV317 pfV525 pfV229 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase318 : pfCheckTree 318 = true := by
  apply pfTreeLift 318 ⟨pfV318,318,593,315,316⟩ pfV318 pfV593 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase319 : pfCheckTree 319 = true := by
  apply pfTreeLift 319 ⟨pfV319,319,544,390,130⟩ pfV319 pfV544 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup9 : pfTRange 288 32 :=
  (pfTJoin 288 16 16 (pfTJoin 288 8 8 (pfTJoin 288 4 4 (pfTJoin 288 2 2 (pfTJoin 288 1 1 (pfTOne 288 pfTCase288) (pfTOne 289 pfTCase289)) (pfTJoin 290 1 1 (pfTOne 290 pfTCase290) (pfTOne 291 pfTCase291))) (pfTJoin 292 2 2 (pfTJoin 292 1 1 (pfTOne 292 pfTCase292) (pfTOne 293 pfTCase293)) (pfTJoin 294 1 1 (pfTOne 294 pfTCase294) (pfTOne 295 pfTCase295)))) (pfTJoin 296 4 4 (pfTJoin 296 2 2 (pfTJoin 296 1 1 (pfTOne 296 pfTCase296) (pfTOne 297 pfTCase297)) (pfTJoin 298 1 1 (pfTOne 298 pfTCase298) (pfTOne 299 pfTCase299))) (pfTJoin 300 2 2 (pfTJoin 300 1 1 (pfTOne 300 pfTCase300) (pfTOne 301 pfTCase301)) (pfTJoin 302 1 1 (pfTOne 302 pfTCase302) (pfTOne 303 pfTCase303))))) (pfTJoin 304 8 8 (pfTJoin 304 4 4 (pfTJoin 304 2 2 (pfTJoin 304 1 1 (pfTOne 304 pfTCase304) (pfTOne 305 pfTCase305)) (pfTJoin 306 1 1 (pfTOne 306 pfTCase306) (pfTOne 307 pfTCase307))) (pfTJoin 308 2 2 (pfTJoin 308 1 1 (pfTOne 308 pfTCase308) (pfTOne 309 pfTCase309)) (pfTJoin 310 1 1 (pfTOne 310 pfTCase310) (pfTOne 311 pfTCase311)))) (pfTJoin 312 4 4 (pfTJoin 312 2 2 (pfTJoin 312 1 1 (pfTOne 312 pfTCase312) (pfTOne 313 pfTCase313)) (pfTJoin 314 1 1 (pfTOne 314 pfTCase314) (pfTOne 315 pfTCase315))) (pfTJoin 316 2 2 (pfTJoin 316 1 1 (pfTOne 316 pfTCase316) (pfTOne 317 pfTCase317)) (pfTJoin 318 1 1 (pfTOne 318 pfTCase318) (pfTOne 319 pfTCase319))))))
