import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase192 : pfCheckTree 192 = true := by
  apply pfTreeLift 192 ⟨pfV192,457,192,193,194⟩ pfV457 pfV192 pfV193 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase193 : pfCheckTree 193 = true := by
  apply pfTreeLift 193 ⟨pfV193,458,459,460,198⟩ pfV458 pfV459 pfV460 pfV198 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase194 : pfCheckTree 194 = true := by
  apply pfTreeLift 194 ⟨pfV194,461,107,144,130⟩ pfV461 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase195 : pfCheckTree 195 = true := by
  apply pfTreeLift 195 ⟨pfV195,195,462,455,198⟩ pfV195 pfV462 pfV455 pfV198 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase196 : pfCheckTree 196 = true := by
  apply pfTreeLift 196 ⟨pfV196,463,464,460,194⟩ pfV463 pfV464 pfV460 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase197 : pfCheckTree 197 = true := by
  apply pfTreeLift 197 ⟨pfV197,465,466,197,410⟩ pfV465 pfV466 pfV197 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase198 : pfCheckTree 198 = true := by
  apply pfTreeLift 198 ⟨pfV198,467,107,144,130⟩ pfV467 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase199 : pfCheckTree 199 = true := by
  apply pfTreeLift 199 ⟨pfV199,199,468,390,130⟩ pfV199 pfV468 pfV390 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase200 : pfCheckTree 200 = true := by
  apply pfTreeLift 200 ⟨pfV200,469,200,144,130⟩ pfV469 pfV200 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase201 : pfCheckTree 201 = true := by
  apply pfTreeLift 201 ⟨pfV201,201,202,470,204⟩ pfV201 pfV202 pfV470 pfV204 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase202 : pfCheckTree 202 = true := by
  apply pfTreeLift 202 ⟨pfV202,471,216,472,208⟩ pfV471 pfV216 pfV472 pfV208 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase203 : pfCheckTree 203 = true := by
  apply pfTreeLift 203 ⟨pfV203,473,474,229,475⟩ pfV473 pfV474 pfV229 pfV475 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase204 : pfCheckTree 204 = true := by
  apply pfTreeLift 204 ⟨pfV204,476,477,478,67⟩ pfV476 pfV477 pfV478 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase205 : pfCheckTree 205 = true := by
  apply pfTreeLift 205 ⟨pfV205,205,216,479,208⟩ pfV205 pfV216 pfV479 pfV208 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase206 : pfCheckTree 206 = true := by
  apply pfTreeLift 206 ⟨pfV206,480,206,481,107⟩ pfV480 pfV206 pfV481 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase207 : pfCheckTree 207 = true := by
  apply pfTreeLift 207 ⟨pfV207,207,482,483,484⟩ pfV207 pfV482 pfV483 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase208 : pfCheckTree 208 = true := by
  apply pfTreeLift 208 ⟨pfV208,485,107,144,130⟩ pfV485 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase209 : pfCheckTree 209 = true := by
  apply pfTreeLift 209 ⟨pfV209,209,486,229,212⟩ pfV209 pfV486 pfV229 pfV212 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase210 : pfCheckTree 210 = true := by
  apply pfTreeLift 210 ⟨pfV210,210,487,315,316⟩ pfV210 pfV487 pfV315 pfV316 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase211 : pfCheckTree 211 = true := by
  apply pfTreeLift 211 ⟨pfV211,317,488,211,144⟩ pfV317 pfV488 pfV211 pfV144 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase212 : pfCheckTree 212 = true := by
  apply pfTreeLift 212 ⟨pfV212,489,107,144,130⟩ pfV489 pfV107 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase213 : pfCheckTree 213 = true := by
  apply pfTreeLift 213 ⟨pfV213,213,490,491,67⟩ pfV213 pfV490 pfV491 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase214 : pfCheckTree 214 = true := by
  apply pfTreeLift 214 ⟨pfV214,492,214,493,194⟩ pfV492 pfV214 pfV493 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase215 : pfCheckTree 215 = true := by
  apply pfTreeLift 215 ⟨pfV215,494,477,495,410⟩ pfV494 pfV477 pfV495 pfV410 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase216 : pfCheckTree 216 = true := by
  apply pfTreeLift 216 ⟨pfV216,480,216,496,107⟩ pfV480 pfV216 pfV496 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase217 : pfCheckTree 217 = true := by
  apply pfTreeLift 217 ⟨pfV217,217,497,498,484⟩ pfV217 pfV497 pfV498 pfV484 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase218 : pfCheckTree 218 = true := by
  apply pfTreeLift 218 ⟨pfV218,499,240,188,130⟩ pfV499 pfV240 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase219 : pfCheckTree 219 = true := by
  apply pfTreeLift 219 ⟨pfV219,219,216,500,167⟩ pfV219 pfV216 pfV500 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase220 : pfCheckTree 220 = true := by
  apply pfTreeLift 220 ⟨pfV220,501,220,221,167⟩ pfV501 pfV220 pfV221 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase221 : pfCheckTree 221 = true := by
  apply pfTreeLift 221 ⟨pfV221,502,503,504,225⟩ pfV502 pfV503 pfV504 pfV225 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase222 : pfCheckTree 222 = true := by
  apply pfTreeLift 222 ⟨pfV222,222,505,498,225⟩ pfV222 pfV505 pfV498 pfV225 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase223 : pfCheckTree 223 = true := by
  apply pfTreeLift 223 ⟨pfV223,506,507,508,167⟩ pfV506 pfV507 pfV508 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup6 : pfTRange 192 32 :=
  (pfTJoin 192 16 16 (pfTJoin 192 8 8 (pfTJoin 192 4 4 (pfTJoin 192 2 2 (pfTJoin 192 1 1 (pfTOne 192 pfTCase192) (pfTOne 193 pfTCase193)) (pfTJoin 194 1 1 (pfTOne 194 pfTCase194) (pfTOne 195 pfTCase195))) (pfTJoin 196 2 2 (pfTJoin 196 1 1 (pfTOne 196 pfTCase196) (pfTOne 197 pfTCase197)) (pfTJoin 198 1 1 (pfTOne 198 pfTCase198) (pfTOne 199 pfTCase199)))) (pfTJoin 200 4 4 (pfTJoin 200 2 2 (pfTJoin 200 1 1 (pfTOne 200 pfTCase200) (pfTOne 201 pfTCase201)) (pfTJoin 202 1 1 (pfTOne 202 pfTCase202) (pfTOne 203 pfTCase203))) (pfTJoin 204 2 2 (pfTJoin 204 1 1 (pfTOne 204 pfTCase204) (pfTOne 205 pfTCase205)) (pfTJoin 206 1 1 (pfTOne 206 pfTCase206) (pfTOne 207 pfTCase207))))) (pfTJoin 208 8 8 (pfTJoin 208 4 4 (pfTJoin 208 2 2 (pfTJoin 208 1 1 (pfTOne 208 pfTCase208) (pfTOne 209 pfTCase209)) (pfTJoin 210 1 1 (pfTOne 210 pfTCase210) (pfTOne 211 pfTCase211))) (pfTJoin 212 2 2 (pfTJoin 212 1 1 (pfTOne 212 pfTCase212) (pfTOne 213 pfTCase213)) (pfTJoin 214 1 1 (pfTOne 214 pfTCase214) (pfTOne 215 pfTCase215)))) (pfTJoin 216 4 4 (pfTJoin 216 2 2 (pfTJoin 216 1 1 (pfTOne 216 pfTCase216) (pfTOne 217 pfTCase217)) (pfTJoin 218 1 1 (pfTOne 218 pfTCase218) (pfTOne 219 pfTCase219))) (pfTJoin 220 2 2 (pfTJoin 220 1 1 (pfTOne 220 pfTCase220) (pfTOne 221 pfTCase221)) (pfTJoin 222 1 1 (pfTOne 222 pfTCase222) (pfTOne 223 pfTCase223))))))
