import PartIFastTreePass
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pfTCase32 : pfCheckTree 32 = true := by
  apply pfTreeLift 32 ⟨pfV32,32,131,132,133⟩ pfV32 pfV131 pfV132 pfV133 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase33 : pfCheckTree 33 = true := by
  apply pfTreeLift 33 ⟨pfV33,134,135,136,137⟩ pfV134 pfV135 pfV136 pfV137 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase34 : pfCheckTree 34 = true := by
  apply pfTreeLift 34 ⟨pfV34,138,139,140,141⟩ pfV138 pfV139 pfV140 pfV141 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase35 : pfCheckTree 35 = true := by
  apply pfTreeLift 35 ⟨pfV35,142,143,144,130⟩ pfV142 pfV143 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase36 : pfCheckTree 36 = true := by
  apply pfTreeLift 36 ⟨pfV36,145,146,147,148⟩ pfV145 pfV146 pfV147 pfV148 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase37 : pfCheckTree 37 = true := by
  apply pfTreeLift 37 ⟨pfV37,149,150,151,107⟩ pfV149 pfV150 pfV151 pfV107 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase38 : pfCheckTree 38 = true := by
  apply pfTreeLift 38 ⟨pfV38,152,153,154,155⟩ pfV152 pfV153 pfV154 pfV155 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase39 : pfCheckTree 39 = true := by
  apply pfTreeLift 39 ⟨pfV39,156,157,158,159⟩ pfV156 pfV157 pfV158 pfV159 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase40 : pfCheckTree 40 = true := by
  apply pfTreeLift 40 ⟨pfV40,160,161,162,163⟩ pfV160 pfV161 pfV162 pfV163 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase41 : pfCheckTree 41 = true := by
  apply pfTreeLift 41 ⟨pfV41,164,165,166,167⟩ pfV164 pfV165 pfV166 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase42 : pfCheckTree 42 = true := by
  apply pfTreeLift 42 ⟨pfV42,168,169,170,171⟩ pfV168 pfV169 pfV170 pfV171 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase43 : pfCheckTree 43 = true := by
  apply pfTreeLift 43 ⟨pfV43,172,173,174,130⟩ pfV172 pfV173 pfV174 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase44 : pfCheckTree 44 = true := by
  apply pfTreeLift 44 ⟨pfV44,44,175,176,177⟩ pfV44 pfV175 pfV176 pfV177 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase45 : pfCheckTree 45 = true := by
  apply pfTreeLift 45 ⟨pfV45,178,179,180,181⟩ pfV178 pfV179 pfV180 pfV181 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase46 : pfCheckTree 46 = true := by
  apply pfTreeLift 46 ⟨pfV46,182,183,184,185⟩ pfV182 pfV183 pfV184 pfV185 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase47 : pfCheckTree 47 = true := by
  apply pfTreeLift 47 ⟨pfV47,186,187,188,130⟩ pfV186 pfV187 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase48 : pfCheckTree 48 = true := by
  apply pfTreeLift 48 ⟨pfV48,48,189,190,159⟩ pfV48 pfV189 pfV190 pfV159 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase49 : pfCheckTree 49 = true := by
  apply pfTreeLift 49 ⟨pfV49,191,192,193,194⟩ pfV191 pfV192 pfV193 pfV194 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase50 : pfCheckTree 50 = true := by
  apply pfTreeLift 50 ⟨pfV50,195,196,197,198⟩ pfV195 pfV196 pfV197 pfV198 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase51 : pfCheckTree 51 = true := by
  apply pfTreeLift 51 ⟨pfV51,199,200,144,130⟩ pfV199 pfV200 pfV144 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase52 : pfCheckTree 52 = true := by
  apply pfTreeLift 52 ⟨pfV52,201,202,203,204⟩ pfV201 pfV202 pfV203 pfV204 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase53 : pfCheckTree 53 = true := by
  apply pfTreeLift 53 ⟨pfV53,205,206,207,208⟩ pfV205 pfV206 pfV207 pfV208 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase54 : pfCheckTree 54 = true := by
  apply pfTreeLift 54 ⟨pfV54,209,210,211,212⟩ pfV209 pfV210 pfV211 pfV212 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase55 : pfCheckTree 55 = true := by
  apply pfTreeLift 55 ⟨pfV55,213,214,215,67⟩ pfV213 pfV214 pfV215 pfV67 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase56 : pfCheckTree 56 = true := by
  apply pfTreeLift 56 ⟨pfV56,56,216,217,218⟩ pfV56 pfV216 pfV217 pfV218 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase57 : pfCheckTree 57 = true := by
  apply pfTreeLift 57 ⟨pfV57,219,220,221,167⟩ pfV219 pfV220 pfV221 pfV167 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase58 : pfCheckTree 58 = true := by
  apply pfTreeLift 58 ⟨pfV58,222,223,224,225⟩ pfV222 pfV223 pfV224 pfV225 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase59 : pfCheckTree 59 = true := by
  apply pfTreeLift 59 ⟨pfV59,226,227,188,130⟩ pfV226 pfV227 pfV188 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase60 : pfCheckTree 60 = true := by
  apply pfTreeLift 60 ⟨pfV60,60,228,229,230⟩ pfV60 pfV228 pfV229 pfV230 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase61 : pfCheckTree 61 = true := by
  apply pfTreeLift 61 ⟨pfV61,231,232,233,234⟩ pfV231 pfV232 pfV233 pfV234 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase62 : pfCheckTree 62 = true := by
  apply pfTreeLift 62 ⟨pfV62,235,236,237,238⟩ pfV235 pfV236 pfV237 pfV238 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTCase63 : pfCheckTree 63 = true := by
  apply pfTreeLift 63 ⟨pfV63,239,240,241,130⟩ pfV239 pfV240 pfV241 pfV130 rfl (by unfold pfTreeBounds; decide) rfl rfl rfl rfl
  decide +kernel

theorem pfTGroup1 : pfTRange 32 32 :=
  (pfTJoin 32 16 16 (pfTJoin 32 8 8 (pfTJoin 32 4 4 (pfTJoin 32 2 2 (pfTJoin 32 1 1 (pfTOne 32 pfTCase32) (pfTOne 33 pfTCase33)) (pfTJoin 34 1 1 (pfTOne 34 pfTCase34) (pfTOne 35 pfTCase35))) (pfTJoin 36 2 2 (pfTJoin 36 1 1 (pfTOne 36 pfTCase36) (pfTOne 37 pfTCase37)) (pfTJoin 38 1 1 (pfTOne 38 pfTCase38) (pfTOne 39 pfTCase39)))) (pfTJoin 40 4 4 (pfTJoin 40 2 2 (pfTJoin 40 1 1 (pfTOne 40 pfTCase40) (pfTOne 41 pfTCase41)) (pfTJoin 42 1 1 (pfTOne 42 pfTCase42) (pfTOne 43 pfTCase43))) (pfTJoin 44 2 2 (pfTJoin 44 1 1 (pfTOne 44 pfTCase44) (pfTOne 45 pfTCase45)) (pfTJoin 46 1 1 (pfTOne 46 pfTCase46) (pfTOne 47 pfTCase47))))) (pfTJoin 48 8 8 (pfTJoin 48 4 4 (pfTJoin 48 2 2 (pfTJoin 48 1 1 (pfTOne 48 pfTCase48) (pfTOne 49 pfTCase49)) (pfTJoin 50 1 1 (pfTOne 50 pfTCase50) (pfTOne 51 pfTCase51))) (pfTJoin 52 2 2 (pfTJoin 52 1 1 (pfTOne 52 pfTCase52) (pfTOne 53 pfTCase53)) (pfTJoin 54 1 1 (pfTOne 54 pfTCase54) (pfTOne 55 pfTCase55)))) (pfTJoin 56 4 4 (pfTJoin 56 2 2 (pfTJoin 56 1 1 (pfTOne 56 pfTCase56) (pfTOne 57 pfTCase57)) (pfTJoin 58 1 1 (pfTOne 58 pfTCase58) (pfTOne 59 pfTCase59))) (pfTJoin 60 2 2 (pfTJoin 60 1 1 (pfTOne 60 pfTCase60) (pfTOne 61 pfTCase61)) (pfTJoin 62 1 1 (pfTOne 62 pfTCase62) (pfTOne 63 pfTCase63))))))
