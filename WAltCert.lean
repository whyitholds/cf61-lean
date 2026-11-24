import WAltCol0
import WAltCol4
import WAltCol8
import WAltCol12
import WAltCol16
import WAltCol20
import WAltCol24
import WAltCol28
import WAltCol32
import WAltCol36
import WAltCol40
import WAltCol44
import WAltCol48
import WAltCol52
import WAltCol56
import WAltCol60
import WAltCol64
import WAltCol68
import WAltMath

theorem waAllPass (s : ℕ) (hs : s < 72) : waPass s = true := by
  have hh : (List.range 4).all (fun i => waPass (4*(s/4)+i)) = true := by
    have hb : s/4 ≤ 17 := by omega
    interval_cases h : s/4
    · exact waCol0
    · exact waCol4
    · exact waCol8
    · exact waCol12
    · exact waCol16
    · exact waCol20
    · exact waCol24
    · exact waCol28
    · exact waCol32
    · exact waCol36
    · exact waCol40
    · exact waCol44
    · exact waCol48
    · exact waCol52
    · exact waCol56
    · exact waCol60
    · exact waCol64
    · exact waCol68
  have hr : s%4 ∈ List.range 4 := List.mem_range.mpr (by omega)
  have hd := List.all_eq_true.mp hh (s%4) hr
  simpa only [show 4*(s/4)+s%4=s by omega] using hd
