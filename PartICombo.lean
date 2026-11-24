import PartIUse
import PartIPairOrder
import EncodeRows

open OneAdd CF61

def piPairTotalRule : Prop :=
  ∀ k d a v ah D r : ℕ, k=2^d → 2 ≤ k → a<k → v<k → D<4 → r<4 →
    piTrueCount k a v ah D r = (piCellPairs k (16*k*(k*ah+a)+4*k*D+4*v+r)).card

theorem piPartIFromRules (closed : CF61_Closed) (liftRule : piLiftRule)
    (first : piVerifiedFirst) (step : piVerifiedStep) (weightRule : piWeightRule)
    (stGood : ∀ i : ℕ, i < 683 → piGood piRowList[i]! = true) (pairRule : piPairTotalRule) :
    CF61_PartI := by
  refine ⟨closed.1,?_⟩
  intro m hm n hn hN hSingle
  let d := m-2
  let k := K m
  have hd : 0 < d := by dsimp [d]; omega
  have hpow : k=2^d := rfl
  have hk : 2 ≤ k := calc
    2 = 2^1 := by norm_num
    _ ≤ 2^d := Nat.pow_le_pow_right (by omega) (by omega)
    _ = k := hpow.symm
  obtain ⟨a,v,ah,D,r,ha,hv,hah,hD,hr,he⟩ := piDecomp hk (n:=n) (by simpa only [n₀] using hN)
  have hlow : 20*k+3 < 16*k*(k*ah+a)+4*k*D+4*v+r := by rw [← he]; exact hn
  have hn23 := piTrueCountGood liftRule first step weightRule stGood
    hd ha hv hah hD hr hlow
  have htot := pairRule k d a v ah D r hpow hk ha hv hD hr
  rw [← he] at htot
  change piTrueCount k a v ah D r ≠ 2 ∧ piTrueCount k a v ah D r ≠ 3 at hn23
  rw [htot] at hn23
  exact (piTwoOrThree m n hN (cfPISupport closed m hm) (cfPIInject m hm) hSingle).elim hn23.1 hn23.2
