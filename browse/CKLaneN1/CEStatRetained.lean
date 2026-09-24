import CKLaneN1.CEStat
import GeneralCK.PsiBoundaryLeafReplay

set_option autoImplicit false

/-!
# Lane N1: CE-stat S.3 row 1 — retained-domain exclusion

`0 < t_C ≤ 1/80000` and `A ≤ 21/200` force `a + c < S = 10⁻⁴`:
`b < t_C ≤ 1/80000` (chart order), so `e < f = H(b) ≤ H(1/80000) ≤ 1/4000`; then
`c - a ≤ (21/200)(e + f) < 21/400000` and `a < b`, whence `a + c < 2/80000 + 21/400000 < 10⁻⁴`.
-/

namespace CKLaneN1.CEStat

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- `a = ι(e) < b = ι(f)` for `0 < e < f ≤ 1`. -/
theorem inv_lt_inv {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f ≤ 1) :
    entropyInverse e < entropyInverse f := by
  have hf0 : 0 < f := he.trans hef
  have h1 := entropyInverse_spec he.le (hef.le.trans hf)
  have h2 := entropyInverse_spec hf0.le hf
  by_contra hn
  have hle : entropyInverse f ≤ entropyInverse e := le_of_not_gt hn
  have := H_strictMonoOn.monotoneOn ⟨h2.1, h2.2.1⟩ ⟨h1.1, h1.2.1⟩ hle
  rw [h1.2.2, h2.2.2] at this
  linarith

/-- `H(1/80000) ≤ 1/4000` (`80000 ≤ 2^17`). -/
theorem H_one_80000_le : H (1 / 80000) ≤ 1 / 4000 := by
  refine BoundaryStrip.H_le_of_pow (v := 1 / 80000) (by norm_num) (by norm_num) (b := 80000)
    (by norm_num) (by norm_num) (p := 17) (k := 1) (by norm_num) (by norm_num) ?_
  norm_num

/-- **S.3 row 1 (CLOSED here):** retained-domain exclusion. -/
theorem retainedDomainExclusion : RetainedDomainExclusion := by
  intro e f c hp htc hA
  have hord := chart_order hp
  obtain ⟨he, hef, hf, hbc, hc, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  obtain ⟨hb0, hb2, hHb⟩ := entropyInverse_spec hf0.le hf
  have hab := inv_lt_inv he hef hf
  have hb80 : entropyInverse f < 1 / 80000 := hord.1.trans_le htc
  have hfH : f ≤ 1 / 4000 := by
    have hm := H_strictMonoOn.monotoneOn ⟨hb0, hb2⟩ ⟨by norm_num, by norm_num⟩ hb80.le
    rw [hHb] at hm
    exact hm.trans H_one_80000_le
  have hE : 0 < e + f := by linarith
  have hcA : c - entropyInverse e ≤ 21 / 200 * (e + f) := by
    unfold chartA at hA
    rwa [div_le_iff₀ hE] at hA
  unfold retainedCutoff
  nlinarith

end CKLaneN1.CEStat
