import CKLaneM07.CE.SoundV2a
import GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge

/-!
# Lane M07 / CE-stat: the real model functions vs. the corpus (monotonicity, identities)

`HnR = H·log 2`, `JnR = J·log 2`, `UpsR = radialSlope·log 2` on `(0, 1/2)`; monotonicity of the
residual functions on `(0, 1/2)` (proved from `H_strictMonoOn` and `radialSlope_antitone`).
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open GeneralCK Set

theorem HnR_eq_hn (z : ℝ) : HnR z = Certificates.Mixed.hn z := by
  unfold HnR Certificates.Mixed.hn; ring

theorem HnR_eq_H (z : ℝ) : HnR z = H z * Real.log 2 := by
  rw [HnR_eq_hn, Certificates.Mixed.hn_eq_H_mul_log]

theorem log2_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

theorem HnR_pos {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : 0 < HnR z := by
  rw [HnR_eq_H]; exact mul_pos (H_pos h0 h1) log2_pos'

theorem HnR_mono : MonotoneOn HnR (Ioo 0 (1 / 2)) := by
  intro a ha b hb hab
  rw [HnR_eq_H, HnR_eq_H]
  apply mul_le_mul_of_nonneg_right _ log2_pos'.le
  exact H_strictMonoOn.monotoneOn ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ hab

theorem LnR_mono : MonotoneOn LnR (Ioo 0 (1 / 2)) := by
  intro a ha b hb hab
  unfold LnR
  have h1 : HnR a ≤ HnR b := HnR_mono ha hb hab
  have h2 : 0 < HnR a := HnR_pos ha.1 (by linarith [ha.2])
  have h3 : 0 < 1 - 2 * a := by linarith [ha.2]
  have h4 : 0 < 1 - 2 * b := by linarith [hb.2]
  have h5 : 1 / (1 - 2 * a) ≤ 1 / (1 - 2 * b) := one_div_le_one_div_of_le h4 (by linarith)
  have h6 : 0 < 1 / (1 - 2 * a) := one_div_pos.mpr h3
  have := mul_le_mul h1 h5 h6.le (h2.le.trans h1)
  linarith

theorem LnR_pos {z : ℝ} (h0 : 0 < z) (h1 : z < 1 / 2) : 0 < LnR z := by
  unfold LnR
  have := HnR_pos h0 (by linarith)
  have h3 : 0 < 1 / (1 - 2 * z) := one_div_pos.mpr (by linarith)
  positivity

theorem JnR_eq {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : JnR z = J z * Real.log 2 := by
  unfold JnR J
  rw [div_mul_cancel₀ _ log2_pos'.ne', Real.log_div (by linarith) h0.ne']

theorem UpsR_eq {z : ℝ} (h0 : 0 < z) (h1 : z < 1 / 2) : UpsR z = radialSlope z * Real.log 2 := by
  have hz1 : 0 < 1 - z := by linarith
  have hL : Real.log 2 ≠ 0 := log2_pos'.ne'
  have hlz : Real.log z < 0 := Real.log_neg h0 (by linarith)
  have hl1z : Real.log (1 - z) < 0 := Real.log_neg hz1 (by linarith)
  have hs : Real.log z + Real.log (1 - z) ≠ 0 := (by linarith : Real.log z + Real.log (1 - z) < 0).ne
  unfold UpsR JnR QaR radialSlope J Certificates.Mixed.kap
  rw [← HnR_eq_hn, Real.log_div hz1.ne' h0.ne', Real.log_mul h0.ne' hz1.ne']
  field_simp

theorem UpsR_anti : AntitoneOn UpsR (Ioo 0 (1 / 2)) := by
  intro a ha b hb hab
  rw [UpsR_eq ha.1 ha.2, UpsR_eq hb.1 hb.2]
  exact mul_le_mul_of_nonneg_right
    (ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ha hb hab) log2_pos'.le

/-- `LnR` at a radial contact point -/
theorem LnR_contact {z h v : ℝ} (hz : 0 < z) (hv1 : v < 1 / 2)
    (heq : z * H v = h * (1 - 2 * v)) : LnR v = 2 * h * Real.log 2 / z := by
  unfold LnR
  rw [HnR_eq_H]
  have h2 : 1 - 2 * v ≠ 0 := by linarith
  have hHv : H v = h * (1 - 2 * v) / z := by
    field_simp
    linarith
  rw [hHv]
  field_simp

end CKLaneM07.CE
