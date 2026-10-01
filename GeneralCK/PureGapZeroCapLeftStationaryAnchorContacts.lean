import GeneralCK.PureGapZeroCapLeftStationaryThetaBracketBridge
import GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures
import GeneralCK.Certificates.SmallMeanBounds

/-! Source-only exact-contact brackets for three zero-cap stationary anchors.
The log enclosures themselves are kernel-checkable 20-term witnesses. -/

namespace GeneralCK
open Certificates.ZeroCapLeftStationaryLogEnclosures
open ZeroCapLeftStationaryThetaBracket
namespace ZeroCapLeftStationaryAnchorContacts

private theorem H_lower_from_log_box {v e Al Bl : ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1) (he : 0 ≤ e)
    (hA : Al ≤ -Real.log v) (hB : Bl ≤ -Real.log (1 - v))
    (hnumeric : e * (693147181 / 1000000000) ≤ v * Al + (1 - v) * Bl) :
    e ≤ H v := by
  have htwo := Certificates.PilotData.log_two.2
  norm_num only [div_one] at htwo
  have hsum : v * Al + (1 - v) * Bl ≤
      v * (-Real.log v) + (1 - v) * (-Real.log (1 - v)) :=
    add_le_add (mul_le_mul_of_nonneg_left hA hv)
      (mul_le_mul_of_nonneg_left hB (by linarith))
  have heq := Certificates.SmallMean.entropy_log_identity v
  have hscale := mul_le_mul_of_nonneg_left htwo he
  have hmul : e * Real.log 2 ≤ H v * Real.log 2 := by
    linarith only [hnumeric, hsum, heq, hscale]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

private theorem H_upper_from_log_box {v e Au Bu : ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1) (he : 0 ≤ e)
    (hA : -Real.log v ≤ Au) (hB : -Real.log (1 - v) ≤ Bu)
    (hnumeric : v * Au + (1 - v) * Bu ≤ e * (34657359 / 50000000)) :
    H v ≤ e := by
  have htwo := Certificates.PilotData.log_two.1
  norm_num only [div_one] at htwo
  have hsum : v * (-Real.log v) + (1 - v) * (-Real.log (1 - v)) ≤
      v * Au + (1 - v) * Bu :=
    add_le_add (mul_le_mul_of_nonneg_left hA hv)
      (mul_le_mul_of_nonneg_left hB (by linarith))
  have heq := Certificates.SmallMean.entropy_log_identity v
  have hscale := mul_le_mul_of_nonneg_left htwo he
  have hmul : H v * Real.log 2 ≤ e * Real.log 2 := by
    linarith only [hnumeric, hsum, heq, hscale]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

theorem contact1_upper :
    radialContact (2 * (3175 / 29184 : ℝ)) 1 ≤ 3949 / 10000 := by
  have hH : (967 / 1000 : ℝ) ≤ H (3949 / 10000) :=
    H_lower_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta1_A.1 theta1_B.1 (by norm_num)
  exact contact_upper_of_entropy_lower (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

theorem contact2_upper :
    radialContact (2 * (25 / 76 : ℝ)) 1 ≤ 299 / 1250 := by
  have hH : (793 / 1000 : ℝ) ≤ H (299 / 1250) :=
    H_lower_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta2_A.1 theta2_B.1 (by norm_num)
  exact contact_upper_of_entropy_lower (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

theorem contact3_lower :
    (37 / 250 : ℝ) ≤ radialContact (2 * (375 / 646 : ℝ)) 1 := by
  have hH : H (37 / 250) ≤ (606 / 1000 : ℝ) :=
    H_upper_from_log_box (by norm_num) (by norm_num) (by norm_num)
      theta3_A.2 theta3_B.2 (by norm_num)
  exact contact_lower_of_entropy_upper (by norm_num) (by norm_num)
    (by norm_num) hH (by norm_num)

end ZeroCapLeftStationaryAnchorContacts

#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact1_upper
#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact2_upper
#print axioms GeneralCK.ZeroCapLeftStationaryAnchorContacts.contact3_lower

end GeneralCK
