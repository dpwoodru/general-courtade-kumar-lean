import GeneralCK.PureGapZeroCapLeftStationaryEntropyBounds
import GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals
import GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle

/-! Additive actual-contact closure for a bounded zero-cap left-stationary
slice. Its sources are only staged; all named theorems require Lean compilation
and a standard-three axiom audit before acceptance. -/

namespace GeneralCK
open ZeroCapLeftStationaryThetaBracket
open ZeroCapLeftStationaryAnchorContacts
open ZeroCapLeftStationaryRadialSlopeIntervals
open ZeroCapLeftStationaryEntropyBounds
namespace ZeroCapLeftStationaryNarrowMiddleCertified

theorem theta1_lower :
    (121 / 100 : ℝ) ≤ e8Theta (3175 / 29184) :=
  radialSlope1_lower.trans
    (e8Theta_lower_of_contact_upper (by norm_num) (by norm_num)
      (by norm_num) contact1_upper)

theorem theta2_lower :
    (3 : ℝ) ≤ e8Theta (25 / 76) :=
  radialSlope2_lower.trans
    (e8Theta_lower_of_contact_upper (by norm_num) (by norm_num)
      (by norm_num) contact2_upper)

theorem theta3_upper :
    e8Theta (375 / 646) ≤ (417 / 100 : ℝ) :=
  (e8Theta_upper_of_contact_lower (by norm_num) (by norm_num)
    (by norm_num) contact3_lower).trans radialSlope3_upper

theorem no_left_stationary_in_narrow_middle {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16) :
    deriv (fun y => canonicalPureGap a y (H a) (H b)) c ≠ 0 := by
  obtain ⟨hElower, hEupper, hBupper⟩ :=
    narrow_box_entropy_bounds ha ha' hb hb'
  exact ZeroCapLeftStationaryNarrowMiddle.no_stationary_of_three_theta_anchors
    ha ha' hb hb' hc hc' hElower hEupper hBupper
    theta1_lower theta2_lower theta3_upper

end ZeroCapLeftStationaryNarrowMiddleCertified

#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta1_lower
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta2_lower
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.theta3_upper
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddleCertified.no_left_stationary_in_narrow_middle

end GeneralCK
