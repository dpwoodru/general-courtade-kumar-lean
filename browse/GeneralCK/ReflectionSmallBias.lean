import GeneralCK.ReflectionSmallBiasDifferenceJet
import GeneralCK.ReflectionSmallBiasRealAgreement

/-! The complete reflection small-bias triangle. -/

namespace GeneralCK.Reflection

theorem curvature_nonneg_small_bias (a b : ℝ) (hb : 0 < b) (hba : b < a) (ha : a ≤ 3/20) :
    0 ≤ curvature a b := by
  have hh := SmallBiasCurvatureAssembly.curvature_nonneg_of_order24
    SmallBiasDifferenceJet.remainder_order24 hb hba ha
  rwa [SmallBiasRealAgreement.deriv2_difference_eq_curvature hb hba ha] at hh

end GeneralCK.Reflection

