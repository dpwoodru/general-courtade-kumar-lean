import GeneralCK.Certificates.Generated.HighBiasCoarseBounds
import GeneralCK.Certificates.Generated.HighBiasCoarseConstants

namespace GeneralCK.Reflection

/-- The full high-bias / small-partner rectangle, including a arbitrarily close
to one. The compact coefficient enclosure and all scalar bounds are discharged. -/
theorem curvature_high_bias_small_partner {a b : ℝ}
    (ha : (999/1000:ℝ)≤a) (ha' : a<1) (hb : 0<b) (hb' : b≤1/2) :
    0<curvature a b := by
  have ha0 : 0<a := by linarith
  have hab : a*(b/a)=b := by field_simp
  have h := HighBias.curvature_pos_of_certificates
    Certificates.HighBiasCoarse.entropy_high_bias
    Certificates.HighBiasCoarse.entropy_half
    Certificates.HighBiasCoarse.log_two_upper
    (by convert Certificates.HighBiasCoarse.contact_lower using 1; norm_num)
    (by convert Certificates.HighBiasCoarse.contact_upper using 1; norm_num)
    Certificates.HighBiasCoarse.coefficient_bounds
    (a := a) (z := b/a) ⟨ha,ha'⟩ (div_pos hb ha0) (by simpa only [hab] using hb')
  simpa only [hab] using h

end GeneralCK.Reflection
