import GeneralCK.ReflectionHighBiasLargeRegion
import GeneralCK.Certificates.Generated.LowRatioFamily.FullCertificate

namespace GeneralCK.Reflection
open Set

/-- The completed low-ratio strip extends through all larger interior biases
using the independent high-bias theorem. -/
theorem curvature_low_ratio_large_bias {a z : ℝ}
    (ha : (3/20:ℝ)≤a) (ha1 : a<1) (hz : 0<z) (hz1 : z≤1/1000) :
    0<curvature a (a*z) := by
  by_cases hhigh : (999/1000:ℝ)≤a
  · apply curvature_high_bias hhigh ha1
    · exact mul_pos (by linarith) hz
    · have ha0 : 0<a := by linarith
      nlinarith
  · exact Certificates.LowRatioFamily.full_low_ratio_strip
      ⟨ha,(lt_of_not_ge hhigh).le⟩ ⟨hz,hz1⟩

/-- Exact remaining reflection inputs after removing both completed regions.
No unproved global curvature sign is hidden in either input. -/
theorem curvature_nonneg_of_remaining_regions
    (hsmall : ∀ a b : ℝ, 0<b → b<a → a≤3/20 → 0≤curvature a b)
    (hcompact : ∀ a z : ℝ, a∈Icc (3/20:ℝ) (999/1000) →
      z∈Ioo (1/1000:ℝ) 1 → 0≤curvature a (a*z))
    {a b : ℝ} (hb : 0<b) (hba : b<a) (ha1 : a<1) : 0≤curvature a b := by
  by_cases hsmall_a : a≤(3/20:ℝ)
  · exact hsmall a b hb hba hsmall_a
  have ha : (3/20:ℝ)≤a := (lt_of_not_ge hsmall_a).le
  have ha0 : 0<a := hb.trans hba
  have hab : a*(b/a)=b := by field_simp
  have hz : 0<b/a := div_pos hb ha0
  have hz1 : b/a<1 := (div_lt_one ha0).mpr hba
  by_cases hhigh : (999/1000:ℝ)≤a
  · exact (curvature_high_bias hhigh ha1 hb hba).le
  by_cases hlow : b/a≤(1/1000:ℝ)
  · simpa only [hab] using (curvature_low_ratio_large_bias ha ha1 hz hlow).le
  · simpa only [hab] using hcompact a (b/a) ⟨ha,(lt_of_not_ge hhigh).le⟩
      ⟨lt_of_not_ge hlow,hz1⟩

end GeneralCK.Reflection
