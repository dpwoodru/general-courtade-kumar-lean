import GeneralCK.ReflectionRemainingRegionsExtended
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.FullCertificate
import GeneralCK.Certificates.ReflectionMidpointCombinedCoverage

/-!
# Reflection remainder after all completed midpoint families

The four kernel-checked midpoint families cover the ratio strip through
`17 / 200`.  This file exposes the smaller compact premise that remains.
-/

namespace GeneralCK.Reflection
open Set

theorem curvature_low_ratio_to_seventeen_two_hundred {a z : ℝ}
    (ha : (3 / 20 : ℝ) ≤ a) (ha1 : a < 1)
    (hz : 0 < z) (hz1 : z ≤ 17 / 200) :
    0 < curvature a (a * z) := by
  by_cases hhigh : (999 / 1000 : ℝ) ≤ a
  · apply curvature_high_bias hhigh ha1
    · exact mul_pos (by linarith) hz
    · nlinarith
  have habox : Certificates.Reflection.Bounds (3 / 20 : ℝ) (999 / 1000) a :=
    ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hbase : z ≤ (1 / 20 : ℝ)
  · exact curvature_low_ratio_to_twentieth ha ha1 hz hbase
  by_cases hext : z ≤ (406621 / 5000000 : ℝ)
  · exact Certificates.ReflectionMidpointExtensionFamily.full_midpoint_extension
      habox ⟨(lt_of_not_ge hbase).le, hext⟩
  · exact Certificates.ReflectionMidpointNextBandFamily.full_midpoint_next_band
      habox ⟨(lt_of_not_ge hext).le, hz1⟩

/-- Only the small-bias region and ratios strictly above `17/200` remain
after applying every completed reflection family. -/
theorem curvature_nonneg_of_remaining_regions_certified
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3 / 20 → 0 ≤ curvature a b)
    (hcompact : ∀ a z : ℝ, a ∈ Icc (3 / 20 : ℝ) (999 / 1000) →
      z ∈ Ioo (17 / 200 : ℝ) 1 → 0 ≤ curvature a (a * z))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a < 1) :
    0 ≤ curvature a b := by
  by_cases hsmall_a : a ≤ (3 / 20 : ℝ)
  · exact hsmall a b hb hba hsmall_a
  have ha : (3 / 20 : ℝ) ≤ a := (lt_of_not_ge hsmall_a).le
  have ha0 : 0 < a := hb.trans hba
  have hab : a * (b / a) = b := by field_simp
  have hz : 0 < b / a := div_pos hb ha0
  have hz1 : b / a < 1 := (div_lt_one ha0).mpr hba
  by_cases hhigh : (999 / 1000 : ℝ) ≤ a
  · exact (curvature_high_bias hhigh ha1 hb hba).le
  by_cases hlow : b / a ≤ (17 / 200 : ℝ)
  · simpa only [hab] using
      (curvature_low_ratio_to_seventeen_two_hundred ha ha1 hz hlow).le
  · simpa only [hab] using hcompact a (b / a)
      ⟨ha, (lt_of_not_ge hhigh).le⟩ ⟨lt_of_not_ge hlow, hz1⟩

#print axioms curvature_low_ratio_to_seventeen_two_hundred
#print axioms curvature_nonneg_of_remaining_regions_certified

/-- Every completed reflection certificate family, including the
post-next-band family, covers all positive ratios through `43 / 500`.

This is the current reduction boundary for the global curvature obligation:
only small bias `a ≤ 3 / 20` and the compact rectangle with ratio strictly
above `43 / 500` remain. -/
theorem curvature_nonneg_of_remaining_regions_post_next_band
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3 / 20 → 0 ≤ curvature a b)
    (hcompact : ∀ a z : ℝ, a ∈ Icc (3 / 20 : ℝ) (999 / 1000) →
      z ∈ Ioo (43 / 500 : ℝ) 1 → 0 ≤ curvature a (a * z))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a < 1) :
    0 ≤ curvature a b := by
  by_cases hsmall_a : a ≤ (3 / 20 : ℝ)
  · exact hsmall a b hb hba hsmall_a
  have ha : (3 / 20 : ℝ) ≤ a := (lt_of_not_ge hsmall_a).le
  have ha0 : 0 < a := hb.trans hba
  have hab : a * (b / a) = b := by field_simp
  have hz : 0 < b / a := div_pos hb ha0
  have hz1 : b / a < 1 := (div_lt_one ha0).mpr hba
  by_cases hhigh : (999 / 1000 : ℝ) ≤ a
  · exact (curvature_high_bias hhigh ha1 hb hba).le
  have habox : Certificates.Reflection.Bounds
      (3 / 20 : ℝ) (999 / 1000) a := ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hcovered : b / a ≤ (43 / 500 : ℝ)
  · simpa only [hab] using
      (GeneralCK.Certificates.ReflectionMidpointCombinedCoverage.full_positive_ratio_through_post_next_band
        habox ⟨hz, hcovered⟩).le
  · simpa only [hab] using hcompact a (b / a) habox
      ⟨lt_of_not_ge hcovered, hz1⟩

#print axioms curvature_nonneg_of_remaining_regions_post_next_band

end GeneralCK.Reflection
