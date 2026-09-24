import GeneralCK.ReflectionRemainingRegions
import GeneralCK.Certificates.Generated.MidpointFamily.FullCertificate
import GeneralCK.Certificates.Generated.MidpointNextFamily.FullCertificate

namespace GeneralCK.Reflection
open Set

/-- The two midpoint families, the completed boundary strip, and the
independent high-bias theorem cover every positive ratio through `1/20` for
all biases at least `3/20`. -/
theorem curvature_low_ratio_to_twentieth {a z : ℝ}
    (ha : (3/20:ℝ) ≤ a) (ha1 : a < 1) (hz : 0 < z) (hz1 : z ≤ 1/20) :
    0 < curvature a (a*z) := by
  by_cases hhigh : (999/1000:ℝ) ≤ a
  · apply curvature_high_bias hhigh ha1
    · exact mul_pos (by linarith) hz
    · nlinarith
  have habox : Certificates.Reflection.Bounds (3/20:ℝ) (999/1000) a :=
    ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hboundary : z ≤ (1/1000:ℝ)
  · exact curvature_low_ratio_large_bias ha ha1 hz hboundary
  by_cases hmidpoint : z ≤ (1/100:ℝ)
  · exact Certificates.ReflectionMidpointFamily.full_midpoint_strip habox
      ⟨(lt_of_not_ge hboundary).le, hmidpoint⟩
  · exact Certificates.ReflectionMidpointNextFamily.full_midpoint_next_strip habox
      ⟨(lt_of_not_ge hmidpoint).le, hz1⟩

/-- After the two midpoint families, the compact reflection premise starts
strictly above `z=1/20`; all lower ratios and endpoint overlaps are proved. -/
theorem curvature_nonneg_of_remaining_regions_extended
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3/20 → 0 ≤ curvature a b)
    (hcompact : ∀ a z : ℝ, a ∈ Icc (3/20:ℝ) (999/1000) →
      z ∈ Ioo (1/20:ℝ) 1 → 0 ≤ curvature a (a*z))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a < 1) :
    0 ≤ curvature a b := by
  refine curvature_nonneg_of_remaining_regions hsmall ?_ hb hba ha1
  intro x z hx hz
  by_cases hlow : z ≤ (1/20:ℝ)
  · exact (curvature_low_ratio_to_twentieth hx.1 (hx.2.trans_lt (by norm_num))
      (by linarith [hz.1]) hlow).le
  · exact hcompact x z hx ⟨lt_of_not_ge hlow, hz.2⟩

end GeneralCK.Reflection
