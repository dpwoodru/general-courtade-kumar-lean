import GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate
import GeneralCK.Certificates.E8OriginQRealRegularity

/-!
# E8 adaptive family to origin-owner bridge

The completed adaptive family supplies the quantitative inverse certificate.
The sole remaining origin input is the strict degree-15 mixed-derivative
enclosure used by the retained origin checker.
-/

namespace GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge

open E8OriginAnalyticCertificate
open E8OriginMixedDerivativeConsumer
open E8OriginPositiveConsumer

noncomputable def quantitativeCertificate : QuantitativeCertificate :=
  certificateOfGlobalDerivativeBound
    Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound

/-- The completed complex-disc certificate discharges inverse existence,
analyticity, real-axis agreement, Taylor coefficients, and the order-17 tail.
Only strict positivity of the explicit mixed derivative remains. -/
theorem originOwner_of_mixed_pos
    (hpos : ∀ s t : ℝ, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : ℝ) →
      0 < deltaSST (qReal quantitativeCertificate) s t) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) := by
  apply e8PositiveOn_of_globalDerivativeBound_and_mixedCertificate
    Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  exact E8OriginQRealRegularity.mixedDerivativeCertificate_of_mixed_pos
    quantitativeCertificate hpos

#print axioms originOwner_of_mixed_pos

end GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge
