import GeneralCK.Certificates.E8OriginMixedKTransfer
import GeneralCK.Certificates.E8OriginMixedCertificateFromK

namespace GeneralCK.Certificates.E8OriginMixedKClosure

open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer
open E8OriginQRealRegularity
open E8OriginRemainder
open E8OriginSourceKExactAssembly
open E8OriginSourceKResidualLower
open E8OriginMixedKTransfer

theorem sourceK_eq_sourceKFormula (s t : ℝ) :
    sourceK s t = sourceKFormula s t := by
  rfl

/-- The exact source polynomial transfers to the analytic mixed derivative
after charging both the order-17 Taylor tail and the finite coefficient-box
error. -/
theorem sourceK_sub_total_error_le_deltaSST
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (2 / 25 : ℝ)) :
    sourceK s t -
        ((remainderOverRadiusCubed : ℝ) + coefficientCubicErrorFactor) *
          (s + t) ^ 3 ≤ deltaSST (qReal cert) s t := by
  have htail := mixedKFormula_sub_taylor_le_remainder cert hs ht
    (by simpa [radius] using hR)
  have hcoeff := weighted_taylor_sub_sourceKFormula_le_coefficient cert hs ht
    (by simpa [radius] using hR)
  rw [deltaSST_eq_mixedKFormula_qReal_on_origin cert hs ht hR]
  rw [← sourceK_eq_sourceKFormula] at hcoeff
  rw [abs_le] at htail hcoeff
  linarith

/-- The checked coefficient error is absorbed by the source polynomial's
reserved cubic slack, closing strict positivity on the full origin simplex. -/
theorem deltaSST_qReal_pos_on_origin
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hR : s + t ≤ (2 / 25 : ℝ)) :
    0 < deltaSST (qReal cert) s t := by
  have htransfer := sourceK_sub_total_error_le_deltaSST cert hs ht.le hR
  have hsource := sourceK_lower hs ht.le hR
  have htail :
      (remainderOverRadiusCubed : ℝ) < ((13 / 1000000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr remainderOverRadiusCubed_lt
  norm_num at htail
  have hcoeff := coefficientCubicErrorFactor_lt
  have hsum : 0 < s + t := by linarith
  have hcube : 0 < (s + t) ^ 3 := pow_pos hsum 3
  nlinarith

/-- Final premise-free E8 origin certificate. -/
theorem mixedDerivativeCertificate_from_sourceK
    (cert : QuantitativeCertificate) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : ℝ) := by
  apply mixedDerivativeCertificate_of_mixed_pos cert
  intro s t hs ht hR
  exact deltaSST_qReal_pos_on_origin cert hs ht hR

#print axioms sourceK_sub_total_error_le_deltaSST
#print axioms deltaSST_qReal_pos_on_origin
#print axioms mixedDerivativeCertificate_from_sourceK

end GeneralCK.Certificates.E8OriginMixedKClosure
