import GeneralCK.Certificates.E8OriginSourceKResidualLower

namespace GeneralCK.Certificates.E8OriginMixedCertificateFromK

open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer
open E8OriginQRealRegularity
open E8OriginRemainder
open E8OriginSourceKExactAssembly
open E8OriginSourceKResidualLower

/-- The exact remaining functional transfer after the 208-coefficient
polynomial replay and retained remainder arithmetic have been discharged. -/
def MixedKTransfer (cert : QuantitativeCertificate) : Prop :=
  ∀ s t : Real, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : Real) →
    sourceK s t - (remainderOverRadiusCubed : Real) * (s + t) ^ 3 ≤
      deltaSST (qReal cert) s t

theorem mixedDerivativeCertificate_of_K_transfer
    (cert : QuantitativeCertificate) (htransfer : MixedKTransfer cert) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : Real) := by
  apply mixedDerivativeCertificate_of_mixed_pos cert
  intro s t hs ht hR
  exact (sourceK_sub_remainder_pos hs ht hR).trans_le
    (htransfer s t hs ht hR)

end GeneralCK.Certificates.E8OriginMixedCertificateFromK
