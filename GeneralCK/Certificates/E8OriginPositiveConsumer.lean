import GeneralCK.Certificates.E8OriginAnalyticCertificate

/-!
# Handoff from the analytic origin branch to the E8 owner

This file isolates the last two mathematical statements made by the source
origin checker: real-axis identification of the quantitative branch and
positivity of its replayed degree-15 Taylor enclosure.  Once supplied, the
result is exactly the `E8PositiveOn` field used by the global case split.
-/

namespace GeneralCK.Certificates.E8OriginPositiveConsumer

open E8QuantitativeBranchBridge
open E8OriginAnalyticCertificate
open E8TauDiscCertificateOfContraction

noncomputable def qReal (cert : QuantitativeCertificate) (y : ℝ) : ℝ :=
  (qDisc cert.inverse (y : ℂ)).re

def RealAgreementOnOrigin (cert : QuantitativeCertificate) : Prop :=
  ∀ y : ℝ, y ∈ e8SlopeRange → y ≤ (4 / 25 : ℝ) → qReal cert y = e8Q y

def DiscOriginPositive (cert : QuantitativeCertificate) : Prop :=
  ∀ s t : ℝ, E8Admissible s t → s + t ≤ (2 / 25 : ℝ) →
    0 < e8Delta (qReal cert) s t

/-- The quantitative analytic certificate is now a direct consumer for the
origin owner.  The factor `4/25` is exactly the largest argument `2s+t`
appearing in `e8Delta` when `s+t ≤ 2/25`. -/
theorem e8PositiveOn_of_quantitativeCertificate
    (cert : QuantitativeCertificate)
    (hreal : RealAgreementOnOrigin cert)
    (hpositive : DiscOriginPositive cert) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) := by
  intro s t hadm hst
  have hs0 : 0 ≤ s := hadm.1.le
  have ht0 : 0 ≤ t := hadm.2.1.le
  have hs : s ≤ (4 / 25 : ℝ) := by linarith
  have ht : t ≤ (4 / 25 : ℝ) := by linarith
  have hsum0 : 0 ≤ s + t := by positivity
  have hsum : s + t ≤ (4 / 25 : ℝ) := by linarith
  have htwo0 : 0 ≤ 2 * s + t := by positivity
  have htwo : 2 * s + t ≤ (4 / 25 : ℝ) := by linarith
  have hp := hpositive s t hadm hst
  unfold e8Delta at hp ⊢
  rw [hreal s hadm.2.2.1 hs, hreal t hadm.2.2.2.1 ht,
    hreal (s + t) hadm.2.2.2.2.1 hsum,
    hreal (2 * s + t) hadm.2.2.2.2.2 htwo] at hp
  exact hp

def GlobalDerivativeBound : Prop :=
  ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)

noncomputable def certificateOfGlobalDerivativeBound
    (hAggregate : GlobalDerivativeBound) : QuantitativeCertificate :=
  quantitativeCertificate_of_expr_bound hAggregate

/-- Final aggregate-facing origin interface.  The generated adaptive family
supplies `hAggregate`; the remaining arguments are precisely the real-axis
identification and the degree-15 origin polynomial replay for the resulting
quantitative branch. -/
theorem e8PositiveOn_of_globalDerivativeBound
    (hAggregate : GlobalDerivativeBound)
    (hreal : RealAgreementOnOrigin (certificateOfGlobalDerivativeBound hAggregate))
    (hpositive : DiscOriginPositive (certificateOfGlobalDerivativeBound hAggregate)) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) :=
  e8PositiveOn_of_quantitativeCertificate _ hreal hpositive

end GeneralCK.Certificates.E8OriginPositiveConsumer
