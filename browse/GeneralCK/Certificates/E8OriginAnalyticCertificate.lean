import GeneralCK.Certificates.E8QCoeff15
import GeneralCK.Certificates.E8CauchyTailBound
import GeneralCK.Certificates.E8TauDiscCertificateOfContraction

/-!
# Complete analytic input for the E8 origin checker

The inverse recurrence now supplies every retained coefficient enclosure.
This file packages that unconditional finite part with the Cauchy estimate
for the sole remaining order-17 analytic tail.
-/

namespace GeneralCK.Certificates.E8OriginAnalyticCertificate

open Metric Set
open E8AnalyticGerm E8OriginRemainder E8AnalyticCoefficientBoxes
open E8QCoeff15
open E8QuantitativeBranchBridge
open E8TauDiscCertificateOfContraction

def HasSourceCenterRemainder : Prop :=
  ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
    (∀ z, qGerm z =
      (∑ n ∈ Finset.range 16, z ^ n * (sourceCenter n : ℂ)) +
      (∑ n ∈ Finset.range 16,
        z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))) +
      z ^ 17 * r z) ∧
    (∀ z, ‖z‖ ≤ (radius : ℝ) →
      ‖∑ n ∈ Finset.range 16,
        z ^ n * (qTaylorCoeff n - (sourceCenter n : ℂ))‖ ≤
          (coefficientErrorBudget : ℝ))

theorem hasSourceCenterRemainder : HasSourceCenterRemainder :=
  exists_unconditional_source_center_remainder

/-- The exact analytic data consumed by the retained origin Taylor checker.
The finite coefficient portion is now unconditional; `tailBound` is the
single uniform analytic estimate left after degree 15. -/
structure Certificate : Prop where
  sourceRemainder : HasSourceCenterRemainder
  tailBound : ∀ y ∈ closedBall (0 : ℂ) (4 / 25 : ℝ),
    ‖iteratedDeriv 17 qGerm y‖ ≤ (q17AbsBound : ℝ)

/-- Ordinary complex-disc data produces the complete origin analytic
certificate.  All recurrence, source-box, and scalar Cauchy arithmetic is
discharged internally. -/
theorem certificate_of_disc_bound
    {outer rho C : ℝ} (hrho : 0 < rho)
    (hfit : (4 / 25 : ℝ) + rho ≤ outer)
    (hf : DiffContOnCl ℂ qGerm (ball 0 outer))
    (hC : ∀ z ∈ closedBall (0 : ℂ) outer, ‖qGerm z‖ ≤ C)
    (harith : (Nat.factorial 17) * C / rho ^ 17 ≤ (q17AbsBound : ℝ)) :
    Certificate where
  sourceRemainder := hasSourceCenterRemainder
  tailBound := E8CauchyTailBound.qGerm_seventeenth_derivative_le_source_bound
    hrho hfit hf hC harith

/-- Sound full-disc form of the origin certificate.  The Taylor coefficients
are those of `qGerm`, while the locally equal quantitative branch carries the
uniform order-17 bound on the whole source disc. -/
structure QuantitativeCertificate where
  inverse : TauDiscInverseCertificate
  sourceRemainder : HasSourceCenterRemainder
  coeffAgreement : ∀ n : ℕ,
    iteratedDeriv n (qDisc inverse) 0 = iteratedDeriv n qGerm 0
  tailBound : ∀ y ∈ closedBall (0 : ℂ) (4 / 25 : ℝ),
    ‖iteratedDeriv 17 (qDisc inverse) y‖ ≤ (q17AbsBound : ℝ)

noncomputable def quantitativeCertificate_of_inverse (cert : TauDiscInverseCertificate) :
    QuantitativeCertificate where
  inverse := cert
  sourceRemainder := hasSourceCenterRemainder
  coeffAgreement := iteratedDeriv_qDisc_zero cert
  tailBound := qDisc_seventeenth_derivative_le_source_bound cert

/-- The exact elementary derivative enclosure is sufficient for every
analytic and Cauchy component of the origin certificate. -/
noncomputable def quantitativeCertificate_of_expr_bound
    (hExpr : ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)) :
    QuantitativeCertificate :=
  quantitativeCertificate_of_inverse
    (tauDiscInverseCertificateOfExprBound hExpr)

end GeneralCK.Certificates.E8OriginAnalyticCertificate
