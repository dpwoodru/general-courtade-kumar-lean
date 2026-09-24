import GeneralCK.PureGapE8CertificateReduction

/-!
# Exact rational pilot for the E8 origin summary

The retained `local_K_origin_R008.json` is a summary of an MPFR/Taylor
calculation.  This module gives its exact rational schema and checks the
arithmetic relation between the polynomial lower bound, remainder upper
bound, and claimed normalized lower bound.  The soundness theorem states the
remaining analytic enclosure premise explicitly.
-/

namespace GeneralCK.Certificates.E8OriginPilot

/-- Exact-rational form of the retained origin summary fields. -/
structure OriginSummary where
  degree : ℕ
  negativeCoefficientCount : ℕ
  anchorLower : ℚ
  anchorUpper : ℚ
  polynomialLower : ℚ
  polynomialUpper : ℚ
  q17AbsBound : ℚ
  remainderLower : ℚ
  remainderUpper : ℚ
  kLower : ℚ
  kUpper : ℚ
  certified : Bool
  deriving Repr

/-- Arithmetic acceptance rule for an origin summary.  Parsing decimal
strings into these rationals is an external data-loading step; all checks
below are exact. -/
def OriginSummary.check (c : OriginSummary) : Bool :=
  decide (c.degree = 15 ∧
    c.negativeCoefficientCount = 74 ∧
    c.certified = true ∧
    c.anchorLower ≤ c.anchorUpper ∧
    0 < c.anchorLower ∧
    c.polynomialLower ≤ c.polynomialUpper ∧
    0 ≤ c.q17AbsBound ∧
    0 ≤ c.remainderLower ∧
    c.remainderLower ≤ c.remainderUpper ∧
    c.kLower ≤ c.kUpper ∧
    c.kLower ≤ c.polynomialLower - c.remainderUpper ∧
    0 < c.kLower)

theorem OriginSummary.check_kLower_pos {c : OriginSummary}
    (hc : c.check = true) : 0 < c.kLower := by
  simp only [OriginSummary.check, decide_eq_true_eq] at hc
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, hpos⟩
  exact hpos

theorem OriginSummary.check_subtraction_sound {c : OriginSummary}
    (hc : c.check = true) :
    c.kLower ≤ c.polynomialLower - c.remainderUpper := by
  simp only [OriginSummary.check, decide_eq_true_eq] at hc
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hsub, _⟩
  exact hsub

/-- If the analytic Taylor replay encloses the normalized mixed derivative
above the checked rational endpoint, the endpoint check proves strict
positivity of that derivative. -/
theorem OriginSummary.proves_mixedDerivative_pos {c : OriginSummary}
    (hc : c.check = true) {K s t : ℝ} (hst : 0 < s + t)
    (henclosure : (c.kLower : ℝ) ≤ K / (s + t) ^ 3) : 0 < K := by
  have hkq : 0 < c.kLower := c.check_kLower_pos hc
  have hk : (0 : ℝ) < (c.kLower : ℝ) := by exact_mod_cast hkq
  have hquot : 0 < K / (s + t) ^ 3 := hk.trans_le henclosure
  rcases div_pos_iff.mp hquot with hpos | hneg
  · exact hpos.1
  · exact False.elim ((not_lt_of_ge (pow_nonneg hst.le 3)) hneg.2)

/-- A compact exact-rational representative of the retained accepted origin
summary.  The endpoints are conservative rational roundings of the JSON
values, while preserving its field layout and certified inequalities. -/
def acceptedPilot : OriginSummary where
  degree := 15
  negativeCoefficientCount := 74
  anchorLower := 599 / 10000000
  anchorUpper := 601 / 10000000
  polynomialLower := 599 / 10000000
  polynomialUpper := 601 / 10000000
  q17AbsBound := 290000000000000
  remainderLower := 129 / 10000000
  remainderUpper := 13 / 1000000
  kLower := 46 / 1000000
  kUpper := 48 / 1000000
  certified := true

theorem acceptedPilot_accepts : acceptedPilot.check = true := by
  norm_num [acceptedPilot, OriginSummary.check]

/-- The same layout with a claimed lower bound exceeding polynomial minus
remainder.  It is deliberately rejected by exact evaluation. -/
def rejectedPilot : OriginSummary where
  degree := 15
  negativeCoefficientCount := 74
  anchorLower := 599 / 10000000
  anchorUpper := 601 / 10000000
  polynomialLower := 599 / 10000000
  polynomialUpper := 601 / 10000000
  q17AbsBound := 290000000000000
  remainderLower := 129 / 10000000
  remainderUpper := 13 / 1000000
  kLower := 48 / 1000000
  kUpper := 49 / 1000000
  certified := true

theorem rejectedPilot_rejects : rejectedPilot.check = false := by
  norm_num [rejectedPilot, OriginSummary.check]

end GeneralCK.Certificates.E8OriginPilot
