import GeneralCK.Certificates.DyadicFastLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds reduced to checked logarithm bounds

This checker proves an enclosure for `Real.exp x` by checking logarithms of
positive rational lower and upper candidates.  It adds no transcendental
approximation algorithm or trust boundary beyond `DyadicFastLog.check`.
-/

namespace GeneralCK.Certificates.DyadicExp

open DyadicInterval

/-- The dyadic hull of two positive rational endpoint candidates. -/
def enclosure (p : ℕ) (lowerNum lowerDen upperNum upperDen : ℤ) :
    DyadicInterval p :=
  ⟨(DyadicFastLog.fraction p lowerNum lowerDen).lo,
   (DyadicFastLog.fraction p upperNum upperDen).hi⟩

/-- Check logs of the candidate endpoints and compare them with the input
interval. `logLower.hi ≤ input.lo` proves the lower candidate is below the
exponential; `input.hi ≤ logUpper.lo` proves the upper candidate is above it. -/
def check {p : ℕ} (input : DyadicInterval p)
    (lowerNum lowerDen upperNum upperDen : ℤ)
    (lowerExponent lowerTerms upperExponent upperTerms : ℕ)
    (logLower logUpper : DyadicInterval p) : Bool :=
  DyadicFastLog.check lowerNum lowerDen lowerExponent lowerTerms logLower &&
    DyadicFastLog.check upperNum upperDen upperExponent upperTerms logUpper &&
    decide (logLower.hi ≤ input.lo ∧ input.hi ≤ logUpper.lo)

theorem check_sound {p : ℕ} {input : DyadicInterval p}
    {lowerNum lowerDen upperNum upperDen : ℤ}
    {lowerExponent lowerTerms upperExponent upperTerms : ℕ}
    {logLower logUpper : DyadicInterval p}
    (hc : check input lowerNum lowerDen upperNum upperDen
      lowerExponent lowerTerms upperExponent upperTerms logLower logUpper = true)
    {x : ℝ} (hx : input.Contains x) :
    (enclosure p lowerNum lowerDen upperNum upperDen).Contains (Real.exp x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hpair := Bool.and_eq_true_iff.mp htop.1
  have hlogLower := DyadicFastLog.check_sound hpair.1
  have hlogUpper := DyadicFastLog.check_sound hpair.2
  have hcmp : logLower.hi ≤ input.lo ∧ input.hi ≤ logUpper.lo :=
    of_decide_eq_true htop.2
  have hlDen : 0 < lowerDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).2
  have huDen : 0 < upperDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).2
  have hlNum : 0 < lowerNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).1
  have huNum : 0 < upperNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).1
  have hs : (0 : ℝ) < DyadicInterval.scale p := DyadicInterval.scale_cast_pos p
  have hlogLowerLe : Real.log ((lowerNum : ℝ) / lowerDen) ≤ x := by
    have h1 := hlogLower.2
    have h2 : (logLower.hi : ℝ) ≤ (input.lo : ℝ) := by exact_mod_cast hcmp.1
    have h3 := hx.1
    nlinarith
  have hxLeLogUpper : x ≤ Real.log ((upperNum : ℝ) / upperDen) := by
    have h1 := hx.2
    have h2 : (input.hi : ℝ) ≤ (logUpper.lo : ℝ) := by exact_mod_cast hcmp.2
    have h3 := hlogUpper.1
    nlinarith
  have hlRatPos : (0 : ℝ) < (lowerNum : ℝ) / lowerDen := by
    positivity
  have huRatPos : (0 : ℝ) < (upperNum : ℝ) / upperDen := by
    positivity
  have hlExp : (lowerNum : ℝ) / lowerDen ≤ Real.exp x :=
    (Real.log_le_iff_le_exp hlRatPos).mp hlogLowerLe
  have hExpU : Real.exp x ≤ (upperNum : ℝ) / upperDen :=
    (Real.le_log_iff_exp_le huRatPos).mp hxLeLogUpper
  have hlFrac := DyadicFastLog.fraction_sound p lowerNum hlDen
  have huFrac := DyadicFastLog.fraction_sound p upperNum huDen
  constructor
  · exact hlFrac.1.trans (mul_le_mul_of_nonneg_left hlExp hs.le)
  · exact (mul_le_mul_of_nonneg_left hExpU hs.le).trans huFrac.2

end GeneralCK.Certificates.DyadicExp
