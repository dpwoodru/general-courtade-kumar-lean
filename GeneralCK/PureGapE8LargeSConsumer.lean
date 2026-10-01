import GeneralCK.PureGapE8AxisConsumers
import Mathlib.Analysis.Convex.Function

/-!
# The analytic large-s reduction for equation (8)

This is the manuscript's logarithmic-convexity argument, with the actual
regularized inverse and all integration/domain details discharged.  The
remaining inputs are one-variable structure and the one-point shift bound.
-/

namespace GeneralCK

open Set Filter

theorem deriv_e8RegularQ_eq {y : ℝ} (hy : 0 < y) :
    deriv e8RegularQ y = deriv e8Q y := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hy] with z hz
  exact e8RegularQ_eq_e8Q hz.le

theorem deriv_e8RegularQ_pos {y : ℝ}
    (hy : y = 0 ∨ y ∈ e8SlopeRange) : 0 < deriv e8RegularQ y := by
  rcases hy with rfl | hy
  · rw [hasDerivAt_e8RegularQ_zero.deriv]
    positivity
  · rw [deriv_e8RegularQ_eq (e8SlopeRange_subset_pos hy)]
    exact deriv_e8Q_pos hy

/-- The four-point inequality for convex logarithms.  The two interior
arguments are complementary convex combinations of the endpoints. -/
theorem convex_add_increment {f : ℝ → ℝ} {s u : ℝ}
    (hs : 0 < s) (hu : 0 ≤ u) (h : ConvexOn ℝ (Icc 0 (s + u)) f) :
    f s + f u ≤ f 0 + f (s + u) := by
  have hsum : 0 < s + u := by linarith
  have hsumne : s + u ≠ 0 := hsum.ne'
  have ha : 0 ≤ s / (s + u) := div_nonneg hs.le hsum.le
  have hb : 0 ≤ u / (s + u) := div_nonneg hu hsum.le
  have hab : s / (s + u) + u / (s + u) = 1 := by field_simp
  have hends0 : (0 : ℝ) ∈ Icc 0 (s + u) := ⟨le_rfl, hsum.le⟩
  have hends1 : s + u ∈ Icc 0 (s + u) := ⟨hsum.le, le_rfl⟩
  have hfirst := h.2 hends0 hends1 hb ha (by linarith [hab])
  have hsecond := h.2 hends0 hends1 ha hb hab
  simp only [smul_eq_mul, mul_zero, zero_add] at hfirst hsecond
  rw [div_mul_cancel₀ _ hsumne] at hfirst hsecond
  have hweight :
      u / (s + u) * f 0 + s / (s + u) * f (s + u) +
        (s / (s + u) * f 0 + u / (s + u) * f (s + u)) =
      f 0 + f (s + u) := by field_simp; ring
  linarith

/-- Convexity of `log Q'` makes the ratio of shifted derivatives at least
its initial ratio. -/
theorem e8RegularQ_shift_product_le {s u : ℝ} (hs : 0 < s) (hu : 0 < u)
    (hmax : s + u ∈ e8SlopeRange)
    (hconvex : ConvexOn ℝ (Icc 0 (s + u))
      (fun y => Real.log (deriv e8RegularQ y))) :
    deriv e8RegularQ s * deriv e8RegularQ u ≤
      deriv e8RegularQ 0 * deriv e8RegularQ (s + u) := by
  have hds := deriv_e8RegularQ_pos (Or.inr
    (e8SlopeRange_downward hmax hs (by linarith)))
  have hdu := deriv_e8RegularQ_pos (Or.inr
    (e8SlopeRange_downward hmax hu (by linarith)))
  have hd0 := deriv_e8RegularQ_pos (y := 0) (Or.inl rfl)
  have hdmax := deriv_e8RegularQ_pos (Or.inr hmax)
  have h := convex_add_increment hs hu.le hconvex
  rw [← Real.log_mul hds.ne' hdu.ne', ← Real.log_mul hd0.ne' hdmax.ne'] at h
  exact (Real.log_le_log_iff (mul_pos hds hdu) (mul_pos hd0 hdmax)).mp h

theorem e8Delta_pos_of_shifted_derivative {s t : ℝ} (hadm : E8Admissible s t)
    (hshift : ∀ u ∈ Ioo 0 t,
      2 * deriv e8RegularQ u < deriv e8RegularQ (s + u)) :
    0 < e8Delta e8Q s t := by
  let f : ℝ → ℝ := fun u => e8RegularQ (s + u) - e8RegularQ s - 2 * e8RegularQ u
  have hf : ∀ u ∈ Icc 0 t,
      HasDerivAt f (deriv e8RegularQ (s + u) - 2 * deriv e8RegularQ u) u := by
    intro u hu
    have hsum : s + u ∈ e8SlopeRange :=
      e8SlopeRange_downward hadm.2.2.2.2.1 (by linarith [hadm.1, hu.1])
        (by linarith [hu.2])
    have hd1 := (e8RegularQ_contDiffAt_of_mem hsum).differentiableAt (by norm_num)
    have hd0 := (e8RegularQ_contDiffAt_interval hadm.2.2.2.1 hu).differentiableAt
      (by norm_num)
    have h := ((hd1.hasDerivAt.comp u
      ((hasDerivAt_const u s).add (hasDerivAt_id u))).sub_const (e8RegularQ s)).sub
        (hd0.hasDerivAt.const_mul 2)
    convert! h using 1; simp
  have hmono : StrictMonoOn f (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
    · exact fun u hu => (hf u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo 0 t := by simpa using hu
      rw [(hf u ⟨hu'.1.le, hu'.2.le⟩).deriv]
      exact sub_pos.mpr (hshift u hu')
  have hgap := hmono ⟨le_rfl, hadm.2.1.le⟩ ⟨hadm.2.1.le, le_rfl⟩ hadm.2.1
  have hgap' : 0 < e8Q (s + t) - e8Q s - 2 * e8Q t := by
    simpa [f, e8RegularQ_eq_e8Q hadm.1.le, e8RegularQ_eq_e8Q hadm.2.1.le,
      e8RegularQ_eq_e8Q (add_nonneg hadm.1.le hadm.2.1.le)] using hgap
  rw [e8Delta_tail_identity]
  exact add_pos (mul_pos (e8Q_pos hadm.2.2.2.2.2) hgap')
    (mul_pos (e8Q_pos hadm.2.2.2.1)
      (add_pos (e8Q_pos hadm.2.2.2.2.1) (e8Q_pos hadm.2.2.1)))

/-- The one-variable numerical structure used by the large-s proof.
Each assertion is restricted to the range actually reached by the inverse. -/
structure E8LargeSStructure : Prop where
  derivative_mono : ∀ x ∈ e8SlopeRange,
    MonotoneOn (deriv e8RegularQ) (Icc 0 x)
  log_derivative_convex : ∀ x ∈ e8SlopeRange,
    ConvexOn ℝ (Icc 0 x) (fun y => Real.log (deriv e8RegularQ y))
  shift : 2 * (Real.log 2 / 8) < deriv e8RegularQ (63 / 20)

/-- Logarithmic convexity, monotonicity, and the one-point bound close the
entire infinite large-s region by exact analysis. -/
theorem e8_largeS_of_structure (h : E8LargeSStructure) :
    E8PositiveOn fun s _ => (63 / 20 : ℝ) ≤ s := by
  intro s t hadm hs
  apply e8Delta_pos_of_shifted_derivative hadm
  intro u hu
  have hsum : s + u ∈ e8SlopeRange :=
    e8SlopeRange_downward hadm.2.2.2.2.1 (by linarith [hadm.1, hu.1]) (by linarith [hu.2])
  have hprod := e8RegularQ_shift_product_le hadm.1 hu.1 hsum
    (h.log_derivative_convex _ hsum)
  have hpoint := h.derivative_mono s hadm.2.2.1
    (show (63 / 20 : ℝ) ∈ Icc 0 s by constructor <;> linarith)
    (show s ∈ Icc 0 s from ⟨hadm.1.le, le_rfl⟩) hs
  have hshift : 2 * deriv e8RegularQ 0 < deriv e8RegularQ s := by
    rw [hasDerivAt_e8RegularQ_zero.deriv]
    exact h.shift.trans_le hpoint
  have hdu := deriv_e8RegularQ_pos (Or.inr
    (e8SlopeRange_downward hadm.2.2.2.1 hu.1 hu.2.le))
  have hd0 := deriv_e8RegularQ_pos (y := 0) (Or.inl rfl)
  nlinarith [mul_lt_mul_of_pos_right hshift hdu]

#print axioms e8RegularQ_shift_product_le
#print axioms e8Delta_pos_of_shifted_derivative
#print axioms e8_largeS_of_structure

end GeneralCK
