import GeneralCK.SmallBoundaryPhiCompactCoordinates
import GeneralCK.SmallBoundaryPhiCompactBoxBounds
import GeneralCK.SmallBoundaryPhiTailSource

/-! The compact contact determinant owner, including its rational lower seam. -/

namespace GeneralCK.SmallBoundaryPhiSchur

open Set SmallMeanPhiCutoff

theorem compact_actual_scalar_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ retainedCutoff) :
    99/100 ≤ naturalA t ∧ naturalA t ≤ 6/5 ∧ naturalK t ≤ 6/5 ∧
      naturalA t-naturalK t ≤ t/5 ∧
      SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t) ≤
        SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/10 := by
  obtain ⟨htU,hz,hzU,hb,hbU⟩ := compact_coordinates_box ht htu
  have h := SmallBoundaryPhiCompactBox.rational_bounds ht.le htU hz.le hzU
    (show 1 ≤ tailB t by linarith) (show tailB t ≤ 10000/9999 by linarith)
  rw [← actualA_eq_box ht (by linarith), ← actualK_eq_box ht (by linarith)] at h
  exact h

theorem compact_comparison_antitone {δ : ℝ} (hδ : 0 < δ) :
    AntitoneOn compactComparisonPotential (Icc δ retainedCutoff) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (f' := fun t => (SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t)-
      SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/10)/t)
  · intro t ht
    have htp : 0 < t := hδ.trans_le ht.1
    have htU := (compact_coordinates_box htp ht.2).1
    exact (hasDerivAt_comparisonPotential htp (by linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have htm := interior_subset ht
    have htp : 0 < t := hδ.trans_le htm.1
    have htU := (compact_coordinates_box htp htm.2).1
    exact (hasDerivAt_comparisonPotential htp (by linarith)).hasDerivWithinAt
  · intro t ht
    have htm := interior_subset ht
    have htp : 0 < t := hδ.trans_le htm.1
    have hbnd := compact_actual_scalar_bounds htp htm.2
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbnd.2.2.2.2) htp.le

theorem compactScalarBounds {δ : ℝ} (hδ : 0 < δ) : CompactScalarBounds δ where
  lowerA := fun _ ht htu => (compact_actual_scalar_bounds (hδ.trans_le ht) htu).1
  upperA := fun _ ht htu => (compact_actual_scalar_bounds (hδ.trans_le ht) htu).2.1
  upperK := fun _ ht htu => (compact_actual_scalar_bounds (hδ.trans_le ht) htu).2.2.1
  defect := fun _ ht htu => (compact_actual_scalar_bounds (hδ.trans_le ht) htu).2.2.2.1
  comparison := compact_comparison_antitone hδ

theorem compactContactOwner_positive_floor {δ : ℝ} (hδ : 0 < δ) : CompactContactOwner δ :=
  compactContactOwner_of_scalarBounds hδ (compactScalarBounds hδ)

theorem compactContactOwner : CompactContactOwner compactDelta :=
  compactContactOwner_positive_floor compactDelta_pos

#print axioms compact_actual_scalar_bounds
#print axioms compact_comparison_antitone
#print axioms compactScalarBounds
#print axioms compactContactOwner_positive_floor
#print axioms compactContactOwner

end GeneralCK.SmallBoundaryPhiSchur
