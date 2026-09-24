import GeneralCK.SmallBoundaryPhiTailSource

namespace GeneralCK.SmallBoundaryPhiSchur

open Set
open SmallMeanPhiCutoff

theorem tailScalarBounds : TailScalarBounds where
  lowerA := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualA_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.A_lower ht.le htU hz.le hzU (by linarith) (by linarith)
  upperA := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualA_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.A_upper ht.le htU hz.le hzU (by linarith) (by linarith)
  upperK := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualK_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.K_upper ht.le htU hz.le hzU (by linarith) (by linarith)
  defect := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    have hbnd := SmallBoundaryPhiTailBox.difference_upper ht htU hz.le hzU
      (show 1 ≤ tailB t by linarith) (show tailB t ≤ 1+1/10000 by linarith)
    rw [← actualA_eq_box ht (by linarith), ← actualK_eq_box ht (by linarith)] at hbnd
    have hv := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hbnd
    linarith
  comparison := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc _ _)
      (f' := fun t => (SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t)-
        SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/10)/t)
    · intro t ht
      have htU := (tail_coordinates_box ht.1 ht.2).1
      exact (hasDerivAt_comparisonPotential ht.1 (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      have htm := interior_subset ht
      have htU := (tail_coordinates_box htm.1 htm.2).1
      exact (hasDerivAt_comparisonPotential htm.1 (by linarith)).hasDerivWithinAt
    · intro t ht
      have htm := interior_subset ht
      obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box htm.1 htm.2
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (SmallBoundaryPhiTailBox.normalizedDerivative_upper htm.1.le htU
          hz.le hzU (by linarith) (by linarith))) htm.1.le

/-- Unconditional closure of the entire singular low-contact tail. -/
theorem lowContactTailOwner : LowContactTailOwner tailDelta :=
  lowContactTailOwner_of_scalarBounds tailScalarBounds

theorem scalarCurvature_of_compactContact (h : CompactContactOwner tailDelta) :
    ScalarCurvatureOwner := scalarCurvature_of_compact_and_tail h lowContactTailOwner

theorem smallBoundaryMidpoint_of_compactContact (h : CompactContactOwner tailDelta) :
    SmallBoundaryPhiMidpointOwner :=
  smallBoundaryMidpoint_of_scalarCurvature (scalarCurvature_of_compactContact h)

theorem belowCutoffHybrid_of_compactContact (h : CompactContactOwner tailDelta) :
    BelowCutoffPhiHybridOwner :=
  belowCutoffHybrid_of_scalarCurvature (scalarCurvature_of_compactContact h)

#print axioms tailScalarBounds
#print axioms lowContactTailOwner
#print axioms scalarCurvature_of_compactContact
#print axioms smallBoundaryMidpoint_of_compactContact
#print axioms belowCutoffHybrid_of_compactContact

end GeneralCK.SmallBoundaryPhiSchur
