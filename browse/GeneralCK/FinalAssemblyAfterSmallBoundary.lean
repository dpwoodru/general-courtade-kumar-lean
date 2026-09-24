import GeneralCK.SmallBoundaryPhiCompactClosure
import GeneralCK.SmallBoundaryPhiLowContactClosure

/-!
The compact contact certificate and the low-contact tail close SB-1 without
an analytic premise. This production assembly consumes that theorem below
the positive retained cutoff. The three remaining actual-law owners are
exactly the pre-existing retained phi, large-mean phi, and residual psi
interfaces; no zero-cutoff pure-gap owner is used.
-/

namespace GeneralCK.SmallBoundaryPhiSchur

open SmallMeanPhiCutoff

theorem compactContactOwner_at_tailDelta : CompactContactOwner tailDelta :=
  compactContactOwner_positive_floor (by norm_num [tailDelta])

theorem scalarCurvature : ScalarCurvatureOwner :=
  scalarCurvature_of_compactContact compactContactOwner_at_tailDelta

theorem adjusted_convex : ConvexOn ℝ domain (fun p => adjusted p.1 p.2) :=
  convexOn_adjusted_of_scalarCurvature scalarCurvature

theorem smallBoundaryMidpoint : SmallBoundaryPhiMidpointOwner :=
  smallBoundaryMidpoint_of_compactContact compactContactOwner_at_tailDelta

theorem belowCutoffHybrid : BelowCutoffPhiHybridOwner :=
  belowCutoffHybrid_of_compactContact compactContactOwner_at_tailDelta

/-- The actual Bellman target is closed below the cutoff for either active
branch, including equal means and arbitrary finite underlying types. -/
theorem belowCutoff_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hs : μ.a + μ.b < retainedCutoff) : μ.gap ≤ μ.cost := by
  by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact (hybrid_gap_le_phi hp).trans
      (smallBoundary_phi_gap_le_cost smallBoundaryMidpoint μ hab hs)
  · exact small_mean_hybrid_of_active_psi μ hab
      (by dsimp [retainedCutoff] at hs; linarith) (lt_of_not_ge hp).le

#print axioms compactContactOwner_at_tailDelta
#print axioms scalarCurvature
#print axioms adjusted_convex
#print axioms smallBoundaryMidpoint
#print axioms belowCutoffHybrid
#print axioms belowCutoff_gap_le_cost

end GeneralCK.SmallBoundaryPhiSchur

namespace GeneralCK.HybridAfterSmallBoundary

open SmallMeanPhiCutoff

/-- The strict below-cutoff domain is now proved. Equality at the positive
cutoff remains in the existing retained owner. -/
theorem smallMeanPhi_iff_retained :
    HybridAfterDiagnostic.SmallMeanPhiOutsideDiagnosticOwner ↔
      RetainedSmallMeanPhiHybridOwner := by
  constructor
  · intro h
    exact (smallMeanPhi_iff_cutoff_owners.mp h).2
  · intro h
    exact smallMeanPhi_iff_cutoff_owners.mpr
      ⟨SmallBoundaryPhiSchur.belowCutoffHybrid, h⟩

structure RemainingOwners : Prop where
  retainedSmallMeanPhi : RetainedSmallMeanPhiHybridOwner
  largeMeanPhi : HybridAfterDiagnostic.LargeMeanPhiActiveHybridOwner
  psi : HybridAfterDiagnostic.RemainingPsiHybridOwner

theorem RemainingOwners.toAfterDiagnostic (h : RemainingOwners) :
    HybridAfterDiagnostic.RemainingOwners where
  smallMeanPhi := smallMeanPhi_iff_retained.mpr h.retainedSmallMeanPhi
  largeMeanPhi := h.largeMeanPhi
  psi := h.psi

theorem remainingOwners_iff_afterDiagnostic :
    RemainingOwners ↔ HybridAfterDiagnostic.RemainingOwners := by
  constructor
  · exact RemainingOwners.toAfterDiagnostic
  · intro h
    exact ⟨smallMeanPhi_iff_retained.mp h.smallMeanPhi, h.largeMeanPhi, h.psi⟩

theorem finiteHybridBellman_of_remainingOwners (h : RemainingOwners) :
    FiniteHybridBellman :=
  HybridAfterDiagnostic.finiteHybridBellman_of_remainingOwners h.toAfterDiagnostic

theorem generalCourtadeKumar_of_remainingOwners (h : RemainingOwners) :
    GeneralCourtadeKumar :=
  HybridAfterDiagnostic.generalCourtadeKumar_of_remainingOwners h.toAfterDiagnostic

/-- The existing positive-cutoff scalar route, with its SB-1 premise
discharged. The retained boundary and earlier scalar owners remain visible. -/
theorem generalCourtadeKumar_of_retainedBoundaryOwners
    (hboundary : RetainedBoundaryOwners)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hE8 : E8StrictOnSlopeRange)
    (hlarge : HybridAfterDiagnostic.LargeMeanPhiActiveHybridOwner)
    (hpsi : HybridAfterDiagnostic.RemainingPsiHybridOwner) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_positiveCutoff SmallBoundaryPhiSchur.smallBoundaryMidpoint
    hboundary href hleft hdet hE8 hlarge hpsi

#print axioms smallMeanPhi_iff_retained
#print axioms RemainingOwners.toAfterDiagnostic
#print axioms remainingOwners_iff_afterDiagnostic
#print axioms finiteHybridBellman_of_remainingOwners
#print axioms generalCourtadeKumar_of_remainingOwners
#print axioms generalCourtadeKumar_of_retainedBoundaryOwners

end GeneralCK.HybridAfterSmallBoundary
