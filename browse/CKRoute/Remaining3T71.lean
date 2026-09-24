import CKRoute.Manuscript
import CKLaneC2.Final
import CKLaneC2R.ReflectionBridge
import CKLaneP.RightLowerFinal
import CKLaneN1.CEStatField
import CKLaneN23.RayAssembly
import CKLaneC3.LargeFields
import CKLaneC3.Origin
import CKLaneC3.TAxis
import CKLaneC.SAxis.Final
import GeneralCK.PureGapE8CertificateReduction

/-!
# Remaining3, part (a): `Theorem71Components` with every closed owner bound (CONDITIONAL)

Closed owners bound here (lane theorems, exact types):
* `halfMeanCurvature` := `CKLaneC2.halfMeanCurvatureNegative_certified` (C2);
* `reflection` := `CKLaneC2R.reflection_certified` (C2; the whole field, small-bias and compact parts,
  gate C2/gate/reflection_record.json; coordinator 08:50Z: replaces the conditional B2 route);
* `capFibers.rightLower` := `CKLaneP.rightLower_certified` (P);
* `capFibers.leftStationary` := `CKLaneN1.CEStat.leftStationary_of_rows345` (N1; rows 1, 2 closed inside,
  rows 3, 4, 5 open);
* `capFibers.rightStationary` := `CKLaneN23.RS.rightStationary_of_gamma` at `εc = 1/20` (N23; the two
  ray-convexity certificate pieces stay open);
* `e8Strict` := `GeneralCK.E8CertificateOwners.e8StrictOnSlopeRange` with the six closed owners
  (C3 largeS, largeT, smallSTail, origin, tAxis; C sAxis), restated from `C3/probe/PreAssembly.lean`;
  the `compact` owner stays open.

Every theorem below is CONDITIONAL on the hypotheses in its type. Nothing here closes a route field.
-/

set_option autoImplicit false

namespace CKRoute

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- CONDITIONAL: `E8StrictOnSlopeRange` from the `compact` owner alone (the six other owners of
`GeneralCK.E8CertificateOwners` are the closed lane theorems; same term as `C3/probe/PreAssembly.lean`). -/
theorem e8Strict_of_compactOwner
    (compact : GeneralCK.E8PositiveOn fun s t =>
      (1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ (1 / 50 : ℝ) ≤ t ∧ t ≤ 12) :
    GeneralCK.E8StrictOnSlopeRange :=
  GeneralCK.E8CertificateOwners.e8StrictOnSlopeRange
    ⟨CKLaneC3.LargeFields.largeS, CKLaneC3.LargeFields.largeT, CKLaneC3.LargeFields.smallSTail,
      CKLaneC3.Origin.origin, CKLaneC.SAxis.Final.sAxis, CKLaneC3.TAxis.tAxis, compact⟩

/-- CONDITIONAL: the Theorem 7.1 cap-fiber owners from the open leaf-level pieces. -/
theorem capFibers_of_open
    (hLeftLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower retainedCutoff f (entropyInverse e)) e f)
    (hLeftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f)
    (hRow3 : CKLaneN1.CEStat.TransverseCurvatureOwner)
    (hRow4 : CKLaneN1.CEStat.A3LeafUnion)
    (hRow5 : CKLaneN1.CEStat.HighTCExclusion)
    (hCorner : CKLaneN23.RS.GammaCorner (1 / 20))
    (hNonCorner : CKLaneN23.RS.GammaNonCorner retainedCutoff (1 / 20)) :
    CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff where
  leftLower := hLeftLower
  leftUpper := hLeftUpper
  leftStationary := CKLaneN1.CEStat.leftStationary_of_rows345 hRow3 hRow4 hRow5
  rightLower := CKLaneP.rightLower_certified
  rightStationary := CKLaneN23.RS.rightStationary_of_gamma hCorner hNonCorner

/-- CONDITIONAL: `Theorem71Components` from the open leaf-level pieces. -/
theorem theorem71_of_open
    (hLeft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hDet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hSeam : StrictSeamMinimizerExclusion retainedCutoff)
    (hLeftLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower retainedCutoff f (entropyInverse e)) e f)
    (hLeftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f)
    (hRow3 : CKLaneN1.CEStat.TransverseCurvatureOwner)
    (hRow4 : CKLaneN1.CEStat.A3LeafUnion)
    (hRow5 : CKLaneN1.CEStat.HighTCExclusion)
    (hCorner : CKLaneN23.RS.GammaCorner (1 / 20))
    (hNonCorner : CKLaneN23.RS.GammaNonCorner retainedCutoff (1 / 20))
    (hE8Compact : GeneralCK.E8PositiveOn fun s t =>
      (1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ (1 / 50 : ℝ) ≤ t ∧ t ≤ 12) :
    Theorem71Components where
  reflection := CKLaneC2R.reflection_certified
  correctionLeft := hLeft
  correctionDet := hDet
  seam := hSeam
  capFibers := capFibers_of_open hLeftLower hLeftUpper hRow3 hRow4 hRow5 hCorner hNonCorner
  halfMeanCurvature := CKLaneC2.halfMeanCurvatureNegative_certified
  e8Strict := e8Strict_of_compactOwner hE8Compact

end CKRoute
