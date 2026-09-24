import CKLaneA5.ChartOwnersAsm
import CKLaneA5.Bands

/-!
# Lane A5: `correctionLeft` / `correctionDet` at the exact `CKRoute.Theorem71Components` field types

`GeneralCK.Correction.Complement.orderedTriangle_signs_of_charts` applied to
* `CKLaneA5.Bands.band1_actual : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1` (R-B1 cover),
* `CKLaneA5.Bands.band2_actual : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1` (R-B2 owner),
* `CKLaneA5.Assembly.chartOwners : ChartOwners` (lanes A1, A2, A3, A4, A5).

Provider: private merged root `A/asmroot5` (F-C root + R-B1/R-B2 band modules, manifest A/a5/asmroot5_manifest.tsv).
-/

namespace CKLaneA5.Assembly

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement

theorem correction_signs :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧ (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :=
  orderedTriangle_signs_of_charts CKLaneA5.Bands.band1_actual CKLaneA5.Bands.band2_actual chartOwners

/-- `Theorem71Components.correctionLeft` -/
theorem correctionLeft :
    ∀ p ∈ GeneralCK.Correction.orderedTriangle, 0 < GeneralCK.Correction.Mleft p.1 p.2 :=
  correction_signs.1

/-- `Theorem71Components.correctionDet` -/
theorem correctionDet :
    ∀ p ∈ GeneralCK.Correction.orderedTriangle, 0 ≤ GeneralCK.Correction.Mdet p.1 p.2 :=
  correction_signs.2

end CKLaneA5.Assembly
