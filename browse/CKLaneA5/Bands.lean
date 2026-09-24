import GeneralCK.Certificates.RB1Band1.Coverage
import GeneralCK.LaneRB2OwnerActual
import GeneralCK.CorrectionComplementCharts

/-!
# Lane A5: the two certified bands in the exact form consumed by `orderedTriangle_signs_of_charts`

* `band1_actual` (= `hC1`): Lane R-B1's generated exact cover `GeneralCK.Certificates.RB1Band1.coverage`
  (5,891 compiled cells over `u ∈ [1/50, 1/10]`, `rho ∈ [3/40, 1]`, strict minors), eta-expanded from its
  ordinary-implicit binders to the strict-implicit binders of `ActualRatioFamilyOn`.
* `band2_actual` (= `hC2`): Lane R-B2's `GeneralCK.Certificates.LaneRB2Owner.hC2_actual`
  (11,784 compiled cells, `u ∈ [1/10, 1/5]`, `rho ∈ [1/10, 1]`).

Provider: private merged root `A/asmroot5` = F-C root (cp -al) + the R-B1/R-B2 farm modules the F-C root lacks
(manifest `A/a5/asmroot5_manifest.tsv`; every shared module byte-identical to F-C, 0 conflicts).
-/

namespace CKLaneA5.Bands

open GeneralCK GeneralCK.Correction

/-- `hC1 : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1`, from R-B1's compiled cover. -/
theorem band1_actual : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1 :=
  fun _ _ hu hr hr1 => GeneralCK.Certificates.RB1Band1.coverage hu hr hr1

/-- `hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1`, R-B2's strict owner re-exported. -/
theorem band2_actual : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1 :=
  GeneralCK.Certificates.LaneRB2Owner.hC2_actual

end CKLaneA5.Bands
