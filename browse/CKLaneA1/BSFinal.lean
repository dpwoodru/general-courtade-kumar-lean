import CKLaneA1.BSCover
import CKLaneA1.Bridge
import GeneralCK.CorrectionComplementCharts
import CKLaneA1.BSData.C000
import CKLaneA1.BSData.C001
import CKLaneA1.BSData.C002
import CKLaneA1.BSData.C003
import CKLaneA1.BSData.C004
import CKLaneA1.BSData.C005
import CKLaneA1.BSData.C006
import CKLaneA1.BSData.C007
import CKLaneA1.BSData.C008

/-!
# CKLaneA1.BSFinal — `ChartOwners.bothSmall`, closed

The generated `(w, u/w)` cover (`9` chunk modules, each checked by `decide +kernel` on the
Boolean checker `bsStripFull`) plus the one-time soundness theorem `bs_pointwise_of_cover` give
pointwise positivity of `m11` and of the gap coefficient on `0 < u < w ≤ 1/40`; the bridge below
converts it to the exact `ChartOwners.bothSmall` field type.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

def bsStrips : List BSStrip := BSData.bstrips000 ++ BSData.bstrips001 ++ BSData.bstrips002 ++ BSData.bstrips003 ++ BSData.bstrips004 ++ BSData.bstrips005 ++ BSData.bstrips006 ++ BSData.bstrips007 ++ BSData.bstrips008

theorem bsStrips_all : bsStrips.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bsStrips, List.all_append, BSData.bstrips000_ok, BSData.bstrips001_ok, BSData.bstrips002_ok, BSData.bstrips003_ok, BSData.bstrips004_ok, BSData.bstrips005_ok, BSData.bstrips006_ok, BSData.bstrips007_ok, BSData.bstrips008_ok, Bool.and_self, Bool.true_and]

theorem bsStrips_chain : bsChainOK 0 bsStrips = true := by decide +kernel

theorem bsStrips_last : decide (SCz ≤ 40 * bsLastW 0 bsStrips) = true := by decide +kernel

theorem bsStrips_ne : decide (bsStrips ≠ []) = true := by decide +kernel

theorem bsCover_ok : bsCoverOK 22 bsStrips = true := by
  unfold bsCoverOK
  rw [bsStrips_chain, bsStrips_last, bsStrips_ne, bsStrips_all]
  all_goals rfl

/-- Pointwise positivity on the both-small triangle `0 < u < w ≤ 1/40`. -/
theorem bothSmall_pointwise : ∀ u w : ℝ, 0 < u → u < w → w ≤ 1/40 →
    0 < actualDetGapCoefficient u w ∧ 0 < m11 u w :=
  bs_pointwise_of_cover bsCover_ok

/-- **`ChartOwners.bothSmall`**, with the exact field type. -/
theorem bothSmall_field : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    u + rho * (1 / 2 - u) ≤ 1 / 40 → GeneralCK.Correction.Complement.RatioSigns u rho := by
  intro u rho hu hu2 hr hr1 hw40
  have hgap : 0 < rho * (1 / 2 - u) := mul_pos hr (by linarith)
  have huw : u < u + rho * (1 / 2 - u) := by linarith
  obtain ⟨hcoef, hm⟩ := bothSmall_pointwise u _ hu huw hw40
  exact ratioSigns_of_pos hu hu2 hr hr1 hcoef.le hm

/-- Machine check that `bothSmall_field` has exactly the `ChartOwners.bothSmall` field type. -/
theorem withBothSmall (c : GeneralCK.Correction.Complement.ChartOwners) :
    GeneralCK.Correction.Complement.ChartOwners :=
  { c with bothSmall := bothSmall_field }

#print axioms bsCover_ok
#print axioms bothSmall_pointwise
#print axioms bothSmall_field

end CKLaneA1
