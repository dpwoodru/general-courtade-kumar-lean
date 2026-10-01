import CKLaneA1.FEStrip
import CKLaneA1.Bridge
import GeneralCK.CorrectionComplementCharts
import CKLaneA1.FEData.C000
import CKLaneA1.FEData.C001
import CKLaneA1.FEData.C002
import CKLaneA1.FEData.C003
import CKLaneA1.FEData.C004
import CKLaneA1.FEData.C005
import CKLaneA1.FEData.C006
import CKLaneA1.FEData.C007
import CKLaneA1.FEData.C008
import CKLaneA1.FEData.C009
import CKLaneA1.FEData.C010
import CKLaneA1.FEData.C011
import CKLaneA1.FEData.C012
import CKLaneA1.FEData.C013
import CKLaneA1.FEData.C014
import CKLaneA1.FEData.C015
import CKLaneA1.FEData.C016

/-!
# CKLaneA1.FEFinal — `ChartOwners.fixedEdge`, closed

The generated cover (`17` chunk modules, each checked by `decide +kernel` on the Boolean
checker `stripOK`) plus the one-time soundness theorem `fe_pointwise_of_cover` give pointwise
positivity of `m11` and of the gap coefficient on `0 < u ≤ 1/50`, `1/40 ≤ w < 1/2`; the bridge
below converts it to the exact `ChartOwners.fixedEdge` field type.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

def feStrips : List FEStrip := FEData.strips000 ++ FEData.strips001 ++ FEData.strips002 ++ FEData.strips003 ++ FEData.strips004 ++ FEData.strips005 ++ FEData.strips006 ++ FEData.strips007 ++ FEData.strips008 ++ FEData.strips009 ++ FEData.strips010 ++ FEData.strips011 ++ FEData.strips012 ++ FEData.strips013 ++ FEData.strips014 ++ FEData.strips015 ++ FEData.strips016

theorem feStrips_all : feStrips.all (stripOK 22 (ln2Iv 22)) = true := by
  simp only [feStrips, List.all_append, FEData.strips000_ok, FEData.strips001_ok, FEData.strips002_ok, FEData.strips003_ok, FEData.strips004_ok, FEData.strips005_ok, FEData.strips006_ok, FEData.strips007_ok, FEData.strips008_ok, FEData.strips009_ok, FEData.strips010_ok, FEData.strips011_ok, FEData.strips012_ok, FEData.strips013_ok, FEData.strips014_ok, FEData.strips015_ok, FEData.strips016_ok, Bool.and_self, Bool.true_and]

theorem feStrips_chain : chainOK 0 feStrips = true := by decide +kernel

theorem feStrips_last : decide (SCz ≤ 50 * lastU 0 feStrips) = true := by decide +kernel

theorem feStrips_ne : decide (feStrips ≠ []) = true := by decide +kernel

theorem feCover_ok : feCoverOK 22 feStrips = true := by
  unfold feCoverOK
  rw [feStrips_chain, feStrips_last, feStrips_ne, feStrips_all]
  all_goals rfl

/-- Pointwise positivity on the fixed-edge rectangle `0 < u ≤ 1/50`, `1/40 ≤ w < 1/2`. -/
theorem fixedEdge_pointwise : ∀ u w : ℝ, 0 < u → u ≤ 1/50 → 1/40 ≤ w → w < 1/2 →
    0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w :=
  fe_pointwise_of_cover feCover_ok

/-- **`ChartOwners.fixedEdge`**, with the exact field type. -/
theorem fixedEdge_field : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 → u ≤ 1 / 50 →
    1 / 40 ≤ u + rho * (1 / 2 - u) → GeneralCK.Correction.Complement.RatioSigns u rho := by
  intro u rho hu hu2 hr hr1 hu50 hw40
  have hw : u + rho * (1 / 2 - u) < 1 / 2 := by
    have : rho * (1 / 2 - u) < 1 * (1 / 2 - u) := mul_lt_mul_of_pos_right hr1 (by linarith)
    linarith
  obtain ⟨hc, hm⟩ := fixedEdge_pointwise u _ hu hu50 hw40 hw
  have hJ : 0 < jn u := jn_pos hu hu2
  have hcoef : 0 < actualDetGapCoefficient u (u + rho * (1 / 2 - u)) :=
    (mul_pos_iff_of_pos_left (one_div_pos.mpr hJ)).mp hc
  exact ratioSigns_of_pos hu hu2 hr hr1 hcoef.le hm

/-- Machine check that `fixedEdge_field` has exactly the `ChartOwners.fixedEdge` field type:
this structure update typechecks only if the types agree. -/
theorem withFixedEdge (c : GeneralCK.Correction.Complement.ChartOwners) :
    GeneralCK.Correction.Complement.ChartOwners :=
  { c with fixedEdge := fixedEdge_field }

#print axioms feCover_ok
#print axioms fixedEdge_pointwise
#print axioms fixedEdge_field

end CKLaneA1
