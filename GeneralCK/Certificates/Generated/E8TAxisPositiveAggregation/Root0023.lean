import GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
import GeneralCK.Certificates.E8TAxisProd0023LCertified
import GeneralCK.Certificates.E8TAxisProd0023RCertified

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0023
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 10 : ℝ), (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (5468750000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0023LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0023LGeometry.rectangle, E8TAxisProd0023LGeometry.sLower, E8TAxisProd0023LGeometry.sUpper, E8TAxisProd0023LGeometry.tLower, E8TAxisProd0023LGeometry.tUpper]
  ·
    convert E8TAxisProd0023RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0023RGeometry.rectangle, E8TAxisProd0023RGeometry.sLower, E8TAxisProd0023RGeometry.sUpper, E8TAxisProd0023RGeometry.tLower, E8TAxisProd0023RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0023
