import GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
import GeneralCK.Certificates.E8TAxisProd0074LCertified
import GeneralCK.Certificates.E8TAxisProd0074RCertified

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0074
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0074LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0074LGeometry.rectangle, E8TAxisProd0074LGeometry.sLower, E8TAxisProd0074LGeometry.sUpper, E8TAxisProd0074LGeometry.tLower, E8TAxisProd0074LGeometry.tUpper]
  ·
    convert E8TAxisProd0074RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0074RGeometry.rectangle, E8TAxisProd0074RGeometry.sLower, E8TAxisProd0074RGeometry.sUpper, E8TAxisProd0074RGeometry.tLower, E8TAxisProd0074RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0074
