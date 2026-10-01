import GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
import GeneralCK.Certificates.E8TAxisProd0087LCertified
import GeneralCK.Certificates.E8TAxisProd0087RCertified

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0087
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(9 / 16 : ℝ), (5 / 8 : ℝ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (19 / 32 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0087LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0087LGeometry.rectangle, E8TAxisProd0087LGeometry.sLower, E8TAxisProd0087LGeometry.sUpper, E8TAxisProd0087LGeometry.tLower, E8TAxisProd0087LGeometry.tUpper]
  ·
    convert E8TAxisProd0087RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0087RGeometry.rectangle, E8TAxisProd0087RGeometry.sLower, E8TAxisProd0087RGeometry.sUpper, E8TAxisProd0087RGeometry.tLower, E8TAxisProd0087RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0087
