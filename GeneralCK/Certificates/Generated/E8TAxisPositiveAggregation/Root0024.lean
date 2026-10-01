import GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
import GeneralCK.Certificates.E8TAxisProd0024LCertified
import GeneralCK.Certificates.E8TAxisProd0024RCertified

/-! Generated local positive-t aggregation. No full-domain assertion. -/
namespace GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0024
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisPositiveAggregationKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable def rectangle : Rect := ⟨(1 / 10 : ℝ), (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)⟩
def tree : Tree := (.splitS (5468750000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) .leaf .leaf)

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  simp only [tree, AllLeaves, rectangle, Rect.leftS, Rect.rightS, Rect.lowerT, Rect.upperT]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  ·
    convert E8TAxisProd0024LCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0024LGeometry.rectangle, E8TAxisProd0024LGeometry.sLower, E8TAxisProd0024LGeometry.sUpper, E8TAxisProd0024LGeometry.tLower, E8TAxisProd0024LGeometry.tUpper]
  ·
    convert E8TAxisProd0024RCertified.cellPositive using 1 <;>
      norm_num [E8TAxisProd0024RGeometry.rectangle, E8TAxisProd0024RGeometry.sLower, E8TAxisProd0024RGeometry.sUpper, E8TAxisProd0024RGeometry.tLower, E8TAxisProd0024RGeometry.tUpper]

theorem cellPositive : CellPositive rectangle := cellPositive_of_allLeaves allLeaves

#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0024
