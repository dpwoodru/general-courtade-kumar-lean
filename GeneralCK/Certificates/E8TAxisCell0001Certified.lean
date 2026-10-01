import GeneralCK.Certificates.E8TAxisCell0001Sub0Certified
import GeneralCK.Certificates.E8TAxisCell0001Sub1Certified

/-! The weak second positive historical t-axis rectangle, certified after one
exact midpoint refinement in the s direction. -/

namespace GeneralCK.Certificates.E8TAxisCell0001Certified

open E8TAxisPartitionKernel

noncomputable def rectangle : Rect :=
  { s0 := 3 / 50
    s1 := E8TAxisOneCellGeometry.sLower
    t0 := E8TAxisOneCellGeometry.tLower
    t1 := 1 / 50 }

def split : ℚ :=
  25500000000000000000000000000000000000000000000000000000000637236764453 /
    400000000000000000000000000000000000000000000000000000000000000000000000

def tree : Tree := .splitS split .leaf .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  refine ⟨by norm_num [rectangle, split, E8TAxisOneCellGeometry.sLower],
    by norm_num [rectangle, split, E8TAxisOneCellGeometry.sLower], ?_, ?_⟩
  · change CellPositive (rectangle.leftS split)
    simpa [rectangle, split, Rect.leftS,
      E8TAxisCell0001Sub0Geometry.rectangle,
      E8TAxisCell0001Sub0Geometry.sLower, E8TAxisCell0001Sub0Geometry.sUpper,
      E8TAxisCell0001Sub0Geometry.tLower, E8TAxisCell0001Sub0Geometry.tUpper,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower] using
      E8TAxisCell0001Sub0Certified.cellPositive
  · change CellPositive (rectangle.rightS split)
    simpa [rectangle, split, Rect.rightS,
      E8TAxisCell0001Sub1Geometry.rectangle,
      E8TAxisCell0001Sub1Geometry.sLower, E8TAxisCell0001Sub1Geometry.sUpper,
      E8TAxisCell0001Sub1Geometry.tLower, E8TAxisCell0001Sub1Geometry.tUpper,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower] using
      E8TAxisCell0001Sub1Certified.cellPositive

theorem cellPositive : CellPositive rectangle := by
  intro s t hadm h
  obtain ⟨leaf, hp, hc⟩ := locate_leaf allLeaves h
  exact hp s t hadm hc

#print axioms allLeaves
#print axioms cellPositive

end GeneralCK.Certificates.E8TAxisCell0001Certified
