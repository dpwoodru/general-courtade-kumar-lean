import CKLaneM07.Checker

/-! M07 derivative leaves (archived same-side owner `derivative`), shard `FleetT.T0032`.
Witnesses only propose rationals; `checkLeaf` recomputes every enclosure. -/

set_option maxRecDepth 100000

namespace CKLaneM07.FleetT.T0032
open CKLaneM07

def L : List (List ℕ × Wit) := [
  ([5,0,2,0,3,0,0,0,5,2,1,2,5,1,3,5,0,3,5,0,2], ⟨dy (656466953106431027) 60, dy (685531228159052439) 60, dy (316335127509405831) 60, dy (1819330227579079) 52⟩),
  ([5,0,2,0,3,0,0,0,5,2,1,2,5,1,3,5,0,3,5,0,3], ⟨dy (656466953106431027) 60, dy (685531228159052439) 60, dy (316335127509405831) 60, dy (14526181306955939) 55⟩),
  ([5,0,2,0,3,0,0,0,5,2,1,2,5,1,3,5,0,3,5,1,3,5], ⟨dy (314317453982457527) 59, dy (164116738276607757) 58, dy (339288325410392369) 60, dy (15079848049683813) 55⟩),
  ([5,0,2,0,3,0,0,0,5,2,1,3,5,1,2,5,0,2,5,1,2,5], ⟨dy (314317453982457527) 59, dy (164116738276607757) 58, dy (339288325410392369) 60, dy (30106020282153643) 56⟩),
  ([5,0,2,0,3,0,0,0,5,2,1,3,5,1,2,5,0,2,5,1,3,5], ⟨dy (314317453982457527) 59, dy (164116738276607757) 58, dy (339288325410392369) 60, dy (1878301788940621) 52⟩)
]

theorem L_check : (L.all fun x => checkLeaf x.1 x.2) = true := by decide +kernel

theorem L_sound : ∀ x ∈ L, SemSBox (ssBox x.1) := checkLeaves_sound L L_check

end CKLaneM07.FleetT.T0032
