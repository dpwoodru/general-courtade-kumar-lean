import CKLaneM2.FleetAll
import CKLaneD.OCompact

/-!
# Lane M2b: the archived `shifted_logsum` leaf family of the (O) tree

`shifted_logsum_leaves`: every leaf `q` of the archived outer-opposite tree `CKLaneD.ArchTree.archTree`
with owner label 1 (`shifted_logsum`; 7,056 leaves) satisfies the psi-candidate Bellman statement
`CKLaneD.SemUVT` on its FULL archived physical image `InUVT (uvtBox q.1)` (a = 2^-u, b = 1 - 2^-v,
clipped by a ≤ 1/10 and a + b ≤ 1, E between the t0/t1 levels EMIN + t (C0 - EMIN)).
No E ≤ 1/25 delegation is used (the 3 archive-delegated leaves are certified directly).
-/

namespace CKLaneM2.Leaves

open CKLaneD

/-- All 7,056 archived `shifted_logsum` leaves (label 1) of the archived (O) tree. -/
theorem shifted_logsum_leaves :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 1 → SemUVT (uvtBox q.1) := by
  intro q hq hl
  apply FleetAll.fleet_sl_sem
  unfold FleetAll.slPaths
  exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa using hl⟩, rfl⟩

/-- The same family in the OP_Compact-row leaf form. -/
theorem shifted_logsum_oLeafOK :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 1 → OCompact.OLeafOK (uvtBox q.1) :=
  fun q hq hl => OCompact.oLeafOK_of_semUVT _ (shifted_logsum_leaves q hq hl)

/-- The label-1 family has exactly 7,056 leaves. -/
theorem shifted_logsum_leaf_count :
    (ArchTree.archTree.leaves.filter (fun x => x.2 = 1)).length = 7056 := by
  have h := FleetAll.slPaths_length
  unfold FleetAll.slPaths at h
  simpa using h

end CKLaneM2.Leaves
