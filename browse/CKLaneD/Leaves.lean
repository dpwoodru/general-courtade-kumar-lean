import CKLaneD.FleetAll
import CKLaneD.OCompact

/-!
# Lane D: the archived `endpoint_plane_taylor` leaf family of the (O) tree

`endpoint_leaves`: every leaf `q` of the archived outer-opposite tree with owner label 0
(`endpoint_plane_taylor`; 16,491 leaves) satisfies the psi-candidate Bellman statement on its full
archived physical image `InUVT (uvtBox q.1)`.
-/

namespace CKLaneD.Leaves

open CKLaneD

/-- All 16,491 archived `endpoint_plane_taylor` leaves (label 0) of the archived (O) tree. -/
theorem endpoint_leaves : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 0 → SemUVT (uvtBox q.1) := by
  intro q hq hl
  apply FleetAll.fleet_endpoint_sem
  unfold ArchTree.endpointPaths
  exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa using hl⟩, rfl⟩

/-- The same family in the OP_Compact-row leaf form. -/
theorem endpoint_oLeafOK :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 0 → OCompact.OLeafOK (uvtBox q.1) :=
  fun q hq hl => OCompact.oLeafOK_of_semUVT _ (endpoint_leaves q hq hl)

/-- The label-0 family has exactly 16,491 leaves. -/
theorem endpoint_leaf_count :
    (ArchTree.archTree.leaves.filter (fun x => x.2 = 0)).length = 16491 := by
  have h := ArchTree.endpointPaths_length
  unfold ArchTree.endpointPaths at h
  simpa using h

end CKLaneD.Leaves
