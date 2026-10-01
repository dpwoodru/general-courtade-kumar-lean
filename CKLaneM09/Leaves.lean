import CKLaneM09.Fleet.S0000
import CKLaneM09.Fleet.S0001
import CKLaneM09.Fleet.S0002
import CKLaneM09.Fleet.S0003
import CKLaneM09.Fleet.S0004
import CKLaneM09.Fleet.S0005
import CKLaneM09.Fleet.S0006
import CKLaneM09.Fleet.S0007
import CKLaneM09.Fleet.S0008
import CKLaneM09.Fleet.S0009
import CKLaneM09.Fleet.S0010
import CKLaneM09.Fleet.S0011
import CKLaneM09.Fleet.S0012
import CKLaneM09.Fleet.S0013
import CKLaneM09.Fleet.S0014
import CKLaneM09.Fleet.S0015
import CKLaneM09.Fleet.S0016
import CKLaneM09.Fleet.S0017
import CKLaneM09.Fleet.S0018
import CKLaneM09.Fleet.S0019
import CKLaneM09.Fleet.S0020
import CKLaneM09.Fleet.S0021
import CKLaneM09.Fleet.S0022
import CKLaneM09.Fleet.S0023
import CKLaneM09.Fleet.S0024
import CKLaneM09.Fleet.S0025
import CKLaneM09.Fleet.S0026
import CKLaneM09.Fleet.S0027
import CKLaneM09.Fleet.S0028
import CKLaneM09.Fleet.S0029
import CKLaneM09.Fleet.S0030
import CKLaneM09.Fleet.S0031
import CKLaneM09.Fleet.S0032
import CKLaneM09.Fleet.S0033
import CKLaneM09.Fleet.S0034
import CKLaneM09.Fleet.S0035
import CKLaneM09.Fleet.S0036
import CKLaneM09.Fleet.S0037
import CKLaneM09.Fleet.S0038
import CKLaneM09.Fleet.S0039
import CKLaneM09.Fleet.S0040
import CKLaneM09.Fleet.S0041
import CKLaneD.ArchTree

/-!
# Lane M09 aggregate: every archived `global_cap_slope` leaf

2093 leaves (label 2 of `CKLaneD.ArchTree.archTree`, generated from
OUTER_OPPOSITE_RESULT.json sha256 44344386e10adb6f6bdd066d7fbe4056ab2c10164019c0d9dce378a2e9edf72d), 42 kernel-checked shards.
`cap_slope_leaves`: for every archived leaf with label 2, the psi-candidate Bellman inequality
holds on the exact clipped physical image of the leaf (`CKLaneD.SemUVT`), with no hypothesis
other than law membership in that image.
-/

set_option autoImplicit false

namespace CKLaneM09.Leaves

open CKLaneD CKLaneM09 GeneralCK

noncomputable def allLeaves : List (List ℕ × CapWitness) :=
  Fleet.S0000.leaves ++
  (Fleet.S0001.leaves ++
  (Fleet.S0002.leaves ++
  (Fleet.S0003.leaves ++
  (Fleet.S0004.leaves ++
  (Fleet.S0005.leaves ++
  (Fleet.S0006.leaves ++
  (Fleet.S0007.leaves ++
  (Fleet.S0008.leaves ++
  (Fleet.S0009.leaves ++
  (Fleet.S0010.leaves ++
  (Fleet.S0011.leaves ++
  (Fleet.S0012.leaves ++
  (Fleet.S0013.leaves ++
  (Fleet.S0014.leaves ++
  (Fleet.S0015.leaves ++
  (Fleet.S0016.leaves ++
  (Fleet.S0017.leaves ++
  (Fleet.S0018.leaves ++
  (Fleet.S0019.leaves ++
  (Fleet.S0020.leaves ++
  (Fleet.S0021.leaves ++
  (Fleet.S0022.leaves ++
  (Fleet.S0023.leaves ++
  (Fleet.S0024.leaves ++
  (Fleet.S0025.leaves ++
  (Fleet.S0026.leaves ++
  (Fleet.S0027.leaves ++
  (Fleet.S0028.leaves ++
  (Fleet.S0029.leaves ++
  (Fleet.S0030.leaves ++
  (Fleet.S0031.leaves ++
  (Fleet.S0032.leaves ++
  (Fleet.S0033.leaves ++
  (Fleet.S0034.leaves ++
  (Fleet.S0035.leaves ++
  (Fleet.S0036.leaves ++
  (Fleet.S0037.leaves ++
  (Fleet.S0038.leaves ++
  (Fleet.S0039.leaves ++
  (Fleet.S0040.leaves ++
  (Fleet.S0041.leaves)))))))))))))))))))))))))))))))))))))))))

theorem forall_mem_append_of {L1 L2 : List (List ℕ × CapWitness)}
    (h1 : ∀ x ∈ L1, SemUVT (uvtBox x.1)) (h2 : ∀ x ∈ L2, SemUVT (uvtBox x.1)) :
    ∀ x ∈ L1 ++ L2, SemUVT (uvtBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

theorem allLeaves_sem : ∀ x ∈ allLeaves, SemUVT (uvtBox x.1) :=
  forall_mem_append_of Fleet.S0000.sem
    (forall_mem_append_of Fleet.S0001.sem
    (forall_mem_append_of Fleet.S0002.sem
    (forall_mem_append_of Fleet.S0003.sem
    (forall_mem_append_of Fleet.S0004.sem
    (forall_mem_append_of Fleet.S0005.sem
    (forall_mem_append_of Fleet.S0006.sem
    (forall_mem_append_of Fleet.S0007.sem
    (forall_mem_append_of Fleet.S0008.sem
    (forall_mem_append_of Fleet.S0009.sem
    (forall_mem_append_of Fleet.S0010.sem
    (forall_mem_append_of Fleet.S0011.sem
    (forall_mem_append_of Fleet.S0012.sem
    (forall_mem_append_of Fleet.S0013.sem
    (forall_mem_append_of Fleet.S0014.sem
    (forall_mem_append_of Fleet.S0015.sem
    (forall_mem_append_of Fleet.S0016.sem
    (forall_mem_append_of Fleet.S0017.sem
    (forall_mem_append_of Fleet.S0018.sem
    (forall_mem_append_of Fleet.S0019.sem
    (forall_mem_append_of Fleet.S0020.sem
    (forall_mem_append_of Fleet.S0021.sem
    (forall_mem_append_of Fleet.S0022.sem
    (forall_mem_append_of Fleet.S0023.sem
    (forall_mem_append_of Fleet.S0024.sem
    (forall_mem_append_of Fleet.S0025.sem
    (forall_mem_append_of Fleet.S0026.sem
    (forall_mem_append_of Fleet.S0027.sem
    (forall_mem_append_of Fleet.S0028.sem
    (forall_mem_append_of Fleet.S0029.sem
    (forall_mem_append_of Fleet.S0030.sem
    (forall_mem_append_of Fleet.S0031.sem
    (forall_mem_append_of Fleet.S0032.sem
    (forall_mem_append_of Fleet.S0033.sem
    (forall_mem_append_of Fleet.S0034.sem
    (forall_mem_append_of Fleet.S0035.sem
    (forall_mem_append_of Fleet.S0036.sem
    (forall_mem_append_of Fleet.S0037.sem
    (forall_mem_append_of Fleet.S0038.sem
    (forall_mem_append_of Fleet.S0039.sem
    (forall_mem_append_of Fleet.S0040.sem
    (Fleet.S0041.sem)))))))))))))))))))))))))))))))))))))))))

/-- The archived `global_cap_slope` leaf paths (label 2), in tree order. -/
def capPaths : List (List ℕ) :=
  (ArchTree.archTree.leaves.filter (fun x => x.2 = 2)).map Prod.fst

theorem allLeaves_length : allLeaves.length = 2093 := by decide +kernel

/-- The shard paths are exactly the archived `global_cap_slope` leaves. -/
theorem paths_eq : capPaths = allLeaves.map Prod.fst := by decide +kernel

theorem capPaths_length : capPaths.length = 2093 := by
  rw [paths_eq, List.length_map, allLeaves_length]

theorem cap_slope_sem : ∀ p ∈ capPaths, SemUVT (uvtBox p) := by
  intro p hp
  rw [paths_eq] at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact allLeaves_sem x hx

/-- Lane G entry point: every archived leaf with owner label 2 (`global_cap_slope`). -/
theorem cap_slope_leaves : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 2 → SemUVT (uvtBox q.1) := by
  intro q hq hl
  apply cap_slope_sem
  exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simpa using hl⟩, rfl⟩

/-- Owner form on every archived `global_cap_slope` leaf (psi weakly active at the parent). -/
theorem cap_slope_gap : ∀ q ∈ ArchTree.archTree.leaves, q.2 = 2 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InUVT (uvtBox q.1) μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost := by
  intro q hq hl k μ hin hact
  exact (hybrid_gap_le_psi hact).trans (cap_slope_leaves q hq hl k μ hin)

end CKLaneM09.Leaves
