import CKLaneD.ArchTree
import CKLaneM10.Fleet.S0000
import CKLaneM10.Fleet.S0001
import CKLaneM10.Fleet.S0002
import CKLaneM10.Fleet.S0003
import CKLaneM10.Fleet.S0004
import CKLaneM10.Fleet.S0005
import CKLaneM10.Fleet.S0006
import CKLaneM10.Fleet.S0007
import CKLaneM10.Fleet.S0008
import CKLaneM10.Fleet.S0009
import CKLaneM10.Fleet.S0010
import CKLaneM10.Fleet.S0011
import CKLaneM10.Fleet.S0012
import CKLaneM10.Fleet.S0013
import CKLaneM10.Fleet.S0014
import CKLaneM10.Fleet.S0015
import CKLaneM10.Fleet.S0016
import CKLaneM10.Fleet.S0017
import CKLaneM10.Fleet.S0018
import CKLaneM10.Fleet.S0019
import CKLaneM10.Fleet.S0020
import CKLaneM10.Fleet.S0021
import CKLaneM10.Fleet.S0022
import CKLaneM10.Fleet.S0023
import CKLaneM10.Fleet.S0024
import CKLaneM10.Fleet.S0025
import CKLaneM10.Fleet.S0026
import CKLaneM10.Fleet.S0027
import CKLaneM10.Fleet.S0028
import CKLaneM10.Fleet.S0029
import CKLaneM10.Fleet.S0030
import CKLaneM10.Fleet.S0031
import CKLaneM10.Fleet.S0032
import CKLaneM10.Fleet.S0033
import CKLaneM10.Fleet.S0034
import CKLaneM10.Fleet.S0035
import CKLaneM10.Fleet.S0036
import CKLaneM10.Fleet.S0037
import CKLaneM10.Fleet.S0038
import CKLaneM10.Fleet.S0039
import CKLaneM10.Fleet.S0040
import CKLaneM10.Fleet.S0041
import CKLaneM10.Fleet.S0042
import CKLaneM10.Fleet.S0043
import CKLaneM10.Fleet.S0044
import CKLaneM10.Fleet.S0045
import CKLaneM10.Fleet.S0046
import CKLaneM10.Fleet.S0047
import CKLaneM10.Fleet.S0048
import CKLaneM10.Fleet.S0049
import CKLaneM10.Fleet.S0050
import CKLaneM10.Fleet.S0051
import CKLaneM10.Fleet.S0052
import CKLaneM10.Fleet.S0053
import CKLaneM10.Fleet.S0054
import CKLaneM10.Fleet.S0055
import CKLaneM10.Fleet.S0056
import CKLaneM10.Fleet.S0057
import CKLaneM10.Fleet.S0058
import CKLaneM10.Fleet.S0059
import CKLaneM10.Fleet.S0060
import CKLaneM10.Fleet.S0061
import CKLaneM10.Fleet.S0062
import CKLaneM10.Fleet.S0063
import CKLaneM10.Fleet.S0064
import CKLaneM10.Fleet.S0065
import CKLaneM10.Fleet.S0066
import CKLaneM10.Fleet.S0067
import CKLaneM10.Fleet.S0068
import CKLaneM10.Fleet.S0069
import CKLaneM10.Fleet.S0070
import CKLaneM10.Fleet.S0071
import CKLaneM10.Fleet.S0072
import CKLaneM10.Fleet.S0073
import CKLaneM10.Fleet.S0074
import CKLaneM10.Fleet.S0075
import CKLaneM10.Fleet.S0076
import CKLaneM10.Fleet.S0077

/-!
# Lane M10: aggregate over ALL archived `global_feasible_split` leaves

`feasibleSplit_leaves_sem`: for every leaf `q` of Lane D's archived outer-opposite tree
(`CKLaneD.ArchTree.archTree`, label `3 = global_feasible_split`), the psi-candidate Bellman inequality
holds for every interior law in the FULL physical image `InUVT (uvtBox q.1)` of the leaf (no entropy
clipping).  Each shard proves its leaves by the Boolean checker `checkLeafFS` (`decide +kernel`) and
`checkLeafFS_sound`; `fsPaths_eq` identifies the shard paths with the archived label-3 paths.
-/

namespace CKLaneM10.Leaves

open CKLaneD CKLaneM10

theorem sem_append {L1 L2 : List (List ℕ × FSWitness)}
    (h1 : ∀ x ∈ L1, SemUVT (uvtBox x.1)) (h2 : ∀ x ∈ L2, SemUVT (uvtBox x.1)) :
    ∀ x ∈ L1 ++ L2, SemUVT (uvtBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

/-- All shard witnesses, in archive (left-first DFS) order. -/
noncomputable def allLeaves : List (List ℕ × FSWitness) :=
    Fleet.S0000.leaves ++
    Fleet.S0001.leaves ++
    Fleet.S0002.leaves ++
    Fleet.S0003.leaves ++
    Fleet.S0004.leaves ++
    Fleet.S0005.leaves ++
    Fleet.S0006.leaves ++
    Fleet.S0007.leaves ++
    Fleet.S0008.leaves ++
    Fleet.S0009.leaves ++
    Fleet.S0010.leaves ++
    Fleet.S0011.leaves ++
    Fleet.S0012.leaves ++
    Fleet.S0013.leaves ++
    Fleet.S0014.leaves ++
    Fleet.S0015.leaves ++
    Fleet.S0016.leaves ++
    Fleet.S0017.leaves ++
    Fleet.S0018.leaves ++
    Fleet.S0019.leaves ++
    Fleet.S0020.leaves ++
    Fleet.S0021.leaves ++
    Fleet.S0022.leaves ++
    Fleet.S0023.leaves ++
    Fleet.S0024.leaves ++
    Fleet.S0025.leaves ++
    Fleet.S0026.leaves ++
    Fleet.S0027.leaves ++
    Fleet.S0028.leaves ++
    Fleet.S0029.leaves ++
    Fleet.S0030.leaves ++
    Fleet.S0031.leaves ++
    Fleet.S0032.leaves ++
    Fleet.S0033.leaves ++
    Fleet.S0034.leaves ++
    Fleet.S0035.leaves ++
    Fleet.S0036.leaves ++
    Fleet.S0037.leaves ++
    Fleet.S0038.leaves ++
    Fleet.S0039.leaves ++
    Fleet.S0040.leaves ++
    Fleet.S0041.leaves ++
    Fleet.S0042.leaves ++
    Fleet.S0043.leaves ++
    Fleet.S0044.leaves ++
    Fleet.S0045.leaves ++
    Fleet.S0046.leaves ++
    Fleet.S0047.leaves ++
    Fleet.S0048.leaves ++
    Fleet.S0049.leaves ++
    Fleet.S0050.leaves ++
    Fleet.S0051.leaves ++
    Fleet.S0052.leaves ++
    Fleet.S0053.leaves ++
    Fleet.S0054.leaves ++
    Fleet.S0055.leaves ++
    Fleet.S0056.leaves ++
    Fleet.S0057.leaves ++
    Fleet.S0058.leaves ++
    Fleet.S0059.leaves ++
    Fleet.S0060.leaves ++
    Fleet.S0061.leaves ++
    Fleet.S0062.leaves ++
    Fleet.S0063.leaves ++
    Fleet.S0064.leaves ++
    Fleet.S0065.leaves ++
    Fleet.S0066.leaves ++
    Fleet.S0067.leaves ++
    Fleet.S0068.leaves ++
    Fleet.S0069.leaves ++
    Fleet.S0070.leaves ++
    Fleet.S0071.leaves ++
    Fleet.S0072.leaves ++
    Fleet.S0073.leaves ++
    Fleet.S0074.leaves ++
    Fleet.S0075.leaves ++
    Fleet.S0076.leaves ++
    Fleet.S0077.leaves

theorem allLeaves_sem : ∀ x ∈ allLeaves, SemUVT (uvtBox x.1) :=
  sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (sem_append (Fleet.S0000.sem) Fleet.S0001.sem) Fleet.S0002.sem) Fleet.S0003.sem) Fleet.S0004.sem) Fleet.S0005.sem) Fleet.S0006.sem) Fleet.S0007.sem) Fleet.S0008.sem) Fleet.S0009.sem) Fleet.S0010.sem) Fleet.S0011.sem) Fleet.S0012.sem) Fleet.S0013.sem) Fleet.S0014.sem) Fleet.S0015.sem) Fleet.S0016.sem) Fleet.S0017.sem) Fleet.S0018.sem) Fleet.S0019.sem) Fleet.S0020.sem) Fleet.S0021.sem) Fleet.S0022.sem) Fleet.S0023.sem) Fleet.S0024.sem) Fleet.S0025.sem) Fleet.S0026.sem) Fleet.S0027.sem) Fleet.S0028.sem) Fleet.S0029.sem) Fleet.S0030.sem) Fleet.S0031.sem) Fleet.S0032.sem) Fleet.S0033.sem) Fleet.S0034.sem) Fleet.S0035.sem) Fleet.S0036.sem) Fleet.S0037.sem) Fleet.S0038.sem) Fleet.S0039.sem) Fleet.S0040.sem) Fleet.S0041.sem) Fleet.S0042.sem) Fleet.S0043.sem) Fleet.S0044.sem) Fleet.S0045.sem) Fleet.S0046.sem) Fleet.S0047.sem) Fleet.S0048.sem) Fleet.S0049.sem) Fleet.S0050.sem) Fleet.S0051.sem) Fleet.S0052.sem) Fleet.S0053.sem) Fleet.S0054.sem) Fleet.S0055.sem) Fleet.S0056.sem) Fleet.S0057.sem) Fleet.S0058.sem) Fleet.S0059.sem) Fleet.S0060.sem) Fleet.S0061.sem) Fleet.S0062.sem) Fleet.S0063.sem) Fleet.S0064.sem) Fleet.S0065.sem) Fleet.S0066.sem) Fleet.S0067.sem) Fleet.S0068.sem) Fleet.S0069.sem) Fleet.S0070.sem) Fleet.S0071.sem) Fleet.S0072.sem) Fleet.S0073.sem) Fleet.S0074.sem) Fleet.S0075.sem) Fleet.S0076.sem) Fleet.S0077.sem

/-- The archived `global_feasible_split` leaf paths (label 3), in archive order. -/
def fsPaths : List (List ℕ) :=
  (ArchTree.archTree.leaves.filter (fun x => x.2 = 3)).map Prod.fst

theorem fsPaths_eq : fsPaths = allLeaves.map Prod.fst := by decide +kernel

theorem allLeaves_length : allLeaves.length = 1872 := by decide +kernel

theorem fsPaths_length : fsPaths.length = 1872 := by
  rw [fsPaths_eq, List.length_map, allLeaves_length]

/-- MAIN (Lane G interface): every archived `global_feasible_split` leaf, full physical image. -/
theorem feasibleSplit_leaves_sem :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 3 → SemUVT (uvtBox q.1) := by
  intro q hq h3
  have hmem : q.1 ∈ fsPaths :=
    List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simp [h3]⟩, rfl⟩
  rw [fsPaths_eq] at hmem
  obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hmem
  rw [← hxq]
  exact allLeaves_sem x hx

/-- Owner form (psi-active branch) for Lane G. -/
theorem feasibleSplit_leaves_gap_le_cost :
    ∀ q ∈ ArchTree.archTree.leaves, q.2 = 3 → ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
      InUVT (uvtBox q.1) μ.a μ.b μ.meanEntropy →
      GeneralCK.phi μ.midpoint μ.meanEntropy ≤ GeneralCK.psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro q hq h3 k μ hin hact
  exact semUVT_gap_le_cost (feasibleSplit_leaves_sem q hq h3) μ hin hact

end CKLaneM10.Leaves
