import CKLaneN1b.Fleet.S0000
import CKLaneN1b.Fleet.S0001
import CKLaneN1b.Fleet.S0002
import CKLaneN1b.Fleet.S0003
import CKLaneN1b.Fleet.S0004
import CKLaneN1b.Fleet.S0005
import CKLaneN1b.Fleet.S0006
import CKLaneN1b.Fleet.S0007
import CKLaneN1b.Fleet.S0008
import CKLaneN1b.Fleet.S0009
import CKLaneN1b.Fleet.S0010
import CKLaneN1b.Fleet.S0011
import CKLaneN1b.Fleet.S0012
import CKLaneN1b.Fleet.S0013
import CKLaneN1b.Fleet.S0014
import CKLaneN1b.Fleet.S0015
import CKLaneN1b.Fleet.S0016
import CKLaneN1b.Fleet.S0017
import CKLaneN1b.Fleet.S0018
import CKLaneN1b.Fleet.S0019
import CKLaneN1b.Fleet.S0020
import CKLaneN1b.Fleet.S0021
import CKLaneN1b.Fleet.S0022
import CKLaneN1b.Fleet.S0023
import CKLaneN1b.Fleet.S0024
import CKLaneN1b.Fleet.S0025
import CKLaneN1b.Fleet.S0026
import CKLaneN1b.Fleet.S0027
import CKLaneN1b.Fleet.S0028
import CKLaneN1b.Fleet.S0029
import CKLaneN1b.Fleet.S0030
import CKLaneN1b.Fleet.S0031
import CKLaneN1b.Fleet.S0032
import CKLaneN1b.Fleet.S0033
import CKLaneN1b.Fleet.S0034
import CKLaneN1b.Fleet.S0035
import CKLaneN1b.Fleet.S0036
import CKLaneN1b.Fleet.S0037
import CKLaneN1b.Fleet.S0038
import CKLaneN1b.Fleet.S0039
import CKLaneN1b.Fleet.S0040
import CKLaneN1b.Fleet.S0041
import CKLaneN1b.Fleet.S0042
import CKLaneN1b.Fleet.S0043
import CKLaneN1b.Fleet.S0044
import CKLaneN1b.Fleet.S0045
import CKLaneN1b.Fleet.S0046
import CKLaneN1b.Fleet.S0047
import CKLaneN1b.Fleet.S0048
import CKLaneN1b.Fleet.S0049
import CKLaneN1b.Fleet.S0050
import CKLaneN1b.Fleet.S0051
import CKLaneN1b.Fleet.S0052
import CKLaneN1b.Fleet.S0053
import CKLaneN1b.Fleet.S0054
import CKLaneN1b.Fleet.S0055
import CKLaneN1b.Fleet.S0056
import CKLaneN1b.Fleet.S0057
import CKLaneN1b.Fleet.S0058
import CKLaneN1b.Fleet.S0059
import CKLaneN1b.Fleet.S0060
import CKLaneN1b.Fleet.S0061
import CKLaneN1b.Fleet.S0062
import CKLaneN1b.Fleet.S0063
import CKLaneN1b.Fleet.S0064
import CKLaneN1b.Fleet.S0065
import CKLaneN1b.Fleet.S0066
import CKLaneN1b.Fleet.S0067
import CKLaneN1b.Fleet.S0068
import CKLaneN1b.Fleet.S0069
import CKLaneN1b.Fleet.S0070
import CKLaneN1b.Fleet.S0071
import CKLaneN1b.Fleet.S0072
import CKLaneN1b.Fleet.S0073
import CKLaneN1b.Fleet.S0074
import CKLaneN1b.Fleet.S0075
import CKLaneN1b.Fleet.S0076
import CKLaneN1b.Fleet.S0077
import CKLaneN1b.Fleet.S0078
import CKLaneN1b.Fleet.S0079
import CKLaneN1b.Fleet.S0080
import CKLaneN1b.Fleet.S0081
import CKLaneN1b.Fleet.S0082
import CKLaneN1b.Fleet.S0083
import CKLaneN1b.Fleet.S0084
import CKLaneN1b.Fleet.S0085
import CKLaneN1b.Fleet.S0086
import CKLaneN1b.Fleet.S0087
import CKLaneN1b.Fleet.S0088
import CKLaneN1b.Fleet.S0089
import CKLaneN1b.Fleet.S0090
import CKLaneN1b.Fleet.S0091
import CKLaneN1b.Fleet.S0092
import CKLaneN1b.Fleet.S0093
import CKLaneN1b.Fleet.S0094
import CKLaneN1b.Fleet.S0095
import CKLaneN1b.Fleet.S0096
import CKLaneN1b.Fleet.S0097
import CKLaneN1b.Fleet.S0098
import CKLaneN1b.Fleet.S0099
import CKLaneN1b.Fleet.S0100
import CKLaneN1b.Fleet.S0101
import CKLaneN1b.Fleet.S0102
import CKLaneN1b.Fleet.S0103
import CKLaneN1b.Fleet.S0104
import CKLaneN1b.Cover

/-!
# Lane N1b: the family theorem over all 4730 archived leaves

`allPaths` concatenates the path lists of the 105 fleet shards; each shard proves `Sem (boxOf p)`
for its paths with kernel-checked certificates (`checkCert_sound`, `decide +kernel`).
`allPaths_eq` (kernel evaluation) identifies `allPaths` with the archived tree's leaf list, so
`family` holds for every archived leaf `q` of `modTree`, whatever its owner label (the six
`outside` leaves are certified irrelevant, not dropped).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

def allPaths : List (List ℕ) :=
    Fleet.S0000.paths ++
    (Fleet.S0001.paths ++
    (Fleet.S0002.paths ++
    (Fleet.S0003.paths ++
    (Fleet.S0004.paths ++
    (Fleet.S0005.paths ++
    (Fleet.S0006.paths ++
    (Fleet.S0007.paths ++
    (Fleet.S0008.paths ++
    (Fleet.S0009.paths ++
    (Fleet.S0010.paths ++
    (Fleet.S0011.paths ++
    (Fleet.S0012.paths ++
    (Fleet.S0013.paths ++
    (Fleet.S0014.paths ++
    (Fleet.S0015.paths ++
    (Fleet.S0016.paths ++
    (Fleet.S0017.paths ++
    (Fleet.S0018.paths ++
    (Fleet.S0019.paths ++
    (Fleet.S0020.paths ++
    (Fleet.S0021.paths ++
    (Fleet.S0022.paths ++
    (Fleet.S0023.paths ++
    (Fleet.S0024.paths ++
    (Fleet.S0025.paths ++
    (Fleet.S0026.paths ++
    (Fleet.S0027.paths ++
    (Fleet.S0028.paths ++
    (Fleet.S0029.paths ++
    (Fleet.S0030.paths ++
    (Fleet.S0031.paths ++
    (Fleet.S0032.paths ++
    (Fleet.S0033.paths ++
    (Fleet.S0034.paths ++
    (Fleet.S0035.paths ++
    (Fleet.S0036.paths ++
    (Fleet.S0037.paths ++
    (Fleet.S0038.paths ++
    (Fleet.S0039.paths ++
    (Fleet.S0040.paths ++
    (Fleet.S0041.paths ++
    (Fleet.S0042.paths ++
    (Fleet.S0043.paths ++
    (Fleet.S0044.paths ++
    (Fleet.S0045.paths ++
    (Fleet.S0046.paths ++
    (Fleet.S0047.paths ++
    (Fleet.S0048.paths ++
    (Fleet.S0049.paths ++
    (Fleet.S0050.paths ++
    (Fleet.S0051.paths ++
    (Fleet.S0052.paths ++
    (Fleet.S0053.paths ++
    (Fleet.S0054.paths ++
    (Fleet.S0055.paths ++
    (Fleet.S0056.paths ++
    (Fleet.S0057.paths ++
    (Fleet.S0058.paths ++
    (Fleet.S0059.paths ++
    (Fleet.S0060.paths ++
    (Fleet.S0061.paths ++
    (Fleet.S0062.paths ++
    (Fleet.S0063.paths ++
    (Fleet.S0064.paths ++
    (Fleet.S0065.paths ++
    (Fleet.S0066.paths ++
    (Fleet.S0067.paths ++
    (Fleet.S0068.paths ++
    (Fleet.S0069.paths ++
    (Fleet.S0070.paths ++
    (Fleet.S0071.paths ++
    (Fleet.S0072.paths ++
    (Fleet.S0073.paths ++
    (Fleet.S0074.paths ++
    (Fleet.S0075.paths ++
    (Fleet.S0076.paths ++
    (Fleet.S0077.paths ++
    (Fleet.S0078.paths ++
    (Fleet.S0079.paths ++
    (Fleet.S0080.paths ++
    (Fleet.S0081.paths ++
    (Fleet.S0082.paths ++
    (Fleet.S0083.paths ++
    (Fleet.S0084.paths ++
    (Fleet.S0085.paths ++
    (Fleet.S0086.paths ++
    (Fleet.S0087.paths ++
    (Fleet.S0088.paths ++
    (Fleet.S0089.paths ++
    (Fleet.S0090.paths ++
    (Fleet.S0091.paths ++
    (Fleet.S0092.paths ++
    (Fleet.S0093.paths ++
    (Fleet.S0094.paths ++
    (Fleet.S0095.paths ++
    (Fleet.S0096.paths ++
    (Fleet.S0097.paths ++
    (Fleet.S0098.paths ++
    (Fleet.S0099.paths ++
    (Fleet.S0100.paths ++
    (Fleet.S0101.paths ++
    (Fleet.S0102.paths ++
    (Fleet.S0103.paths ++
    (Fleet.S0104.paths))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem allPaths_sem : ∀ p ∈ allPaths, Sem (boxOf p) := by
  unfold allPaths
  exact List.forall_mem_append.mpr ⟨Fleet.S0000.sem, List.forall_mem_append.mpr ⟨Fleet.S0001.sem, List.forall_mem_append.mpr ⟨Fleet.S0002.sem, List.forall_mem_append.mpr ⟨Fleet.S0003.sem, List.forall_mem_append.mpr ⟨Fleet.S0004.sem, List.forall_mem_append.mpr ⟨Fleet.S0005.sem, List.forall_mem_append.mpr ⟨Fleet.S0006.sem, List.forall_mem_append.mpr ⟨Fleet.S0007.sem, List.forall_mem_append.mpr ⟨Fleet.S0008.sem, List.forall_mem_append.mpr ⟨Fleet.S0009.sem, List.forall_mem_append.mpr ⟨Fleet.S0010.sem, List.forall_mem_append.mpr ⟨Fleet.S0011.sem, List.forall_mem_append.mpr ⟨Fleet.S0012.sem, List.forall_mem_append.mpr ⟨Fleet.S0013.sem, List.forall_mem_append.mpr ⟨Fleet.S0014.sem, List.forall_mem_append.mpr ⟨Fleet.S0015.sem, List.forall_mem_append.mpr ⟨Fleet.S0016.sem, List.forall_mem_append.mpr ⟨Fleet.S0017.sem, List.forall_mem_append.mpr ⟨Fleet.S0018.sem, List.forall_mem_append.mpr ⟨Fleet.S0019.sem, List.forall_mem_append.mpr ⟨Fleet.S0020.sem, List.forall_mem_append.mpr ⟨Fleet.S0021.sem, List.forall_mem_append.mpr ⟨Fleet.S0022.sem, List.forall_mem_append.mpr ⟨Fleet.S0023.sem, List.forall_mem_append.mpr ⟨Fleet.S0024.sem, List.forall_mem_append.mpr ⟨Fleet.S0025.sem, List.forall_mem_append.mpr ⟨Fleet.S0026.sem, List.forall_mem_append.mpr ⟨Fleet.S0027.sem, List.forall_mem_append.mpr ⟨Fleet.S0028.sem, List.forall_mem_append.mpr ⟨Fleet.S0029.sem, List.forall_mem_append.mpr ⟨Fleet.S0030.sem, List.forall_mem_append.mpr ⟨Fleet.S0031.sem, List.forall_mem_append.mpr ⟨Fleet.S0032.sem, List.forall_mem_append.mpr ⟨Fleet.S0033.sem, List.forall_mem_append.mpr ⟨Fleet.S0034.sem, List.forall_mem_append.mpr ⟨Fleet.S0035.sem, List.forall_mem_append.mpr ⟨Fleet.S0036.sem, List.forall_mem_append.mpr ⟨Fleet.S0037.sem, List.forall_mem_append.mpr ⟨Fleet.S0038.sem, List.forall_mem_append.mpr ⟨Fleet.S0039.sem, List.forall_mem_append.mpr ⟨Fleet.S0040.sem, List.forall_mem_append.mpr ⟨Fleet.S0041.sem, List.forall_mem_append.mpr ⟨Fleet.S0042.sem, List.forall_mem_append.mpr ⟨Fleet.S0043.sem, List.forall_mem_append.mpr ⟨Fleet.S0044.sem, List.forall_mem_append.mpr ⟨Fleet.S0045.sem, List.forall_mem_append.mpr ⟨Fleet.S0046.sem, List.forall_mem_append.mpr ⟨Fleet.S0047.sem, List.forall_mem_append.mpr ⟨Fleet.S0048.sem, List.forall_mem_append.mpr ⟨Fleet.S0049.sem, List.forall_mem_append.mpr ⟨Fleet.S0050.sem, List.forall_mem_append.mpr ⟨Fleet.S0051.sem, List.forall_mem_append.mpr ⟨Fleet.S0052.sem, List.forall_mem_append.mpr ⟨Fleet.S0053.sem, List.forall_mem_append.mpr ⟨Fleet.S0054.sem, List.forall_mem_append.mpr ⟨Fleet.S0055.sem, List.forall_mem_append.mpr ⟨Fleet.S0056.sem, List.forall_mem_append.mpr ⟨Fleet.S0057.sem, List.forall_mem_append.mpr ⟨Fleet.S0058.sem, List.forall_mem_append.mpr ⟨Fleet.S0059.sem, List.forall_mem_append.mpr ⟨Fleet.S0060.sem, List.forall_mem_append.mpr ⟨Fleet.S0061.sem, List.forall_mem_append.mpr ⟨Fleet.S0062.sem, List.forall_mem_append.mpr ⟨Fleet.S0063.sem, List.forall_mem_append.mpr ⟨Fleet.S0064.sem, List.forall_mem_append.mpr ⟨Fleet.S0065.sem, List.forall_mem_append.mpr ⟨Fleet.S0066.sem, List.forall_mem_append.mpr ⟨Fleet.S0067.sem, List.forall_mem_append.mpr ⟨Fleet.S0068.sem, List.forall_mem_append.mpr ⟨Fleet.S0069.sem, List.forall_mem_append.mpr ⟨Fleet.S0070.sem, List.forall_mem_append.mpr ⟨Fleet.S0071.sem, List.forall_mem_append.mpr ⟨Fleet.S0072.sem, List.forall_mem_append.mpr ⟨Fleet.S0073.sem, List.forall_mem_append.mpr ⟨Fleet.S0074.sem, List.forall_mem_append.mpr ⟨Fleet.S0075.sem, List.forall_mem_append.mpr ⟨Fleet.S0076.sem, List.forall_mem_append.mpr ⟨Fleet.S0077.sem, List.forall_mem_append.mpr ⟨Fleet.S0078.sem, List.forall_mem_append.mpr ⟨Fleet.S0079.sem, List.forall_mem_append.mpr ⟨Fleet.S0080.sem, List.forall_mem_append.mpr ⟨Fleet.S0081.sem, List.forall_mem_append.mpr ⟨Fleet.S0082.sem, List.forall_mem_append.mpr ⟨Fleet.S0083.sem, List.forall_mem_append.mpr ⟨Fleet.S0084.sem, List.forall_mem_append.mpr ⟨Fleet.S0085.sem, List.forall_mem_append.mpr ⟨Fleet.S0086.sem, List.forall_mem_append.mpr ⟨Fleet.S0087.sem, List.forall_mem_append.mpr ⟨Fleet.S0088.sem, List.forall_mem_append.mpr ⟨Fleet.S0089.sem, List.forall_mem_append.mpr ⟨Fleet.S0090.sem, List.forall_mem_append.mpr ⟨Fleet.S0091.sem, List.forall_mem_append.mpr ⟨Fleet.S0092.sem, List.forall_mem_append.mpr ⟨Fleet.S0093.sem, List.forall_mem_append.mpr ⟨Fleet.S0094.sem, List.forall_mem_append.mpr ⟨Fleet.S0095.sem, List.forall_mem_append.mpr ⟨Fleet.S0096.sem, List.forall_mem_append.mpr ⟨Fleet.S0097.sem, List.forall_mem_append.mpr ⟨Fleet.S0098.sem, List.forall_mem_append.mpr ⟨Fleet.S0099.sem, List.forall_mem_append.mpr ⟨Fleet.S0100.sem, List.forall_mem_append.mpr ⟨Fleet.S0101.sem, List.forall_mem_append.mpr ⟨Fleet.S0102.sem, List.forall_mem_append.mpr ⟨Fleet.S0103.sem, Fleet.S0104.sem⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Boolean comparison of path lists.  Kernel evaluation of `decide (a = b) && eqPaths as bs`
returns the recursive call in tail position, so it runs iteratively; `List.hasDecEq` nests the
recursive call inside a `match` and overflows the kernel stack on 4730-element lists
("(kernel) deep recursion detected"). -/
def eqPaths : List (List ℕ) → List (List ℕ) → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a = b) && eqPaths as bs
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem eqPaths_sound : ∀ l₁ l₂ : List (List ℕ), eqPaths l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [eqPaths, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, eqPaths_sound as bs h.2]
  | [], _ :: _, h => by simp [eqPaths] at h
  | _ :: _, [], h => by simp [eqPaths] at h

theorem allPaths_eq : allPaths = modTree.leaves.map Prod.fst :=
  eqPaths_sound allPaths (modTree.leaves.map Prod.fst) (by decide +kernel)

/-- Family theorem: the psi-candidate Bellman statement on the exact image of every archived
leaf of the moderate-entropy partition (for mean difference at least `1/50`). -/
theorem family : ∀ q ∈ modTree.leaves, Sem (boxOf q.1) := by
  intro q hq
  have h1 : q.1 ∈ modTree.leaves.map Prod.fst := List.mem_map_of_mem hq
  rw [← allPaths_eq] at h1
  exact allPaths_sem q.1 h1

end CKLaneN1b
