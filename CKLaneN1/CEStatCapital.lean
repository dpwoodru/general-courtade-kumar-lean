import CKLaneN1.CapShard.K00
import CKLaneN1.CapShard.K01
import CKLaneN1.CapShard.K02
import CKLaneN1.CapShard.K03
import CKLaneN1.CapShard.K04
import CKLaneN1.CapShard.K05
import CKLaneN1.CapShard.K06
import CKLaneN1.CapShard.K07
import CKLaneN1.CapShard.K08
import CKLaneN1.Chunks
import CKLaneN1.CapKey

set_option autoImplicit false

/-!
# Lane N1: CE-stat S.3 row 2 — capital exclusion

`capTree_ok`: all 531 capital boxes pass the kernel check (fleet shards `CapShard.K00..K08`,
`decide +kernel`). With the analytic tails of `CapTail` this gives the concavity-free pure-`Θ`
inequality `theta_capital` and the S.3 owner `capitalExclusion : CapitalExclusion`.
-/

namespace CKLaneN1.Capital

open GeneralCK CKLaneN1.CEStat

theorem capTree_length : capTree.leaves.length = 531 := by decide +kernel

/-- Every capital box passes the kernel check. -/
theorem capTree_ok : capTree.allLeaves (fun p w => capLeafOK (capRoot.ofPath p) w) = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => capLeafOK (capRoot.ofPath q.1) q.2) 60 9 capTree.leaves
    (by rw [capTree_length]; decide)
  intro k hk
  interval_cases k
  · exact CapShard.K00
  · exact CapShard.K01
  · exact CapShard.K02
  · exact CapShard.K03
  · exact CapShard.K04
  · exact CapShard.K05
  · exact CapShard.K06
  · exact CapShard.K07
  · exact CapShard.K08

/-- **Pure-Θ capital inequality** (concavity-free) on `[21/200, ∞) × [303/50, ∞)`. -/
theorem theta_capital {U W : ℝ} (hU : 21 / 200 ≤ U) (hW : 303 / 50 ≤ W) :
    e8Theta (U + 2 * W) ≤ e8Theta U + e8Theta W :=
  theta_capital_of_tree capTree_ok hU hW

/-- **S.3 row 2 (CE-stat capital exclusion).** -/
theorem capitalExclusion : CapitalExclusion := capitalExclusion_of_tree capTree_ok

end CKLaneN1.Capital
