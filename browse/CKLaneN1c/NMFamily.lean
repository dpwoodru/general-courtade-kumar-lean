import CKLaneN1c.NMShard.S00
import CKLaneN1c.NMShard.S01
import CKLaneN1c.NMShard.S02
import CKLaneN1c.NMShard.S03
import CKLaneN1c.NMShard.S04
import CKLaneN1c.NMShard.S05
import CKLaneN1c.LeafSem
import CKLaneG1.CoverKit3

/-!
# Lane N1c-c: the transition `normalized_phi_children` and `prior_collar` families

`nmList` concatenates the fleet shards `NMShard.S00`–`S05` (512 entries: the 508 archived
`normalized_phi_children` leaves and the 4 archived `prior_collar` leaves, archive DFS order); each shard
proves `checkN` on all of its entries by `decide +kernel`.  `nm_walk` checks (kernel) that the entry
paths are exactly the label-2 and label-3 leaves of `CKLaneG1.OppTransition.tree`, in order.

The 4 `prior_collar` leaves (archived delegate: the `q ≤ 2E, d ≥ 6E` collar of SHARPER_COLLARS) are
closed here directly by the transition component's own normalized comparison (10) on the exact archived
leaf boxes (exact margins ≥ 0.12); no collar theorem is assumed.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- The archived label-2/3 leaves with their witnesses `(v_p, v_m, v_l)`, archive (DFS) order. -/
def nmList : List (List ℕ × ℚ × ℚ × ℚ) :=
    NMShard.nmL00 ++
    NMShard.nmL01 ++
    NMShard.nmL02 ++
    NMShard.nmL03 ++
    NMShard.nmL04 ++
    NMShard.nmL05

theorem nmList_ok : nmList.all
    (fun e => checkN (OppTransition.root.ofPath e.1) e.2.1 e.2.2.1 e.2.2.2) = true := by
  simp only [nmList, List.all_append, NMShard.nmL00_ok, NMShard.nmL01_ok, NMShard.nmL02_ok, NMShard.nmL03_ok, NMShard.nmL04_ok, NMShard.nmL05_ok, Bool.and_self]

theorem nmList_length : nmList.length = 512 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nm_walk : PT.walkE (fun l => !(l == 2 || l == 3)) OppTransition.tree [] nmList = some [] := by
  decide +kernel

theorem nm_leafSem : ∀ q ∈ OppTransition.tree.leaves, (q.2 = 2 ∨ q.2 = 3) → LeafSem q.1 := by
  intro q hq hl
  have hP : ∀ e ∈ nmList, LeafSem e.1 := by
    intro e he k μ _hab hsum ha hb _hb9 hd hE h4 _h8 hin hact
    have hok := List.all_eq_true.mp nmList_ok e he
    exact checkN_sound hok μ hsum ha hb hd hE h4 hin hact
  apply PT.walkE_all nm_walk hP q hq
  rcases hl with h | h <;> simp [h]

/-- Family theorem, label `normalized_phi_children` (code 2) of `CKLaneG1.OppTransition.tree`. -/
theorem normalized_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 2 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  fun q hq hl => nm_leafSem q hq (Or.inl hl)

/-- Family theorem, label `prior_collar` (code 3) of `CKLaneG1.OppTransition.tree`. -/
theorem collar_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 3 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  fun q hq hl => nm_leafSem q hq (Or.inr hl)

end CKLaneN1c
