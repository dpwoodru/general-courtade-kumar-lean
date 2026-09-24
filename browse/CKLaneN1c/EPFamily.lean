import CKLaneN1c.EPShard.S00
import CKLaneN1c.EPShard.S01
import CKLaneN1c.EPShard.S02
import CKLaneN1c.EPShard.S03
import CKLaneN1c.EPShard.S04
import CKLaneN1c.EPShard.S05
import CKLaneN1c.EPShard.S06
import CKLaneN1c.EPShard.S07
import CKLaneN1c.EPShard.S08
import CKLaneN1c.EPShard.S09
import CKLaneN1c.EPShard.S10
import CKLaneN1c.EPShard.S11
import CKLaneN1c.EPShard.S12
import CKLaneN1c.EPShard.S13
import CKLaneN1c.EPShard.S14
import CKLaneN1c.EPShard.S15
import CKLaneN1c.EPShard.S16
import CKLaneN1c.LeafSem
import CKLaneG1.CoverKit3

/-!
# Lane N1c-c: the transition `endpoint` family (1,687 archived leaves)

`epList` concatenates the 17 fleet shards (`EPShard.S00`–`S16`, archive DFS order); each shard proves
`checkEP` on all of its entries by `decide +kernel`.  `ep_walk` checks (kernel) that the entry paths
are exactly the `endpoint` (label 1) leaves of the archived tree `CKLaneG1.OppTransition.tree`, in order.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- The 1,687 archived `endpoint` leaves with their witnesses, in archive (DFS) order. -/
def epList : List (List ℕ × ℚ × ℚ × ℚ) :=
    EPShard.epL00 ++
    EPShard.epL01 ++
    EPShard.epL02 ++
    EPShard.epL03 ++
    EPShard.epL04 ++
    EPShard.epL05 ++
    EPShard.epL06 ++
    EPShard.epL07 ++
    EPShard.epL08 ++
    EPShard.epL09 ++
    EPShard.epL10 ++
    EPShard.epL11 ++
    EPShard.epL12 ++
    EPShard.epL13 ++
    EPShard.epL14 ++
    EPShard.epL15 ++
    EPShard.epL16

theorem epList_ok : epList.all
    (fun e => checkEP (OppTransition.root.ofPath e.1) e.2.1 e.2.2.1 e.2.2.2) = true := by
  simp only [epList, List.all_append, EPShard.epL00_ok, EPShard.epL01_ok, EPShard.epL02_ok, EPShard.epL03_ok, EPShard.epL04_ok, EPShard.epL05_ok, EPShard.epL06_ok, EPShard.epL07_ok, EPShard.epL08_ok, EPShard.epL09_ok, EPShard.epL10_ok, EPShard.epL11_ok, EPShard.epL12_ok, EPShard.epL13_ok, EPShard.epL14_ok, EPShard.epL15_ok, EPShard.epL16_ok, Bool.and_self]

theorem epList_length : epList.length = 1687 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ep_walk : PT.walkE (fun l => l != 1) OppTransition.tree [] epList = some [] := by
  decide +kernel

/-- Every archived `endpoint` leaf satisfies the in-row statement on its whole leaf image. -/
theorem endpoint_leafSem : ∀ q ∈ OppTransition.tree.leaves, q.2 = 1 → LeafSem q.1 := by
  intro q hq hl
  have hP : ∀ e ∈ epList, LeafSem e.1 := by
    intro e he k μ _hab hsum ha hb _hb9 hd _hE _h4 _h8 hin hact
    have hok := List.all_eq_true.mp epList_ok e he
    exact checkEP_sound hok μ hsum ha hb (by linarith) hin hact
  exact PT.walkE_all ep_walk hP q hq (by simp [hl])

/-- Family theorem, label `endpoint` (code 1) of `CKLaneG1.OppTransition.tree`: for every archived
`endpoint` leaf and every law in its exact image `InExy` satisfying the `SR_Transition` hypotheses and
strict psi-activity, `gap ≤ cost`. -/
theorem endpoint_family : ∀ q ∈ OppTransition.tree.leaves, q.2 = 1 →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
      1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
      4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
      InExy (OppTransition.root.ofPath q.1) μ.a μ.b μ.meanEntropy → PsiActive μ →
      μ.gap ≤ μ.cost :=
  endpoint_leafSem

end CKLaneN1c
