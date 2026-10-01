import CKLaneN1c.EPFamily
import CKLaneN1c.NMFamily

/-!
# Lane N1c-c: `CKLaneN1.SR_Transition` — CK_OPPOSITE_EXTENSION low-entropy transition theorem (4)

Archive `CK_OPPOSITE_EXTENSION.zip` (sha256 3f4b121c…392a), `transition/PROOF.md`, certificate
`transition/TRANSITION_RESULT.json` (sha256 3ebdd33e523bf99eded391317d7323b72dacea4c4aac2e0df88c79595cc33b0c):
2,425 leaves in `(E, x, y)`, root `[1/400, 11/200] × [4, 8] × [0, 8]`.

* cover: `CKLaneG1.OppTransition.cover_law` (lane G1, the exact archived partition);
* `outside` (226): `CKLaneG1.OppTransition.outside_empty` (lane G1);
* `endpoint` (1,687): `CKLaneN1c.endpoint_family` (kernel `checkEP`, soundness `checkEP_sound`);
* `normalized_phi_children` (508): `CKLaneN1c.normalized_family` (kernel `checkN`, `checkN_sound`);
* `prior_collar` (4): `CKLaneN1c.collar_family` (the same normalized kernel on the exact leaf boxes).
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

theorem tree_labels : OppTransition.tree.leaves.all (fun q => decide (q.2 < 4)) = true := by
  decide +kernel

/-- `SR_Transition`: the §4 row `d ≥ 1/50, E ≤ 11/200, 4E ≤ d ≤ 8E` of the central mean square. -/
theorem row_SR_Transition : SR_Transition := by
  intro k μ hab hsum ha hb hb9 hd hE h4 h8 hact
  obtain ⟨q, hq, hin⟩ := OppTransition.cover_law μ hsum hb hd hE h4 h8
  have hlt : q.2 < 4 := by
    have h := List.all_eq_true.mp tree_labels q hq
    simpa using h
  have hcases : q.2 = 0 ∨ q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact absurd hin (OppTransition.outside_empty q hq h0 μ.a μ.b μ.meanEntropy ha hb hd h8)
  · exact endpoint_family q hq h1 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact
  · exact normalized_family q hq h2 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact
  · exact collar_family q hq h3 k μ hab hsum ha hb hb9 hd hE h4 h8 hin hact

end CKLaneN1c
