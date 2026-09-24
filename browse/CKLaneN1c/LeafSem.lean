import CKLaneN1.SubRows
import CKLaneG1.OppTransition

/-!
# Lane N1c-c: the in-row leaf statement of the transition cover

`LeafSem p`: every law satisfying the hypotheses of `CKLaneN1.SR_Transition` (canonical, central
opposite side, `1/50 ≤ d`, `E ≤ 11/200`, `4E ≤ d ≤ 8E`), lying in the exact image `CKLaneG1.InExy` of the
archived leaf box `CKLaneG1.OppTransition.root.ofPath p`, with strict psi-activity, has `gap ≤ cost`.
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneN1 CKLaneG1

/-- In-row statement on the image of the archived leaf with path `p`. -/
def LeafSem (p : List ℕ) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
    InExy (OppTransition.root.ofPath p) μ.a μ.b μ.meanEntropy → PsiActive μ →
    μ.gap ≤ μ.cost

end CKLaneN1c
