import CKLaneN23.OpCorner
import GeneralCK.PsiOppositeBoundaryOwner

/-!
# Lane N23 — row `OP_BoundaryStrip` of the scope-locked manuscript route

`OP_BoundaryStrip` is copied verbatim from
`~/ck_lanes_20260923/coord/routesrc/CKRoute/Manuscript.lean`
(sha256 5eefe06bd891dd6c492304e881a4574172568b6d04ec1329d0ddf3d6c01aaa04);
`PsiActive` is the verbatim copy in `CKLaneN23.OpCorner`.

Archived owner: `opposite/PROOF.md` (uniform boundary strip, all positive feasible
entropies). Its reduction: if `a + 1 - b ≤ 2^-13` the opposite corner (Input 2) applies;
otherwise `x = 1 - b ∈ [2^-13 - 2^-28, 1/2]`, `q = x - a > 0`, the deterministic cost
lower bound `j(a,1-x) ≥ ½(1-u-A)[J(A)+J(u)]` on a leaf `x ∈ [l,u]`, and the parent-only
envelope `R_B ≤ η(C(l-A))` (resp. with the `q/8` entropy floor on small bias) are compared
on the 17 exact rational leaves of `opposite/BOUNDARY_STRIP.py`.

The row is discharged by an adapter terminating in the row, reusing:

* `CKLaneN23.row_opCorner` (this lane, unconditional) on `a + (1 - b) ≤ 1/8192`;
* `GeneralCK.PsiOppositeBoundary.law_gap_le_cost_outside_corner` (F-C provider, compiled,
  sorry-free): `1/2 ≤ b`, `a ≤ Ac = 1/268435456`, `1/8192 < a + 1 - b`, strict psi-activity
  `⟹ gap ≤ cost`, proved from the 17 archived rational leaves (three with the plain
  envelope), the analytic parent envelope and `stripCost_le_actual`.

No numerical or regional fact is taken as a hypothesis.
-/

namespace CKLaneN23

open GeneralCK

/-- Row `a ≤ 2^-28`: `opposite/PROOF.md`, uniform boundary strip. -/
def OP_BoundaryStrip : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a ≤ 1 / 268435456 → PsiActive μ → μ.gap ≤ μ.cost

/-- The uniform extreme-mean opposite boundary strip row, unconditionally. -/
theorem row_opBoundaryStrip : OP_BoundaryStrip := by
  intro k μ hab hsum hb hbs hact
  by_cases hcor : μ.a + (1 - μ.b) ≤ 1 / 8192
  · exact row_opCorner k μ hab hsum hb hcor hact
  · have hc : 1 / 8192 < μ.a + 1 - μ.b := by linarith [lt_of_not_ge hcor]
    have haA : μ.a ≤ BoundaryStrip.Ac := by
      unfold BoundaryStrip.Ac
      exact hbs
    have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
    exact PsiOppositeBoundary.law_gap_le_cost_outside_corner μ hb haA hc hact'

end CKLaneN23
