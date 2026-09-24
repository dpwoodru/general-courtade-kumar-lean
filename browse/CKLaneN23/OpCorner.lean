import GeneralCK.PsiEndpointBellman
import GeneralCK.PsiOppositeCornerDomain

/-!
# Lane N23 — row `OP_Corner` of the scope-locked manuscript route

`OP_Corner` and `PsiActive` are copied verbatim from
`~/ck_lanes_20260923/coord/routesrc/CKRoute/Manuscript.lean`
(sha256 5eefe06bd891dd6c492304e881a4574172568b6d04ec1329d0ddf3d6c01aaa04).

Archived owner: `retained/opposite_corner/OPPOSITE_CORNER_PROOF.md`, Theorem 2
(`a + (1-b) ≤ 2^-13`, every positive feasible entropy pair). In the psi-active branch the
archived proof bounds `R_B` by the Proposition 3.4 endpoint value with an entropy-imbalance
(logarithmic barrier) gain and a `q²/E` parent margin, after placing the corner inside
`d ≥ 9/10`, `E ≤ 10^-3`, `q ≤ 1/10`.

The row is discharged by an adapter over two compiled, sorry-free theorems of the F-C
provider (`~/gck_lanes/F-C/work/root`), which prove exactly that psi-branch estimate for
actual finite laws:

* `GeneralCK.PsiOppositeCornerDomain.corner_domain`: on the corner, `0 ≤ q ≤ 1/10`,
  `0 < E ≤ 1/1024`, `8E ≤ b - a` (entropy concavity and `H(2^-14) ≤ 1/1024`);
* `GeneralCK.PsiEndpointBellman.law_gap_le_cost`: for `a + b ≤ 1`, `E ≤ 1/80`,
  `8E ≤ b - a`, `q ≤ 1/10` and `phi ≤ psi` at the parent,
  `gap + (9/100)·q²/E ≤ F(d,E) + d/(2 ln 2)·barrier(t) ≤ cost`
  (endpoint contact with logarithmic imbalance gain, retained child maxima).

No numerical or regional fact is taken as a hypothesis.
-/

namespace CKLaneN23

open GeneralCK

/-- Strict psi-activity at the parent. -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Row `a + 1 - b ≤ 2^-13`: `retained/opposite_corner/OPPOSITE_CORNER_PROOF.md`, Thm 2. -/
def OP_Corner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a + (1 - μ.b) ≤ 1 / 8192 → PsiActive μ → μ.gap ≤ μ.cost

/-- The opposite deterministic corner row, unconditionally. -/
theorem row_opCorner : OP_Corner := by
  intro k μ _hab hsum _hb hcor hact
  have hc : μ.a + 1 - μ.b ≤ 1 / 8192 := by linarith
  obtain ⟨_hq, hqsmall, _hE, hEi, hd, _ha, _hb'⟩ :=
    PsiOppositeCornerDomain.corner_domain μ hsum hc
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) hd hqsmall hact'.le

end CKLaneN23
