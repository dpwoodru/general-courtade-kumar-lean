import CKLaneN1b.Family
import CKLaneN1.SubRows

/-!
# Lane N1b: CK_OPPOSITE_EXTENSION component (5) — opposite moderate-entropy theorem

`moderate_psi` is the archived theorem (5) of `CK_OPPOSITE_EXTENSION/PROOF.md` §3.4 on the whole
cross-half rectangle: `a ∈ [1/10,1/2]`, `b ∈ [1/2,9/10]`, `b - a ≥ 1/50`, `E ≥ 11/200` imply
`ζ ≥ R_ψ` at law level.  `sr_moderate` is the published sub-row `CKLaneN1.SR_Moderate`
(`~/ck_lanes_20260923/N1/SUBROWS.lean`, verbatim) via the branch transfer
`hybrid_gap_le_psi`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK

theorem moderate_psi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → 1 / 10 ≤ μ.a →
    μ.a ≤ 1 / 2 → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 → 1 / 50 ≤ μ.b - μ.a →
    11 / 200 ≤ μ.meanEntropy → candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  intro k μ _ ha0 ha1 hb0 hb1 hd hE
  have hE0 : ((E0 : ℚ) : ℝ) ≤ μ.meanEntropy := by
    have e : ((E0 : ℚ) : ℝ) = 11 / 200 := by norm_num [E0]
    rw [e]; exact hE
  have hd0 : ((DMIN : ℚ) : ℝ) ≤ μ.b - μ.a := by
    have e : ((DMIN : ℚ) : ℝ) = 1 / 50 := by norm_num [DMIN]
    rw [e]; exact hd
  obtain ⟨q, hq, hin⟩ := modTree_cover μ ha0 ha1 hb0 hb1 hE0
  exact family q hq k μ hin hd0

theorem sr_moderate : CKLaneN1.SR_Moderate := by
  intro k μ hab hsum ha0 hb0 hb1 hd hE hact
  have ha1 : μ.a ≤ 1 / 2 := by linarith
  exact (hybrid_gap_le_psi hact.le).trans (moderate_psi k μ hab ha0 ha1 hb0 hb1 hd hE)

end CKLaneN1b
