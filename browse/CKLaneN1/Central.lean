import CKLaneN1.SubRows

/-!
# Lane N1: §4 assembly adapter for the central mean square (conditional)

`centralSquare_of_subrows : SubRows → CentralSquareRow` is the exhaustive assembly of
`CK_OPPOSITE_EXTENSION.zip`, `PROOF.md` §4: same side ⇒ half-square theorem; otherwise
(`a ≤ 1/2 ≤ b` in canonical orientation) the six-row table on `d = b - a`, `q = 1 - a - b`,
`E = meanEntropy`. It is CONDITIONAL on the sub-rows; it closes nothing by itself.

Helper adapters:
* `largeRatio_of_parent8_eightRatio` — the last two §4 rows give the N4 union row;
* `parent8_of_dominance` — law-level parent dominance makes `SR_Parent8` vacuous;
* `sameSideHalf_of_ssCompact` — cross-row reduction: the route's own same-side row
  `CKRoute.SS_Compact` (verbatim copy `SSCompactRow`) contains the half-square;
* `centralSquare_of_opp` / `CentralSquareOppRow` — the opposite part, which is all that
  `CKRoute.ManuscriptRoute.oppositeSide` consumes.
-/

namespace CKLaneN1

open GeneralCK

/-- §4 exhaustive assembly, conditional on the six sub-rows. -/
theorem centralSquare_of_subrows (h : SubRows) : CentralSquareRow := by
  intro k μ hab hsum ha hb hact
  by_cases hhalf : μ.b ≤ 1 / 2
  · exact h.sameSideHalf k μ hab hsum ha hhalf hact
  have hb2 : 1 / 2 ≤ μ.b := le_of_lt (lt_of_not_ge hhalf)
  by_cases hd : μ.b - μ.a ≤ 1 / 50
  · exact h.diagonalBand k μ hab hsum ha hb2 hb hd hact
  have hd' : 1 / 50 ≤ μ.b - μ.a := le_of_lt (lt_of_not_ge hd)
  by_cases hE : 11 / 200 ≤ μ.meanEntropy
  · exact h.moderate k μ hab hsum ha hb2 hb hd' hE hact
  have hE' : μ.meanEntropy ≤ 11 / 200 := le_of_lt (lt_of_not_ge hE)
  by_cases h4 : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact h.smallRatio k μ hab hsum ha hb2 hb hd' hE' h4 hact
  have h4' : 4 * μ.meanEntropy ≤ μ.b - μ.a := le_of_lt (lt_of_not_ge h4)
  by_cases h8 : μ.b - μ.a ≤ 8 * μ.meanEntropy
  · exact h.transition k μ hab hsum ha hb2 hb hd' hE' h4' h8 hact
  have h8' : 8 * μ.meanEntropy ≤ μ.b - μ.a := le_of_lt (lt_of_not_ge h8)
  exact h.largeRatio k μ hab hsum ha hb2 hb hd' hE' h8' hact

/-- The last two §4 rows (split on `q = 8E`) give the union row owned by lane N4. -/
theorem largeRatio_of_parent8_eightRatio (hp : SR_Parent8) (he : SR_EightRatio) :
    SR_LargeRatio := by
  intro k μ hab hsum ha hb2 hb hd hE h8 hact
  by_cases hq : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
  · exact hp k μ hab hsum ha hb2 hb hd hE h8 hq hact
  · exact he k μ hab hsum ha hb2 hb hd hE h8 (le_of_lt (lt_of_not_ge hq)) hact

/-- Parent dominance makes the `q ≥ 8E` row vacuous under strict psi-activity. -/
theorem parent8_of_dominance (h : SR_Parent8Dominance) : SR_Parent8 := by
  intro k μ hab hsum ha hb2 hb hd hE h8 hq hact
  exact absurd (h k μ hab hsum ha hb2 hb hd hE h8 hq) (not_le.mpr hact)

/-- Verbatim copy of the route row `CKRoute.SS_Compact` (same-side "otherwise" row). -/
def SSCompactRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 →
    1 / 16 < μ.a + μ.b → 1 / 4294967296 < μ.a / μ.b → PsiActive μ → μ.gap ≤ μ.cost

/-- Cross-row reduction: the same-side half-square lies inside the route's `SS_Compact` domain. -/
theorem sameSideHalf_of_ssCompact (h : SSCompactRow) : SR_SameSideHalf := by
  intro k μ hab _hsum ha hb hact
  have hbpos : 0 < μ.b := by linarith
  refine h k μ hab hb (by linarith) ?_ hact
  rw [lt_div_iff₀ hbpos]
  linarith

/-- The opposite part of the central square (all that `ManuscriptRoute.oppositeSide` uses). -/
def CentralSquareOppRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 → PsiActive μ → μ.gap ≤ μ.cost

/-- The central-square row from the half-square and the opposite part. -/
theorem centralSquare_of_opp (hs : SR_SameSideHalf) (ho : CentralSquareOppRow) :
    CentralSquareRow := by
  intro k μ hab hsum ha hb hact
  by_cases hhalf : μ.b ≤ 1 / 2
  · exact hs k μ hab hsum ha hhalf hact
  · exact ho k μ hab hsum ha (le_of_lt (lt_of_not_ge hhalf)) hb hact

/-- The opposite part from the five opposite §4 rows. -/
theorem centralSquareOpp_of_rows (hdb : SR_DiagonalBand) (hmod : SR_Moderate)
    (hsr : SR_SmallRatio) (htr : SR_Transition) (hlr : SR_LargeRatio) :
    CentralSquareOppRow := by
  intro k μ hab hsum ha hb2 hb hact
  by_cases hd : μ.b - μ.a ≤ 1 / 50
  · exact hdb k μ hab hsum ha hb2 hb hd hact
  have hd' : 1 / 50 ≤ μ.b - μ.a := le_of_lt (lt_of_not_ge hd)
  by_cases hE : 11 / 200 ≤ μ.meanEntropy
  · exact hmod k μ hab hsum ha hb2 hb hd' hE hact
  have hE' : μ.meanEntropy ≤ 11 / 200 := le_of_lt (lt_of_not_ge hE)
  by_cases h4 : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact hsr k μ hab hsum ha hb2 hb hd' hE' h4 hact
  have h4' : 4 * μ.meanEntropy ≤ μ.b - μ.a := le_of_lt (lt_of_not_ge h4)
  by_cases h8 : μ.b - μ.a ≤ 8 * μ.meanEntropy
  · exact htr k μ hab hsum ha hb2 hb hd' hE' h4' h8 hact
  exact hlr k μ hab hsum ha hb2 hb hd' hE' (le_of_lt (lt_of_not_ge h8)) hact

end CKLaneN1
