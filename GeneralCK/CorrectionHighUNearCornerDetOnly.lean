import GeneralCK.CorrectionHighUNearCornerLeftMinor
import GeneralCK.CorrectionHighUNearCornerActualAdapter

/-! The accepted left-minor bound removes one of the raw corner premises. -/

namespace GeneralCK.Correction.HighU

def NearCornerDetWedgeTarget : Prop :=
  ∀ t rho : ℝ, 0 < t → t ≤ 1 / 100 → 0 < rho → rho ≤ 1 / 100 →
    (rho ≤ t →
      2 * rho ^ 2 * t ^ 9 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t)) ∧
    (t ≤ rho →
      2 * rho ^ 4 * t ^ 7 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t))

theorem nearCorner_rawWedges_of_detWedges
    (h : NearCornerDetWedgeTarget) : NearCornerRawWedgeTarget := by
  intro t rho ht ht1 hr hr1
  obtain ⟨hsmall, hlarge⟩ := h t rho ht ht1 hr hr1
  exact ⟨nearCorner_m11_lower ht ht1 hr hr1, hsmall, hlarge⟩

theorem nearCorner_actual_ratio_of_detWedges
    (h : NearCornerDetWedgeTarget) {t rho : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    ActualRatioMinorsPositive (1 / 2 - t) rho :=
  nearCorner_actual_ratio_of_raw_wedges
    (nearCorner_rawWedges_of_detWedges h) ht ht1 hr hr1

#print axioms nearCorner_rawWedges_of_detWedges
#print axioms nearCorner_actual_ratio_of_detWedges

end GeneralCK.Correction.HighU
