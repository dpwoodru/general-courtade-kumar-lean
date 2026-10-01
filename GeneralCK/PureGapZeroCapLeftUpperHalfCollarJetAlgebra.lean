import GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic

/-!
Pure algebra for the proposed real-series degree-four jets. This file
does not prove that the actual entropy/contact functions equal these jets
up to an order-six remainder.
-/

namespace GeneralCK

noncomputable def leftUpperHalfD2 (z w L : ℝ) : ℝ :=
  (z ^ 2 + w ^ 2) / L

noncomputable def leftUpperHalfD4 (z w L : ℝ) : ℝ :=
  2 * (z ^ 4 + w ^ 4) / (3 * L)

noncomputable def leftUpperHalfInteriorJet (z w L : ℝ) : ℝ :=
  2 * (z - w) ^ 2 / L +
    8 * (z - w) * (z ^ 3 - w ^ 3) / (3 * L)

noncomputable def leftUpperHalfFJet (r D2 L : ℝ) : ℝ :=
  2 * r ^ 2 / L + 2 * r ^ 2 * D2 / L +
    (2 / (3 * L) - 1 / L ^ 2) * r ^ 4

noncomputable def leftUpperHalfEtaJet (D2 D4 L : ℝ) : ℝ :=
  4 * D2 + 4 * D4 + 4 * L * D2 ^ 2 / 3

noncomputable def leftUpperHalfEtaBJet (w L : ℝ) : ℝ :=
  4 * w ^ 2 / L + 16 * w ^ 4 / (3 * L)

noncomputable def leftUpperHalfCombinedJet (z w L : ℝ) : ℝ :=
  leftUpperHalfInteriorJet z w L +
    2 * leftUpperHalfFJet z (leftUpperHalfD2 z w L) L -
    leftUpperHalfFJet (z - w) (leftUpperHalfD2 z w L) L -
    leftUpperHalfEtaJet (leftUpperHalfD2 z w L)
      (leftUpperHalfD4 z w L) L +
    leftUpperHalfEtaBJet w L

theorem leftUpperHalfCombinedJet_eq_quartic {z lambda L : ℝ}
    (hL : L ≠ 0) :
    leftUpperHalfCombinedJet z (lambda * z) L =
      z ^ 4 * leftUpperQuarticCoefficient L lambda := by
  unfold leftUpperHalfCombinedJet leftUpperHalfInteriorJet
    leftUpperHalfFJet leftUpperHalfD2 leftUpperHalfD4
    leftUpperHalfEtaJet leftUpperHalfEtaBJet
    leftUpperQuarticCoefficient leftUpperQuarticNumerator
  field_simp [hL]
  ring

#print axioms leftUpperHalfCombinedJet_eq_quartic

end GeneralCK
