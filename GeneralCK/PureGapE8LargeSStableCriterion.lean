import GeneralCK.PureGapE8LargeSJetCriterion
import GeneralCK.PureGapE8StableParameterSurjective

/-!
# Stable-parameter certificate interface for E8 logarithmic convexity

This is the final adapter expected by the finite `[0,20]` and analytic-tail
`[20,∞)` certificate: it is enough to establish the jet numerator sign at
`Y a` for every positive stable parameter `a`.
-/

namespace GeneralCK

open Certificates.E8TAxisDeltaDirectionalJet
open Certificates.E8TAxisStableScalar

/-- The exact statement emitted by an alpha-space certificate. -/
def E8StableLogDerivativeJetNumeratorNonnegative : Prop :=
  ∀ a : ℝ, 0 < a → 0 ≤ e8LogDerivativeJetNumerator (Y a)

theorem e8LogDerivativeJetNumeratorNonnegative_of_stable
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8LogDerivativeJetNumeratorNonnegative := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := e8SlopeRange_exists_stable_parameter hy
  exact h a ha

theorem e8LargeSStructure_of_stable_jet_numerator
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8LargeSStructure :=
  e8LargeSStructure_of_jet_numerator
    (e8LogDerivativeJetNumeratorNonnegative_of_stable h)

theorem e8_largeS_of_stable_jet_numerator
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  e8_largeS_of_jet_numerator
    (e8LogDerivativeJetNumeratorNonnegative_of_stable h)

#print axioms e8LogDerivativeJetNumeratorNonnegative_of_stable
#print axioms e8LargeSStructure_of_stable_jet_numerator
#print axioms e8_largeS_of_stable_jet_numerator

end GeneralCK
