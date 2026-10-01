import GeneralCK.PsiRegionLedger
import GeneralCK.LogSum

/-!
# Direct active-psi owner from the log-sum cost floor

`InteriorLaw.psi_gap_le_splitBound` is the exact entropy-split reduction of
the active parent branch.  `LogSum.cost_lower_bound` supplies a law-uniform
lower bound for the cost.  This module joins them, leaving only a scalar
comparison at the parent means and entropy deficits.
-/

namespace GeneralCK

namespace Scalar

/-- The production profile is nonnegative on its information domain. -/
theorem P_nonneg_on_Ico {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ P t := by
  have hh : 1 - t ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [P, eta_eq_profile hh.1.le hh.2]
  have hi := entropyInverse_spec hh.1.le hh.2
  have hip := entropyInverse_pos hh.1 hh.2
  exact mul_nonneg (by linarith [hi.2.1]) (J_nonneg hip hi.2.1)

end Scalar

namespace InteriorLaw

variable {ι : Type*} [Fintype ι]

/-- The full parent-only lower bound supplied by the log-sum argument. -/
noncomputable def psiLogSumCostFloor (μ : InteriorLaw ι) : ℝ :=
  interiorCost μ.a μ.b +
    (μ.a - μ.b)^2 / (4 * LogSum.V μ.a μ.b) *
      ((H μ.a - μ.e) + (H μ.b - μ.f))

theorem psiLogSumCostFloor_le_cost (μ : InteriorLaw ι) :
    μ.psiLogSumCostFloor ≤ μ.cost := by
  simpa only [psiLogSumCostFloor] using LogSum.cost_lower_bound μ

/-- Strong direct owner: after the exact split reduction, it suffices to
compare `splitBound` with the complete log-sum floor. -/
theorem gap_le_of_activePsi_of_splitBound_le_logSumCostFloor
    (μ : InteriorLaw ι)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy)
    (hscalar : μ.splitBound ≤ μ.psiLogSumCostFloor) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive.le
    (hscalar.trans (μ.psiLogSumCostFloor_le_cost))

/-- The variance improvement in the log-sum floor is nonnegative. -/
theorem interiorCost_le_psiLogSumCostFloor (μ : InteriorLaw ι) :
    interiorCost μ.a μ.b ≤ μ.psiLogSumCostFloor := by
  have hV : 0 < LogSum.V μ.a μ.b :=
    LogSum.V_pos μ.a_interior μ.b_interior
  have hcoef : 0 ≤ (μ.a - μ.b)^2 / (4 * LogSum.V μ.a μ.b) := by
    positivity
  have hdef : 0 ≤ (H μ.a - μ.e) + (H μ.b - μ.f) := by
    linarith [μ.left_deficit_mem.1, μ.right_deficit_mem.1]
  unfold psiLogSumCostFloor
  exact le_add_of_nonneg_right (mul_nonneg hcoef hdef)

/-- The exact split bound is at most the unsplit active-parent value. -/
theorem splitBound_le_P_information (μ : InteriorLaw ι) :
    μ.splitBound ≤ Scalar.P μ.information := by
  rw [information_eq]
  unfold splitBound
  exact sub_le_self _ (Scalar.P_nonneg_on_Ico μ.meanDeficit_mem)

/-- Equation-(106) style owner.  The simpler scalar comparison
`splitBound ≤ j(a,b)` implies the Bellman inequality; the log-sum theorem
bridges the parent cost `j(a,b)=interiorCost a b` to the law cost. -/
theorem gap_le_of_activePsi_of_splitBound_le_interiorCost
    (μ : InteriorLaw ι)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy)
    (hscalar : μ.splitBound ≤ interiorCost μ.a μ.b) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_activePsi_of_splitBound_le_logSumCostFloor hactive
    (hscalar.trans (μ.interiorCost_le_psiLogSumCostFloor))

/-- Direct manuscript equation-(106) owner: it is enough that the parent
Jeffreys cost dominate the unsplit active-psi value `P(information)`. -/
theorem gap_le_of_activePsi_of_P_information_le_interiorCost
    (μ : InteriorLaw ι)
    (hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy)
    (hscalar : Scalar.P μ.information ≤ interiorCost μ.a μ.b) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_activePsi_of_splitBound_le_interiorCost hactive
    (μ.splitBound_le_P_information.trans hscalar)

end InteriorLaw

/-- A single scalar owner on the canonical residual domain discharges the
entire active-psi premise without referring to the seven chart labels. -/
theorem residualPsi_of_splitBound_le_logSumCostFloor
    (hscalar : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.splitBound ≤ μ.psiLogSumCostFloor) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro k μ hab hsum hmean hinfo hactive
  exact μ.gap_le_of_activePsi_of_splitBound_le_logSumCostFloor hactive
    (hscalar k μ hab hsum hmean hinfo hactive)

/-- Equation-(106) on the residual domain directly supplies the active-psi
premise. -/
theorem residualPsi_of_P_information_le_interiorCost
    (hscalar : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      Scalar.P μ.information ≤ interiorCost μ.a μ.b) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost := by
  intro k μ hab hsum hmean hinfo hactive
  exact μ.gap_le_of_activePsi_of_P_information_le_interiorCost hactive
    (hscalar k μ hab hsum hmean hinfo hactive)

#print axioms Scalar.P_nonneg_on_Ico
#print axioms InteriorLaw.psiLogSumCostFloor_le_cost
#print axioms InteriorLaw.gap_le_of_activePsi_of_splitBound_le_logSumCostFloor
#print axioms InteriorLaw.interiorCost_le_psiLogSumCostFloor
#print axioms InteriorLaw.splitBound_le_P_information
#print axioms InteriorLaw.gap_le_of_activePsi_of_splitBound_le_interiorCost
#print axioms InteriorLaw.gap_le_of_activePsi_of_P_information_le_interiorCost
#print axioms residualPsi_of_splitBound_le_logSumCostFloor
#print axioms residualPsi_of_P_information_le_interiorCost

end GeneralCK
