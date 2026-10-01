import GeneralCK.PsiOuterEntropy28
import GeneralCK.PsiThreeTenthsCentralTail37

/-!
# Exact opposite active-Psi remainders after the ratio-28 exclusion

The central chart has `q ≤ 2/5` automatically. The compact chart uses that
bias bound as an explicit clipping premise. The closed face `q = 28E` is
excluded by strict parent dominance in both charts.
-/

namespace GeneralCK.PsiThreeTenthsTail28

theorem law_active_bias_lt_twenty_eight_entropy
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hq : 1 - μ.a - μ.b ≤ 2 / 5)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    1 - μ.a - μ.b < 28 * μ.meanEntropy := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  exact PsiOuterEntropy28.active_bias_lt_twenty_eight_entropy hq hE (by rwa [hm])

def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsCentralTail37.centralRegion a b E ∧ 1 - a - b < 28 * E

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem toTail37CentralOwner (h : CentralOwner) :
    PsiThreeTenthsCentralTail37.CentralOwner := by
  intro k μ hab hregion hactive
  have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
    hregion.1.1.1.1.1.1.1.1.1
  have hq : 1 - μ.a - μ.b ≤ 2 / 5 := by
    linarith [hbase.2.1, hbase.2.2.1]
  exact h k μ hab ⟨hregion,
    law_active_bias_lt_twenty_eight_entropy μ hq hactive.le⟩ hactive

/-- High-bias central certificates now start strictly above entropy 3/280. -/
theorem central_high_bias_entropy_lower {a b E : ℝ}
    (hregion : centralRegion a b E) (hq : 3 / 10 < 1 - a - b) :
    3 / 280 < E := by
  linarith [hregion.2]

def compactRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsBias.compactRegion a b E ∧
    (1 - a - b ≤ 2 / 5 → 1 - a - b < 28 * E)

def CompactOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    compactRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

/-- Direct conversion to the compact field of the current residual package. -/
theorem toThreeTenthsCompactOwner (h : CompactOwner) :
    PsiThreeTenthsBias.CompactOwner := by
  intro k μ hregion hactive
  apply h k μ ⟨hregion, ?_⟩ hactive
  intro hq
  exact law_active_bias_lt_twenty_eight_entropy μ hq hactive.le

#print axioms law_active_bias_lt_twenty_eight_entropy
#print axioms toTail37CentralOwner
#print axioms central_high_bias_entropy_lower
#print axioms toThreeTenthsCompactOwner

end GeneralCK.PsiThreeTenthsTail28
