import GeneralCK.PsiThreeTenthsBiasClosure
import GeneralCK.PsiOuterEntropy200

/-!
The opposite central owner after the three-tenths wedge, with the already
proved forty-ratio parent exclusion inserted on its remaining high-bias side.
This module is a source-only draft until directly compiled and audited.
-/

namespace GeneralCK.PsiThreeTenthsCentralTail40

def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsBias.centralRegion a b E ∧
    (3 / 10 < 1 - a - b → 1 - a - b < 40 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem toThreeTenthsCentralOwner (h : CentralOwner) :
    PsiThreeTenthsBias.CentralOwner := by
  intro k μ hab hregion hactive
  apply h k μ hab ⟨hregion, ?_⟩ hactive
  intro hq3
  have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
    hregion.1.1.1.1.1.1.1.1
  have hb : (1 / 2 : ℝ) ≤ μ.b := hbase.2.1
  have ha : (1 / 10 : ℝ) ≤ μ.a := hbase.2.2.1
  have hqu : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have hq0 : 0 < 1 - μ.a - μ.b := by linarith
  have htail := PsiOuterEntropy200.parent_dominance_two_fifths
    hq0 hqu hE (le_of_not_gt hn)
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hmid] at htail
  exact (not_lt_of_ge hactive.le) htail

end GeneralCK.PsiThreeTenthsCentralTail40

#print axioms GeneralCK.PsiThreeTenthsCentralTail40.toThreeTenthsCentralOwner
