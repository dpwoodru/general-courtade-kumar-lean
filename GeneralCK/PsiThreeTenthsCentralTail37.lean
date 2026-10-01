import GeneralCK.PsiThreeTenthsCentralTail40
import GeneralCK.PsiOuterEntropy37

/-! The checked parent exclusion at `37E≤q≤2/5` narrows the opposite
central active-Psi owner. -/

namespace GeneralCK.PsiThreeTenthsCentralTail37

def centralRegion (a b E : ℝ) : Prop :=
  PsiThreeTenthsBias.centralRegion a b E ∧
    (3 / 10 < 1 - a - b → 1 - a - b < 37 * E)

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem toTail40CentralOwner (h : CentralOwner) :
    PsiThreeTenthsCentralTail40.CentralOwner := by
  intro k μ hab hregion hactive
  apply h k μ hab ⟨hregion.1, ?_⟩ hactive
  intro hq3
  have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
    hregion.1.1.1.1.1.1.1.1.1
  have hb : (1 / 2 : ℝ) ≤ μ.b := hbase.2.1
  have ha : (1 / 10 : ℝ) ≤ μ.a := hbase.2.2.1
  have hqu : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  by_contra hn
  have hq0 : 0 < 1 - μ.a - μ.b := by linarith
  have htail := PsiOuterEntropy37.parent_dominance_two_fifths37
    hq0 hqu hE (le_of_not_gt hn)
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  rw [hmid] at htail
  exact (not_lt_of_ge hactive.le) htail

#print axioms toTail40CentralOwner

end GeneralCK.PsiThreeTenthsCentralTail37
