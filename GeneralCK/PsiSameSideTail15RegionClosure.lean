import GeneralCK.PsiSameSideTail16RegionClosure
import GeneralCK.PsiSameRatioTail15

/-!
# Exact same-side residual after the ratio-fifteen tail

Every actual law with `a/b≤2⁻¹⁵` is closed by the checked tail theorem once
the latter module passes its direct Lean audit. The remaining owner has
the strict complement ratio; every other canonical chart condition remains.
-/

namespace GeneralCK

def SameSidePsiTail15ChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiExtendedChartOwner_of_tail15
    (h : SameSidePsiTail15ChartOwner) : SameSidePsiExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 32768
  · exact sameSidePsiRatioTail15Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

theorem sameSidePsiTail16ChartOwner_of_tail15
    (h : SameSidePsiTail15ChartOwner) : SameSidePsiTail16ChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 32768
  · exact sameSidePsiRatioTail15Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

end GeneralCK

#print axioms GeneralCK.sameSidePsiExtendedChartOwner_of_tail15
#print axioms GeneralCK.sameSidePsiTail16ChartOwner_of_tail15
