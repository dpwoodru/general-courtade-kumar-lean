import GeneralCK.PsiExtendedRegionClosure
import GeneralCK.PsiSameRatioTail16

/-!
# Exact same-side residual after the ratio-sixteen tail

The closed region `a/b≤2⁻¹⁶` is discharged for every actual law by
`sameSidePsiRatioTail16Owner`. The only remaining same-side chart premise
begins at the strict complement `2⁻¹⁶<a/b`, with the other canonical
conditions unchanged.
-/

namespace GeneralCK

def SameSidePsiTail16ChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 65536 < μ.a / μ.b →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiExtendedChartOwner_of_tail16
    (h : SameSidePsiTail16ChartOwner) : SameSidePsiExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside _hratio hactive
  by_cases hr : μ.a / μ.b ≤ 1 / 65536
  · exact sameSidePsiRatioTail16Owner μ hab.le hside hr hactive.le
  · exact h k μ hab hsum hmean hinfo hE hside (lt_of_not_ge hr) hactive

end GeneralCK

#print axioms GeneralCK.sameSidePsiExtendedChartOwner_of_tail16
