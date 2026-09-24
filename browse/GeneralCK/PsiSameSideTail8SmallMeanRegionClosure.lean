import GeneralCK.PsiSameSideTail14ExtendedRegionClosure
import GeneralCK.PsiSameRatioTail8SmallMean

/-!
# Exact complement of the checked small-mean ratio-eight strip

The ratio-eight strip is closed for every physical child entropy allocation.
The residual keeps the previous ratio-fourteen chart and adds its strict
complement, still expressed using only the means and average entropy.
-/

namespace GeneralCK

def SameSidePsiTail8SmallMeanChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    (μ.b ≤ 17 / 40 → 1 / 16384 < μ.a / μ.b) →
    (μ.a + μ.b ≤ 1 / 4 → 1 / 256 < μ.a / μ.b) →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean
    (h : SameSidePsiTail8SmallMeanChartOwner) : SameSidePsiTail14ExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hactive
  by_cases hsmall : μ.a + μ.b ≤ 1 / 4 ∧ μ.a / μ.b ≤ 1 / 256
  · exact sameSidePsiRatioTail8SmallMeanOwner μ hab.le hsmall.1 hsmall.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hside hratio hstrip ?_ hactive
    intro hsum'
    by_contra hn
    exact hsmall ⟨hsum', le_of_not_gt hn⟩

def sameSideTail8SmallMeanScalarRegion (a b E : ℝ) : Prop :=
  sameSideTail14ExtendedScalarRegion a b E ∧
    (a + b ≤ 1 / 4 → 1 / 256 < a / b)

theorem sameSidePsiTail8SmallMeanChartOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate
      sameSideTail8SmallMeanScalarRegion) :
    SameSidePsiTail8SmallMeanChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hsmall hactive
  have hregion : sameSideTail8SmallMeanScalarRegion μ.a μ.b μ.meanEntropy := by
    refine ⟨⟨hsum, hmean, ?_, hE, hside, hratio, hstrip⟩, hsmall⟩
    simpa only [InteriorLaw.information, InteriorLaw.midpoint] using hinfo
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab
    hregion hactive.le

end GeneralCK

#print axioms GeneralCK.sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean
#print axioms GeneralCK.sameSidePsiTail8SmallMeanChartOwner_of_affineCertificate
