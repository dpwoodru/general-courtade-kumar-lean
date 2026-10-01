import GeneralCK.PsiSameSideTail15RegionClosure
import GeneralCK.PsiSameRatioTail14Extended
import GeneralCK.PsiAffineChildCertificate

/-!
# Exact same-side residual after the extended ratio-fourteen strip

The actual-law theorem covers the closed strip `b ≤ 17/40` and
`a/b ≤ 2⁻¹⁴`.  This owner records its strict complement within the
previous ratio-fifteen chart.
-/

namespace GeneralCK

def SameSidePsiTail14ExtendedChartOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
    μ.a < μ.b → μ.a + μ.b < 1 →
    1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
    1 / 1000000 < μ.meanEntropy →
    μ.b ≤ 1 / 2 → 1 / 32768 < μ.a / μ.b →
    (μ.b ≤ 17 / 40 → 1 / 16384 < μ.a / μ.b) →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
    μ.gap ≤ μ.cost

theorem sameSidePsiTail15ChartOwner_of_tail14Extended
    (h : SameSidePsiTail14ExtendedChartOwner) : SameSidePsiTail15ChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hactive
  by_cases hstrip : μ.b ≤ 17 / 40 ∧ μ.a / μ.b ≤ 1 / 16384
  · exact sameSidePsiRatioTail14ExtendedOwner μ hab.le hstrip.1 hstrip.2 hactive.le
  · apply h k μ hab hsum hmean hinfo hE hside hratio ?_ hactive
    intro hb
    by_contra hn
    exact hstrip ⟨hb, le_of_not_gt hn⟩

/-- The exact three-variable region remaining after the checked strips. -/
def sameSideTail14ExtendedScalarRegion (a b E : ℝ) : Prop :=
  a + b < 1 ∧ 1 / 16 < a + b ∧
  1 / 100 < H ((a + b) / 2) - E ∧ 1 / 1000000 < E ∧
  b ≤ 1 / 2 ∧ 1 / 32768 < a / b ∧
  (b ≤ 17 / 40 → 1 / 16384 < a / b)

/-- A valid two-floor child-support certificate on the residual three-variable
chart supplies the remaining actual-law owner. -/
theorem sameSidePsiTail14ExtendedChartOwner_of_affineCertificate
    (h : PsiAffineChildCertificate.AffineChildCertificate
      sameSideTail14ExtendedScalarRegion) :
    SameSidePsiTail14ExtendedChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hactive
  have hregion : sameSideTail14ExtendedScalarRegion μ.a μ.b μ.meanEntropy := by
    refine ⟨hsum, hmean, ?_, hE, hside, hratio, hstrip⟩
    simpa only [InteriorLaw.information, InteriorLaw.midpoint] using hinfo
  exact PsiAffineChildCertificate.law_gap_le_cost_of_certificate h μ hab
    hregion hactive.le

#print axioms sameSidePsiTail15ChartOwner_of_tail14Extended
#print axioms sameSidePsiTail14ExtendedChartOwner_of_affineCertificate

end GeneralCK
