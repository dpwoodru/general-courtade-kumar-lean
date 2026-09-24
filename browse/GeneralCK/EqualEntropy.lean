import GeneralCK.FourMomentDefs
import GeneralCK.RadialFourPoint
import GeneralCK.FourMomentLowerBound

namespace GeneralCK

/-- The source's equal-entropy pure-gap owner, without assuming the L4 lower bound. -/
theorem pureGap_equal_entropy_nonneg {e : ℝ} (he : 0 < e) (a b : ℝ) :
    0 ≤ pureGap a b e e := by
  have h := equal_entropy_phi_gap_le_radial he a b
  simpa only [pureGap,fourMomentLowerBound,entropyCorrection_self,add_zero,
    show (e+e)/2=e by ring] using sub_nonneg.mpr h

/-- Equal entropies discharge the pure-gap input; the two LB1 inputs remain explicit. -/
theorem InteriorLaw.equal_entropy_phi_of_fourMoment {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (heq : μ.e = μ.f)
    (hreflect : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      entropyCorrection (H u) (H v) ≤ atomCorrection u v)
    (hconvex : ConvexOn ℝ (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2)) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  apply μ.phi_gap_le_cost_of_fourMoment hreflect hconvex
  rw [← heq]
  exact pureGap_equal_entropy_nonneg μ.e_pos μ.a μ.b

end GeneralCK
