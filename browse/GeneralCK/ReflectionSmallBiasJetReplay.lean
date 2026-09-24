import GeneralCK.ReflectionSmallBiasCompactFunctions

/-! Composition with a separately checked finite polynomial computation. -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem comp_finite {n : ℕ} {k : ℂ} {f g h : ℂ × ℂ → ℂ}
    {p q ts result : List Term}
    (hg : Approximates n k g p) (hh : Approximates n k h q)
    (hg0 : g 0 = 0) (hh0 : h 0 = 0) (hf : Approximates n k f ts)
    (ht : Approximates n k (fun z => eval k ts (g z,h z)) result) :
    Approximates n k (fun z => f (g z,h z)) result := by
  have hprod : AnalyticAt ℂ (fun z => (g z,h z)) 0 := hg.analytic.prod hh.analytic
  have hz : (g 0,h 0) = (0 : ℂ × ℂ) := by simp only [hg0,hh0]; rfl
  have hT : Tendsto (fun z => (g z,h z)) (𝓝 (0 : ℂ × ℂ)) (𝓝 0) := by
    simpa only [hz] using hprod.continuousAt.tendsto
  have hnorm : (fun z => (g z,h z)) =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖) := by
    simpa only [hz,sub_zero] using hprod.differentiableAt.isBigO_sub.norm_right
  exact ht.transfer (hf.analytic.comp_of_eq hprod hz)
    ((hf.error.comp_tendsto hT).trans (hnorm.norm_left.pow n))

theorem entropy_of_finite {k : ℂ} {f : ℂ × ℂ → ℂ} {p q : List Term}
    (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ))
    (hf : Approximates 24 k f p) (hzero : f 0 = 0)
    (ht : Approximates 24 k (fun z => eval k entropySeed (f z,0)) q) :
    Approximates 24 k (fun z => ComplexEntropy.entropyExt (f z)) q := by
  have hs := ((coordinateA 24 k).entropy hk hklog (by rfl)).replacePolynomial
    (equalityCheck_sound entropySeed_checked k)
  simpa only [Rat.cast_zero] using hf.comp_finite (const 24 k 0) hzero (by simp) hs ht

theorem atanh_of_finite {k : ℂ} {f : ℂ × ℂ → ℂ} {p q : List Term}
    (hk : k ≠ 0) (hf : Approximates 24 k f p) (hzero : f 0 = 0)
    (ht : Approximates 24 k (fun z => eval k atanhSeed (f z,0)) q) :
    Approximates 24 k (fun z => SmallBiasComplexDomain.atanhExt (f z)) q := by
  have hs := ((coordinateA 24 k).atanh hk (by rfl)).replacePolynomial
    (equalityCheck_sound atanhSeed_checked k)
  simpa only [Rat.cast_zero] using hf.comp_finite (const 24 k 0) hzero (by simp) hs ht

end GeneralCK.Reflection.SmallBiasJet.Approximates
