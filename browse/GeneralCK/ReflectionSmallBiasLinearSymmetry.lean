import GeneralCK.ReflectionSmallBiasJetRawSum

/-! Exact reflection of a Taylor table in its second variable. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def reflectB (p : List Term) : List Term :=
  p.map (fun t => {t with c := (-1)^t.b*t.c})

theorem eval_reflectB (k : ℂ) (p : List Term) (z : ℂ × ℂ) :
    eval k (reflectB p) z = eval k p (z.1,-z.2) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    have hn : (-z.2)^t.b = (-1:ℂ)^t.b*z.2^t.b := by rw [neg_eq_neg_one_mul,mul_pow]
    change evalTerm k {t with c := (-1)^t.b*t.c} z + eval k (reflectB ts) z =
      evalTerm k t (z.1,-z.2) + eval k ts (z.1,-z.2)
    rw [ih]
    congr 1
    simp only [evalTerm,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,hn]
    ring

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem reflectB {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hf : Approximates n k f p) :
    Approximates n k (fun z => f (z.1,-z.2)) (SmallBiasPolynomial.reflectB p) := by
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ => (z.1,-z.2)) 0 :=
    analyticAt_fst.prod analyticAt_snd.neg
  have hzero : ((0:ℂ × ℂ).1,-(0:ℂ × ℂ).2) = 0 := by simp
  have ht : Tendsto (fun z : ℂ × ℂ => (z.1,-z.2)) (𝓝 0) (𝓝 0) := by
    simpa only [hzero] using ha.continuousAt.tendsto
  refine ⟨hf.analytic.comp_of_eq ha hzero, ?_⟩
  apply (hf.error.comp_tendsto ht).congr'
  · exact Filter.Eventually.of_forall (fun z => by
      change f (z.1,-z.2)-eval k p (z.1,-z.2) = f (z.1,-z.2)-eval k (SmallBiasPolynomial.reflectB p) z
      rw [eval_reflectB])
  · exact Filter.Eventually.of_forall (fun z => by
      change ‖(z.1,-z.2)‖^n = ‖z‖^n
      simp only [Prod.norm_def,norm_neg])

end GeneralCK.Reflection.SmallBiasJet.Approximates

namespace GeneralCK.Reflection.SmallBiasComplexDomain

theorem entropyExt_neg (c : ℂ) : ComplexEntropy.entropyExt (-c) = ComplexEntropy.entropyExt c := by
  simp only [ComplexEntropy.entropyExt,show 1+(-c)=1-c by ring,show 1-(-c)=1+c by ring]
  ring

end GeneralCK.Reflection.SmallBiasComplexDomain

