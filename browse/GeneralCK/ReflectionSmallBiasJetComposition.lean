import GeneralCK.ReflectionSmallBiasJetConstructors

/-! # Composition of checked multivariate Taylor jets -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def substituteTerm (n : ℕ) (t : Term) (p q : List Term) : List Term :=
  scale t.c (mulTrunc n (mulTrunc n (parameter t.k) (power n p t.a)) (power n q t.b))

def substitute (n : ℕ) (p q : List Term) : List Term → List Term
  | [] => const 0
  | t :: ts => add (substituteTerm n t p q) (substitute n p q ts)

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

variable {n : ℕ} {k : ℂ} {g h : ℂ × ℂ → ℂ} {p q : List Term}

theorem substituteTerm (hk : k ≠ 0) (hg : Approximates n k g p) (hh : Approximates n k h q)
    (t : Term) :
    Approximates n k (fun z => evalTerm k t (g z, h z)) (SmallBiasPolynomial.substituteTerm n t p q) := by
  have hterm := (((parameter n k t.k).mul hk (hg.pow hk t.a)).mul hk (hh.pow hk t.b)).scale t.c
  convert hterm using 1
  · funext z
    unfold evalTerm
    ring
  · rfl

theorem substitute (hk : k ≠ 0) (hg : Approximates n k g p) (hh : Approximates n k h q)
    (ts : List Term) :
    Approximates n k (fun z => eval k ts (g z, h z)) (SmallBiasPolynomial.substitute n p q ts) := by
  induction ts with
  | nil => simpa only [eval, SmallBiasPolynomial.substitute, Rat.cast_zero] using const n k 0
  | cons t ts ih => exact (hg.substituteTerm hk hh t).add ih

theorem comp (hk : k ≠ 0) (hg : Approximates n k g p) (hh : Approximates n k h q)
    (hg0 : g 0 = 0) (hh0 : h 0 = 0) {f : ℂ × ℂ → ℂ} {ts : List Term}
    (hf : Approximates n k f ts) :
    Approximates n k (fun z => f (g z, h z)) (SmallBiasPolynomial.substitute n p q ts) := by
  have hprod : AnalyticAt ℂ (fun z => (g z, h z)) 0 := hg.analytic.prod hh.analytic
  have hz : (g 0, h 0) = (0 : ℂ × ℂ) := by simp only [hg0, hh0]; rfl
  have hT : Tendsto (fun z => (g z, h z)) (𝓝 (0 : ℂ × ℂ)) (𝓝 0) := by
    simpa only [hz] using hprod.continuousAt.tendsto
  have hnorm : (fun z => (g z, h z)) =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖) := by
    simpa only [hz, sub_zero] using hprod.differentiableAt.isBigO_sub.norm_right
  have he := (hf.error.comp_tendsto hT).trans (hnorm.norm_left.pow n)
  exact (hg.substitute hk hh ts).transfer (hf.analytic.comp_of_eq hprod hz) he

end GeneralCK.Reflection.SmallBiasJet.Approximates
