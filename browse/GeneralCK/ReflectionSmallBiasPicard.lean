import GeneralCK.ReflectionSmallBiasComplexDifference
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Finite Picard approximation of the analytic contact

This identifies a finite expression built from entropy and arithmetic with
the contact germ to any prescribed finite order. It does not rely on a
numerically computed inverse-series table.
-/

namespace GeneralCK.Reflection.SmallBiasPicard

open Filter Asymptotics ComplexEntropy ComplexGlobalAnalytic
open scoped Topology

noncomputable def iterate : ℕ → ℂ → ℂ
  | 0, _ => 0
  | n + 1, t => t * entropyExt (iterate n t)

@[simp] theorem iterate_zero (n : ℕ) : iterate n 0 = 0 := by
  cases n <;> simp [iterate]

@[simp] theorem contact_zero : fixedPointOnDisc 0 = 0 := by
  have hh := fixedPointOnDisc_fixed (tau := 0) (by norm_num)
  simpa using hh

theorem analyticAt_iterate (n : ℕ) : AnalyticAt ℂ (iterate n) 0 := by
  induction n with
  | zero => exact analyticAt_const
  | succ n ih =>
    exact analyticAt_id.mul
      ((ComplexContactGerm.analyticAt_entropyExt (c := 0) (by norm_num)).comp_of_eq ih (iterate_zero n))

theorem analyticAt_contact : AnalyticAt ℂ fixedPointOnDisc 0 :=
  analyticAt_fixedPointOnDisc (by norm_num)

theorem contact_sub_iterate_isBigO (n : ℕ) :
    (fun t => fixedPointOnDisc t - iterate n t) =O[𝓝 (0 : ℂ)] (fun t => t ^ (n + 1)) := by
  induction n with
  | zero =>
    simpa only [iterate, contact_zero, sub_zero, Nat.zero_add, pow_one] using
      analyticAt_contact.differentiableAt.isBigO_sub
  | succ n ih =>
    have hpair : Tendsto (fun t => (fixedPointOnDisc t, iterate n t))
        (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
      simpa only [contact_zero, iterate_zero] using
        analyticAt_contact.continuousAt.tendsto.prodMk_nhds (analyticAt_iterate n).continuousAt.tendsto
    have hE := (ComplexContactGerm.analyticAt_entropyExt (c := 0) (by norm_num)).hasStrictFDerivAt.isBigO_sub
    have hd : (fun t => entropyExt (fixedPointOnDisc t) - entropyExt (iterate n t))
        =O[𝓝 (0 : ℂ)] (fun t => t ^ (n + 1)) :=
      (hE.comp_tendsto hpair).trans ih
    have hm := (isBigO_refl (fun t : ℂ => t) (𝓝 0)).mul hd
    have heq : (fun t => t * (entropyExt (fixedPointOnDisc t) - entropyExt (iterate n t)))
        =ᶠ[𝓝 (0 : ℂ)] (fun t => fixedPointOnDisc t - iterate (n + 1) t) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖(0 : ℂ)‖ < (7 / 10 : ℝ) by norm_num)] with t ht
      calc
        _ = t * entropyExt (fixedPointOnDisc t) - t * entropyExt (iterate n t) := by ring
        _ = fixedPointOnDisc t - iterate (n + 1) t :=
          congrArg (fun z => z - t * entropyExt (iterate n t)) (fixedPointOnDisc_fixed ht).symm
    exact hm.congr' heq (Filter.Eventually.of_forall fun t => (pow_succ' t (n + 1)).symm)

/-- Twenty-two finite iterations suffice for the contact value's order-24 remainder. -/
theorem contact_sub_iterate22_isBigO :
    (fun t => fixedPointOnDisc t - iterate 22 t) =O[𝓝 (0 : ℂ)] (fun t => t ^ 23) :=
  contact_sub_iterate_isBigO 22

end GeneralCK.Reflection.SmallBiasPicard
