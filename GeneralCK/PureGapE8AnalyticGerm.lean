import GeneralCK.ReflectionComplexContactGerm
import GeneralCK.ReflectionComplexContactFactor
import GeneralCK.Certificates.E8InverseJet

/-!
# An analytic E8 inverse germ at slope zero

This is deliberately separate from the zero-filled real `e8Q`.  The stable
hyperbolic parametrization is written in the bias coordinate `c = tanh α` and
inverted over `ℂ` near `c = 0`.
-/

namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection.ComplexEntropy

abbrev CDeriv (f : ℂ → ℂ) (f' x : ℂ) : Prop :=
  @HasDerivAt ℂ _ ℂ _
    (((NormedAlgebra.toNormedSpace ℂ) : NormedSpace ℂ ℂ).toModule) _ _ f f' x

noncomputable def atanhExt (c : ℂ) : ℂ :=
  (Complex.log (1 + c) - Complex.log (1 - c)) / 2

noncomputable def biasBExt (c : ℂ) : ℂ :=
  (Real.log 2 : ℂ) - Complex.log (1 - c ^ 2) / 2

/-- The manuscript's `Theta_*(α)` expressed through `c = tanh α`. -/
noncomputable def thetaParam (c : ℂ) : ℂ :=
  (2 / (Real.log 2 : ℂ)) *
    (atanhExt c + c * entropyExt c / ((1 - c ^ 2) * biasBExt c))

/-- The manuscript's `X(α)` in the same coordinate. -/
noncomputable def xParam (c : ℂ) : ℂ :=
  (Real.log 2 : ℂ) * c / (2 * entropyExt c)

@[simp] theorem atanhExt_zero : atanhExt 0 = 0 := by simp [atanhExt]
@[simp] theorem biasBExt_zero : biasBExt 0 = (Real.log 2 : ℂ) := by simp [biasBExt]
@[simp] theorem thetaParam_zero : thetaParam 0 = 0 := by simp [thetaParam]
@[simp] theorem xParam_zero : xParam 0 = 0 := by simp [xParam]

/-- The hyperbolic coordinate is odd, as an identity of principal logarithms. -/
theorem atanhExt_neg (c : ℂ) : atanhExt (-c) = -atanhExt c := by
  unfold atanhExt
  rw [show 1 + -c = 1 - c by ring, show 1 - -c = 1 + c by ring]
  ring

/-- The second hyperbolic denominator is even. -/
theorem biasBExt_neg (c : ℂ) : biasBExt (-c) = biasBExt c := by
  simp only [biasBExt, neg_sq]

/-- Exact odd symmetry of the analytic slope parametrization. -/
theorem thetaParam_neg (c : ℂ) : thetaParam (-c) = -thetaParam c := by
  simp only [thetaParam, atanhExt_neg, neg_sq, biasBExt_neg,
    Reflection.ComplexContactFactor.entropyExt_neg]
  ring

/-- Exact odd symmetry of the analytic contact-coordinate parametrization. -/
theorem xParam_neg (c : ℂ) : xParam (-c) = -xParam c := by
  simp only [xParam, Reflection.ComplexContactFactor.entropyExt_neg]
  ring

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem one_mem_slit : (1 : ℂ) ∈ Complex.slitPlane := by
  simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))

theorem analyticAt_atanhExt : AnalyticAt ℂ atanhExt 0 := by
  unfold atanhExt
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := analyticAt_const.add analyticAt_id
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z) 0 := analyticAt_const.sub analyticAt_id
  exact ((hp.clog (by simpa using one_mem_slit)).sub
    (hm.clog (by simpa using one_mem_slit))).div analyticAt_const (by norm_num)

theorem analyticAt_biasBExt : AnalyticAt ℂ biasBExt 0 := by
  unfold biasBExt
  have harg : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) 0 :=
    analyticAt_const.sub (analyticAt_id.pow 2)
  have hslit : (1 - (0 : ℂ) ^ 2) ∈ Complex.slitPlane := by simpa using one_mem_slit
  exact analyticAt_const.sub ((harg.clog hslit).div analyticAt_const (by norm_num))

theorem analyticAt_thetaParam : AnalyticAt ℂ thetaParam 0 := by
  unfold thetaParam
  have hE := Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have hden : (1 - (0 : ℂ) ^ 2) * biasBExt 0 ≠ 0 := by
    simpa only [biasBExt_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, one_mul] using logTwo_ne
  exact analyticAt_const.mul (analyticAt_atanhExt.add
    ((analyticAt_id.mul hE).div
      ((analyticAt_const.sub (analyticAt_id.pow 2)).mul analyticAt_biasBExt) hden))

theorem analyticAt_xParam : AnalyticAt ℂ xParam 0 := by
  unfold xParam
  exact (analyticAt_const.mul analyticAt_id).div
    (analyticAt_const.mul
      (Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ)) (by norm_num)))
    (by
      rw [Reflection.ComplexContactGerm.entropyExt_zero]
      exact mul_ne_zero (by norm_num) logTwo_ne)

theorem hasDerivAt_xParam_zero : CDeriv xParam (1 / 2) 0 := by
  have hE : CDeriv entropyExt 0 0 := by
    simpa [entropyDeriv] using hasDerivAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have h := ((hasDerivAt_const (𝕜 := ℂ) 0 (Real.log 2 : ℂ)).mul
    (hasDerivAt_id 0)).div
      ((hasDerivAt_const (𝕜 := ℂ) 0 2).mul hE) (by
        simp only [Pi.mul_apply, Reflection.ComplexContactGerm.entropyExt_zero]
        exact mul_ne_zero (by norm_num) logTwo_ne)
  convert! h using 1
  · simp only [Reflection.ComplexContactGerm.entropyExt_zero, id_eq,
      zero_mul, mul_zero, add_zero, sub_zero, Pi.mul_apply]
    field_simp [logTwo_ne]
    simpa using (div_self logTwo_ne).symm

theorem hasDerivAt_thetaParam_zero :
    CDeriv thetaParam (4 / (Real.log 2 : ℂ)) 0 := by
  have hp : CDeriv (fun z : ℂ => Complex.log (1 + z)) 1 0 := by
    have hi : CDeriv (fun z : ℂ => 1 + z) 1 0 := by
      convert (hasDerivAt_id (𝕜 := ℂ) 0).const_add 1 using 1 <;> simp [add_comm]
    have hc := (Complex.hasDerivAt_log (show 1 + (0 : ℂ) ∈ Complex.slitPlane by
      simpa using one_mem_slit)).comp (0 : ℂ) hi
    convert hc using 1
    · rfl
    · norm_num
  have hm : CDeriv (fun z : ℂ => Complex.log (1 - z)) (-1) 0 := by
    have hi := (hasDerivAt_id (𝕜 := ℂ) 0).const_sub 1
    have hc := (Complex.hasDerivAt_log (show 1 - (0 : ℂ) ∈ Complex.slitPlane by
      simpa using one_mem_slit)).comp (0 : ℂ) hi
    convert hc using 1
    · rfl
    · norm_num
  have hA : CDeriv atanhExt 1 0 := by
    convert! (hp.sub hm).div_const 2 using 1 <;> simp [atanhExt]
  have hE : CDeriv entropyExt 0 0 := by
    simpa [entropyDeriv] using hasDerivAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have hB : CDeriv biasBExt 0 0 := by
    have hs := ((hasDerivAt_id (𝕜 := ℂ) 0).pow 2).const_sub 1
    have hl := (Complex.hasDerivAt_log
      (show 1 - ((id : ℂ → ℂ) ^ 2) 0 ∈ Complex.slitPlane by
        simpa [id_eq] using one_mem_slit)).comp (0 : ℂ) hs
    convert! (hl.div_const 2).const_sub (Real.log 2 : ℂ) using 1 <;>
      simp [biasBExt]
  have hden := (((hasDerivAt_id (𝕜 := ℂ) 0).pow 2).const_sub 1).mul hB
  have hden0 : (1 - (0 : ℂ) ^ 2) * biasBExt 0 ≠ 0 := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      one_mul, biasBExt_zero] using logTwo_ne
  have hfrac := ((hasDerivAt_id (𝕜 := ℂ) 0).mul hE).div hden (by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using hden0)
  have h := (hA.add hfrac).const_mul (2 / (Real.log 2 : ℂ))
  convert! h using 1
  · simp only [Reflection.ComplexContactGerm.entropyExt_zero, biasBExt_zero,
      id_eq, zero_mul, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, one_mul, Pi.mul_apply, Pi.pow_apply]
    have hk : (Real.log 2 : ℂ) * (Real.log 2 : ℂ) /
        (Real.log 2 : ℂ) ^ 2 = 1 := by
      calc
        _ = (Real.log 2 : ℂ) / (Real.log 2 : ℂ) := by
          field_simp [logTwo_ne]
        _ = 1 := div_self logTwo_ne
    rw [hk]
    ring

private theorem deriv_thetaParam_zero :
    deriv thetaParam 0 = 4 / (Real.log 2 : ℂ) :=
  hasDerivAt_thetaParam_zero.deriv

private theorem deriv_thetaParam_ne : deriv thetaParam 0 ≠ 0 := by
  rw [deriv_thetaParam_zero]
  exact div_ne_zero (by norm_num) logTwo_ne

/-- Bias-coordinate inverse germ for the E8 slope parametrization. -/
noncomputable def biasGerm : ℂ → ℂ :=
  analyticAt_thetaParam.hasStrictDerivAt.localInverse thetaParam
    (deriv thetaParam 0) 0 deriv_thetaParam_ne

/-- The analytic inverse `Q` germ, still separate from the zero-filled `e8Q`. -/
noncomputable def qGerm (y : ℂ) : ℂ := xParam (biasGerm y)

@[simp] theorem biasGerm_zero : biasGerm 0 = 0 := by
  have h := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse deriv_thetaParam_ne
  simpa [biasGerm] using h.self_of_nhds

@[simp] theorem qGerm_zero : qGerm 0 = 0 := by simp [qGerm]

theorem analyticAt_biasGerm : AnalyticAt ℂ biasGerm 0 := by
  simpa [biasGerm] using
    analyticAt_thetaParam.analyticAt_localInverse deriv_thetaParam_ne

theorem hasDerivAt_biasGerm_zero :
    CDeriv biasGerm ((Real.log 2 : ℂ) / 4) 0 := by
  have h := analyticAt_thetaParam.hasStrictDerivAt.to_localInverse deriv_thetaParam_ne
  have hk : ((4 / (Real.log 2 : ℂ))⁻¹) = (Real.log 2 : ℂ) / 4 := by
    field_simp [logTwo_ne]
  simpa [biasGerm, deriv_thetaParam_zero, hk] using h.hasDerivAt

theorem analyticAt_qGerm : AnalyticAt ℂ qGerm 0 := by
  exact analyticAt_xParam.comp_of_eq analyticAt_biasGerm biasGerm_zero

/-- The analytic germ has the manuscript's exact linear coefficient. -/
theorem hasDerivAt_qGerm_zero :
    CDeriv qGerm ((Real.log 2 : ℂ) / 8) 0 := by
  have hx : CDeriv xParam (1 / 2) (biasGerm 0) := by
    simpa using hasDerivAt_xParam_zero
  have h := hx.comp (0 : ℂ) hasDerivAt_biasGerm_zero
  convert! h using 1
  · ring

/-- Factorial-normalized Taylor coefficient convention used by the finite
inverse-jet checker. -/
noncomputable def qTaylorCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n qGerm 0 / n.factorial

@[simp] theorem qTaylorCoeff_zero : qTaylorCoeff 0 = 0 := by
  simp [qTaylorCoeff, iteratedDeriv_zero]

/-- Concrete order-one connection between the analytic germ and the
factorial-normalized inverse jet. -/
theorem qTaylorCoeff_one :
    qTaylorCoeff 1 = (Real.log 2 : ℂ) / 8 := by
  rw [qTaylorCoeff, iteratedDeriv_one, hasDerivAt_qGerm_zero.deriv]
  norm_num

theorem eventually_thetaParam_biasGerm :
    ∀ᶠ y in nhds (0 : ℂ), thetaParam (biasGerm y) = y := by
  simpa [biasGerm, thetaParam_zero] using
    analyticAt_thetaParam.hasStrictDerivAt.eventually_right_inverse deriv_thetaParam_ne

/-- The locally chosen inverse bias coordinate inherits the exact odd symmetry. -/
theorem eventually_biasGerm_neg :
    ∀ᶠ y in nhds (0 : ℂ), biasGerm (-y) = -biasGerm y := by
  let g : ℂ → ℂ := fun y => -biasGerm (-y)
  have hleft := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse
    deriv_thetaParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), biasGerm (thetaParam x) = x at hleft
  have hneg : ∀ᶠ x in nhds (0 : ℂ),
      biasGerm (thetaParam (-x)) = -x := by
    have ht : Tendsto (fun z : ℂ => -z) (nhds 0) (nhds 0) := by
      simpa only [neg_zero] using continuous_neg.tendsto (0 : ℂ)
    exact ht hleft
  have hg : ∀ᶠ x in nhds (0 : ℂ), g (thetaParam x) = x := by
    filter_upwards [hneg] with x hx
    simp only [g, ← thetaParam_neg]
    rw [hx]
    simp
  have hu : ∀ᶠ y in nhds (0 : ℂ), g y = biasGerm y := by
    simpa [biasGerm] using
      (analyticAt_thetaParam.hasStrictDerivAt.hasStrictFDerivAt_equiv
        deriv_thetaParam_ne).localInverse_unique hg
  filter_upwards [hu] with y hy
  dsimp [g] at hy
  linear_combination -hy

/-- Consequently the analytic inverse contact germ is locally odd. -/
theorem eventually_qGerm_neg :
    ∀ᶠ y in nhds (0 : ℂ), qGerm (-y) = -qGerm y := by
  filter_upwards [eventually_biasGerm_neg] with y hy
  simp only [qGerm, hy, xParam_neg]

/-- Every even factorial-normalized Taylor coefficient of the odd analytic
germ vanishes.  In particular this supplies all even entries through the
order-17 inverse-jet ledger at once. -/
theorem qTaylorCoeff_eq_zero_of_even {n : ℕ} (hn : Even n) :
    qTaylorCoeff n = 0 := by
  have heq : (fun y : ℂ => qGerm (-y)) =ᶠ[nhds 0]
      (fun y : ℂ => -qGerm y) := eventually_qGerm_neg
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero] at hd
  have hp : (-1 : ℂ) ^ n = 1 := Even.neg_one_pow hn
  rw [hp, one_smul] at hd
  have hz : iteratedDeriv n qGerm 0 = 0 := by
    have htwo : (2 : ℂ) * iteratedDeriv n qGerm 0 = 0 := by
      linear_combination hd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  unfold qTaylorCoeff
  rw [hz]
  simp

end GeneralCK.E8AnalyticGerm
