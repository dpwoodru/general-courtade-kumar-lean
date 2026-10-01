import GeneralCK.Certificates.E8ComplexLogBoxChecker
import GeneralCK.Certificates.E8ThetaTauDerivativeFormula

/-! An elementary, interval-checker-facing formula for `deriv thetaParam`. -/

namespace GeneralCK.Certificates.E8ThetaParamDerivativeExplicit

open E8AnalyticGerm
open Reflection.ComplexEntropy
open E8ThetaTauAnalytic

noncomputable def thetaParamDerivExplicit (c : ℂ) : ℂ :=
  let B := biasBExt c
  let E := entropyExt c
  let E' := entropyDeriv c
  let den := (1 - c ^ 2) * B
  let den' := (-2 * c) * B + (1 - c ^ 2) * (c / (1 - c ^ 2))
  (2 / (Real.log 2 : ℂ)) *
    ((1 - c ^ 2)⁻¹ +
      (((E + c * E') * den - (c * E) * den') / den ^ 2))

/-- The same expression with its three logarithm values exposed as inputs
for the rational-ball checker. -/
noncomputable def thetaParamDerivFromLogs
    (c lp lm ls L : ℂ) : ℂ :=
  let B := L - ls / 2
  let E := L - ((1 + c) * lp + (1 - c) * lm) / 2
  let E' := (lm - lp) / 2
  let den := (1 - c ^ 2) * B
  let den' := (-2 * c) * B + (1 - c ^ 2) * (c / (1 - c ^ 2))
  (2 / L) * ((1 - c ^ 2)⁻¹ +
    (((E + c * E') * den - (c * E) * den') / den ^ 2))

theorem explicit_eq_from_logs (c : ℂ) :
    thetaParamDerivExplicit c = thetaParamDerivFromLogs c
      (Complex.log (1 + c)) (Complex.log (1 - c))
      (Complex.log (1 - c ^ 2)) (Real.log 2 : ℂ) := by
  simp only [thetaParamDerivExplicit, thetaParamDerivFromLogs, biasBExt,
    entropyExt, entropyDeriv]

theorem deriv_thetaParam_eq_explicit {c : ℂ}
    (hc : ‖c‖ ≤ (1103 / 2500 : ℝ)) :
    deriv thetaParam c = thetaParamDerivExplicit c := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hc20 : (1 - c ^ 2 : ℂ) ≠ 0 := by
    intro heq
    have heq' : c ^ 2 = 1 := (eq_of_sub_eq_zero heq).symm
    have hn := congrArg norm heq'
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg c]
  have hp : HasDerivAt (fun z : ℂ => Complex.log (1 + z)) (1 + c)⁻¹ c := by
    simpa only [one_div] using
      (Complex.hasDerivAt_log (Complex.mem_slitPlane_of_norm_lt_one hc1)).comp_const_add 1 c
  have hminus : HasDerivAt (fun z : ℂ => 1 - z) (-1) c := by
    simpa using (hasDerivAt_id c).const_sub 1
  have hm : HasDerivAt (fun z : ℂ => Complex.log (1 - z)) (-(1 - c)⁻¹) c := by
    have hs : 1 - c ∈ Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc1))
    have hcomp := (Complex.hasDerivAt_log hs).comp c hminus
    change HasDerivAt (fun z : ℂ => Complex.log (1 - z)) ((1 - c)⁻¹ * (-1)) c at hcomp
    convert hcomp using 1 <;> ring
  have hA : HasDerivAt atanhExt (1 - c ^ 2)⁻¹ c := by
    have h := (hp.sub hm).div_const 2
    change HasDerivAt atanhExt (((1 + c)⁻¹ - -(1 - c)⁻¹) / 2) c at h
    convert h using 1
    have hp0 : (1 + c : ℂ) ≠ 0 :=
        Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hc1)
    have hm0 : (1 - c : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (by
          simpa only [sub_eq_add_neg] using
            (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc1)))
    rw [inv_eq_one_div]
    field_simp [hp0, hm0, hc20]
    ring
  have hE := hasDerivAt_entropyExt hc1
  have harg : HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-2 * c) c := by
    have h := ((hasDerivAt_id c).pow 2).const_sub 1
    change HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-(2 * c ^ (2 - 1) * 1)) c at h
    convert h using 1 <;> norm_num
  have hlog : HasDerivAt (fun z : ℂ => Complex.log (1 - z ^ 2))
      ((1 - c ^ 2)⁻¹ * (-2 * c)) c :=
    (Complex.hasDerivAt_log (by
      simpa only [sub_eq_add_neg] using
        (Complex.mem_slitPlane_of_norm_lt_one (z := -(c ^ 2)) (by
          rw [norm_neg, norm_pow]
          nlinarith [norm_nonneg c])))).comp c harg
  have hB : HasDerivAt biasBExt (c / (1 - c ^ 2)) c := by
    have h := (hlog.div_const 2).const_sub (Real.log 2 : ℂ)
    change HasDerivAt biasBExt (-((1 - c ^ 2)⁻¹ * (-2 * c) / 2)) c at h
    convert h using 1
    field_simp [hc20]
  have hden := (((hasDerivAt_id c).pow 2).const_sub 1).mul hB
  have hden0 : (1 - c ^ 2) * biasBExt c ≠ 0 := mul_ne_zero
    (by
      intro heq
      have heq' : c ^ 2 = 1 := (eq_of_sub_eq_zero heq).symm
      have hn := congrArg norm heq'
      rw [norm_pow, norm_one] at hn
      nlinarith [norm_nonneg c])
    (biasBExt_ne_on_half_disc hc)
  have hnum := (hasDerivAt_id c).mul hE
  have hfrac := hnum.div hden hden0
  have h := (hA.add hfrac).const_mul (2 / (Real.log 2 : ℂ))
  change HasDerivAt thetaParam _ c at h
  rw [h.deriv]
  simp only [thetaParamDerivExplicit, id_eq, Pi.mul_apply, Pi.pow_apply,
    one_mul, pow_one, Nat.cast_ofNat]
  congr 1
  field_simp [hden0, hc20]
  ring

theorem checkLogs_connects_derivative {cBall : E8GaussianRatBall.RatBall} {c : ℂ}
    (hcBall : cBall.Holds c) (hc : ‖c‖ ≤ (1103 / 2500 : ℝ)) :
    let boxes := E8ComplexLogBoxChecker.checkLogs cBall
    boxes.plus.Holds (Complex.log (1 + c)) ∧
    boxes.minus.Holds (Complex.log (1 - c)) ∧
    boxes.square.Holds (Complex.log (1 - c ^ 2)) ∧
    deriv thetaParam c = thetaParamDerivFromLogs c
      (Complex.log (1 + c)) (Complex.log (1 - c))
      (Complex.log (1 - c ^ 2)) (Real.log 2 : ℂ) := by
  have hc' : ‖c‖ ≤ (E8ComplexLogBoxChecker.contactRadiusQ : ℝ) := by
    simpa [E8ComplexLogBoxChecker.contactRadiusQ] using hc
  have hlogs := E8ComplexLogBoxChecker.checkLogs_sound hcBall hc'
  exact ⟨hlogs.1, hlogs.2.1, hlogs.2.2,
    (deriv_thetaParam_eq_explicit hc).trans (explicit_eq_from_logs c)⟩

end GeneralCK.Certificates.E8ThetaParamDerivativeExplicit
