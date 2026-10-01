import GeneralCK.Certificates.E8ElementaryCoeff13
import GeneralCK.Certificates.E8ParamCoeff9
import GeneralCK.Certificates.E8ParamCoeff11

namespace GeneralCK.Certificates.E8ParamCoeff13

open Filter
open E8AnalyticGerm Reflection.ComplexEntropy Reflection.ComplexContactFactor
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5 E8ElementaryCoeff7 E8ElementaryCoeff9 E8ElementaryCoeff11
open E8ElementaryCoeff13
open E8ParamCoeff5 E8ParamCoeff7 E8ParamCoeff9 E8ParamCoeff11 E8ComposeCoeff13

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

private theorem eventually_entropy_mul_xParam :
    (fun z : ℂ => entropyExt z * xParam z) =ᶠ[nhds 0]
      (fun z => (Real.log 2 : ℂ) * z / 2) := by
  have h0 : entropyExt 0 ≠ 0 := by
    rw [Reflection.ComplexContactGerm.entropyExt_zero]
    exact logTwo_ne
  have hE := (Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ))
    (by norm_num)).continuousAt.eventually_ne h0
  filter_upwards [hE] with z hz
  simp only [xParam]
  field_simp [hz]

private theorem coeff_entropy_odd (n : ℕ) (hn : Odd n) : coeff entropyExt n = 0 :=
  coeff_even_zero_of_odd entropyExt_neg hn
private theorem coeff_xParam_even (n : ℕ) (hn : Even n) : coeff xParam n = 0 :=
  coeff_odd_zero_of_even xParam_neg hn

theorem coeff_xParam_thirteen : coeff xParam 13 =
    1 / (264 * (Real.log 2 : ℂ)) + 383 / (50400 * (Real.log 2 : ℂ)^2) +
      1349 / (120960 * (Real.log 2 : ℂ)^3) + 13 / (960 * (Real.log 2 : ℂ)^4) +
      5 / (384 * (Real.log 2 : ℂ)^5) + 1 / (128 * (Real.log 2 : ℂ)^6) := by
  have hp := coeff_mul entropyExt xParam
    (Reflection.ComplexContactGerm.analyticAt_entropyExt (by norm_num)) analyticAt_xParam 13
  have he := coeff_congr eventually_entropy_mul_xParam 13
  change coeff (fun z : ℂ => entropyExt z * xParam z) 13 = _ at hp
  rw [hp] at he
  norm_num [Finset.sum_range_succ, coeff_entropyExt_zero, coeff_entropyExt_two,
    coeff_entropyExt_four, coeff_entropyExt_six, coeff_entropyExt_eight,
    coeff_entropyExt_ten, coeff_entropyExt_twelve, coeff_entropy_odd,
    coeff_xParam_one, coeff_xParam_three,
    coeff_xParam_five, coeff_xParam_seven, coeff_xParam_nine,
    coeff_xParam_eleven, coeff_xParam_even] at he
  rw [coeff_entropy_odd 3 (by decide), coeff_entropy_odd 5 (by decide),
    coeff_entropy_odd 7 (by decide), coeff_entropy_odd 9 (by decide),
    coeff_xParam_even 4 (by decide), coeff_xParam_even 6 (by decide),
    coeff_xParam_even 8 (by decide), coeff_xParam_even 10 (by decide)] at he
  norm_num at he
  have hr : coeff (fun z : ℂ => (Real.log 2 : ℂ) * z / 2) 13 = 0 := by
    rw [coeff, iteratedDeriv_div_const, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id_zero]
  rw [clogTwo_eq] at he
  rw [hr] at he
  apply mul_left_cancel₀ logTwo_ne
  ring_nf at he ⊢
  have hi0 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ logTwo_ne
  have hi1 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^2 =
      (Real.log 2 : ℂ)⁻¹ := by field_simp [logTwo_ne]
  have hi2 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^3 =
      (Real.log 2 : ℂ)⁻¹^2 := by field_simp [logTwo_ne]
  have hi3 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^4 =
      (Real.log 2 : ℂ)⁻¹^3 := by field_simp [logTwo_ne]
  have hi4 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^5 =
      (Real.log 2 : ℂ)⁻¹^4 := by field_simp [logTwo_ne]
  have hi5 : (Real.log 2 : ℂ) * (Real.log 2 : ℂ)⁻¹^6 =
      (Real.log 2 : ℂ)⁻¹^5 := by field_simp [logTwo_ne]
  linear_combination he - (1 / 264) * hi0 - (383 / 50400) * hi1 -
    (1349 / 120960) * hi2 - (13 / 960) * hi3 - (5 / 384) * hi4 -
    (1 / 128) * hi5

private theorem deriv_xParam_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

private theorem eventually_xBias_xParam :
    (xBiasGerm ∘ xParam) =ᶠ[nhds (0 : ℂ)] id := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x
  simpa only [xBiasGerm] using h

theorem coeff_xBiasGerm_thirteen : coeff xBiasGerm 13 =
    -2048 / (33*(Real.log 2 : ℂ)) + 392192 / (525*(Real.log 2 : ℂ)^2) -
      3798784 / (945*(Real.log 2 : ℂ)^3) + 36608 / (3*(Real.log 2 : ℂ)^4) -
      21120 / (Real.log 2 : ℂ)^5 + 16896 / (Real.log 2 : ℂ)^6 := by
  have hc := coeff_comp xBiasGerm xParam analyticAt_xBiasGerm analyticAt_xParam
    xParam_zero 13
  have hi := coeff_congr eventually_xBias_xParam 13
  have hid : coeff id 13 = 0 := by rw [coeff, iteratedDeriv_id]; norm_num
  rw [hc, composeCoeff_thirteen_odd (coeff xBiasGerm) (coeff xParam)
    (coeff_xBiasGerm_even (by decide : Even 2))
    (coeff_xBiasGerm_even (by decide : Even 4))
    (coeff_xBiasGerm_even (by decide : Even 6))
    (coeff_xBiasGerm_even (by decide : Even 8))
    (coeff_xBiasGerm_even (by decide : Even 10))
    (by simp [coeff, xParam_zero]) (coeff_xParam_even 2 (by decide))
    (coeff_xParam_even 4 (by decide)) (coeff_xParam_even 6 (by decide))
    (coeff_xParam_even 8 (by decide)) (coeff_xParam_even 10 (by decide))
    (coeff_xParam_even 12 (by decide)), hid] at hi
  rw [coeff_xParam_one, coeff_xParam_three, coeff_xParam_five, coeff_xParam_seven,
    coeff_xParam_nine, coeff_xParam_eleven, coeff_xParam_thirteen, coeff_xBiasGerm_one,
    coeff_xBiasGerm_three, coeff_xBiasGerm_five, coeff_xBiasGerm_seven,
    coeff_xBiasGerm_nine, coeff_xBiasGerm_eleven] at hi
  ring_nf at hi ⊢
  linear_combination 8192 * hi

end GeneralCK.Certificates.E8ParamCoeff13
