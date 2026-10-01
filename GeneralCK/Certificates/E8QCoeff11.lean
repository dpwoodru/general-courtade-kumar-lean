import GeneralCK.Certificates.E8ThetaParamCoeff11

namespace GeneralCK.Certificates.E8QCoeff11

open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9 E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ComposeCoeff11 E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem thetaTaylorCoeff_even (n : ℕ) (hn : Even n) :
    thetaTaylorCoeff n = 0 := by
  have heq : (fun z : ℂ => thetaGerm (-z)) =ᶠ[nhds 0]
      (fun z => -thetaGerm z) := by
    filter_upwards [eventually_xBiasGerm_neg] with z hz
    simp only [thetaGerm, hz, thetaParam_neg]
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold thetaTaylorCoeff
  have hz : iteratedDeriv n thetaGerm 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

private theorem clogTwo_eq : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm
private theorem clogTwo_ne : Complex.log (2 : ℂ) ≠ 0 := by
  rw [clogTwo_eq]
  exact logTwo_ne

set_option maxHeartbeats 0 in
theorem qTaylorCoeff_eleven_formula :
    qTaylorCoeff 11 = (q11Formula (Real.log 2) : ℂ) := by
  have hc := composeCoeff_theta_q 11
  rw [composeCoeff_eleven_odd thetaTaylorCoeff qTaylorCoeff
    (thetaTaylorCoeff_even 2 (by decide)) (thetaTaylorCoeff_even 4 (by decide))
    (thetaTaylorCoeff_even 6 (by decide)) (thetaTaylorCoeff_even 8 (by decide))
    qTaylorCoeff_zero (qTaylorCoeff_eq_zero_of_even (by decide : Even 2))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 4))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 6))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 8))
    (qTaylorCoeff_eq_zero_of_even (by decide : Even 10))] at hc
  rw [thetaTaylorCoeff_one, thetaTaylorCoeff_three, thetaTaylorCoeff_five,
    thetaTaylorCoeff_seven, thetaTaylorCoeff_nine, thetaTaylorCoeff_eleven,
    qTaylorCoeff_one, qTaylorCoeff_three_formula, qTaylorCoeff_five_formula,
    qTaylorCoeff_seven_formula, qTaylorCoeff_nine_formula] at hc
  rw [q7Formula, q9Formula] at hc
  push_cast at hc
  norm_num [targetCoeff] at hc
  rw [clogTwo_eq] at hc
  change qTaylorCoeff 11 = ((q11Formula (Real.log 2) : ℝ) : ℂ)
  rw [q11Formula]
  push_cast
  have hc' := congrArg (fun z => z * (Real.log 2 : ℂ)) hc
  field_simp [logTwo_ne] at hc' ⊢
  simp [mul_assoc, mul_left_comm, mul_comm] at hc' ⊢
  rcases hc' with (hzero | hc') | hzero
  · exact (clogTwo_ne hzero).elim
  · ring_nf at hc' ⊢
    linear_combination
      (1 / 157959891389528613059306980962100838400000) * hc'
  · exact (clogTwo_ne hzero).elim

theorem inverseStep_eleven_formula :
    inverseStep thetaTaylorCoeff qTaylorCoeff 11 = (q11Formula (Real.log 2) : ℂ) := by
  rw [← qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 11)]
  exact qTaylorCoeff_eleven_formula

theorem qTaylorCoeff_eleven_in_sourceBox :
    ‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤ (sourceHalfWidth 11 : ℝ) := by
  rw [qTaylorCoeff_eleven_formula]
  exact norm_sub_sourceCenter_le_of_real_endpoint_bounds rfl
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.1.1
    (formula_endpoints_of_lipschitz formulaLipschitzTrace).2.2.1.2

end GeneralCK.Certificates.E8QCoeff11
