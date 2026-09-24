import GeneralCK.ReflectionSmallBiasMonomialCurvature

/-! Real restriction of the candidate and its strict curvature lower bound. -/

namespace GeneralCK.Reflection.SmallBiasCandidate

open SmallBiasCoefficientBounds

noncomputable def realRows : List CoefficientRow → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | r :: rs, a, b => coefficient r * b^(2*r.j+1) * weightedBase (2*r.i) b a + realRows rs a b

noncomputable def firstRows : List CoefficientRow → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | r :: rs, a, b => coefficient r * b^(2*r.j+1) * weightedFirst (2*r.i) b a + firstRows rs a b

noncomputable def secondRows : List CoefficientRow → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | r :: rs, a, b => coefficient r * b^(2*r.j+1) * weightedSecond (2*r.i) b a + secondRows rs a b

noncomputable def realPolynomial (a b : ℝ) : ℝ := realRows SmallBiasCoefficientData.rows a b

theorem realRows_cast (rs : List CoefficientRow) (a b : ℝ) :
    (realRows rs a b : ℂ) = (a:ℂ)*(b:ℂ)*((a:ℂ)^2-(b:ℂ)^2)^2*quotient rs ((a:ℂ),(b:ℂ)) := by
  induction rs with
  | nil => simp [realRows,quotient]
  | cons r rs ih =>
    simp only [realRows,quotient,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,ih]
    simp only [weightedBase,base,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_pow,pow_add,pow_one]
    ring

theorem realPolynomial_cast (a b : ℝ) :
    (realPolynomial a b : ℂ) = polynomial ((a:ℂ),(b:ℂ)) :=
  realRows_cast _ a b

theorem hasDerivAt_realRows (rs : List CoefficientRow) (a b : ℝ) :
    HasDerivAt (fun x => realRows rs x b) (firstRows rs a b) a := by
  induction rs with
  | nil => exact hasDerivAt_const a 0
  | cons r rs ih =>
    exact ((hasDerivAt_weightedBase (2*r.i) b a).const_mul (coefficient r*b^(2*r.j+1))).add ih

theorem hasDerivAt_firstRows (rs : List CoefficientRow) (a b : ℝ) :
    HasDerivAt (fun x => firstRows rs x b) (secondRows rs a b) a := by
  induction rs with
  | nil => exact hasDerivAt_const a 0
  | cons r rs ih =>
    exact ((hasDerivAt_weightedFirst (2*r.i) b a).const_mul (coefficient r*b^(2*r.j+1))).add ih

theorem deriv2_realPolynomial (a b : ℝ) :
    deriv (deriv (fun x => realPolynomial x b)) a = secondRows SmallBiasCoefficientData.rows a b := by
  have he : deriv (fun x => realPolynomial x b) = fun x => firstRows SmallBiasCoefficientData.rows x b :=
    funext (fun x => (hasDerivAt_realRows _ x b).deriv)
  rw [he]
  exact (hasDerivAt_firstRows _ a b).deriv

theorem secondRows_nonneg (rs : List CoefficientRow) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hc : ∀ r ∈ rs, 0 ≤ coefficient r) : 0 ≤ secondRows rs a b := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := hc r (by simp)
    have hrest := ih (fun s hs => hc s (by simp [hs]))
    exact add_nonneg (mul_nonneg (mul_nonneg hr (pow_nonneg hb _))
      (weightedSecond_nonneg _ ha hb hba)) hrest

theorem realPolynomial_curvature_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (16/25:ℝ)*a^3*b < deriv (deriv (fun x => realPolynomial x b)) a := by
  rw [deriv2_realPolynomial]
  let rs := SmallBiasCoefficientData.rows.tail
  let r0 : CoefficientRow := ⟨0,0,SmallBiasCoefficientData.q_0_0⟩
  have hrows : SmallBiasCoefficientData.rows = r0 :: rs := rfl
  have hc : (2/25:ℝ) < coefficient r0 := SmallBiasCoefficientData.constant_coefficient_lower
  have hc0 : 0 ≤ coefficient r0 := by linarith
  have hrest : 0 ≤ secondRows rs a b := secondRows_nonneg rs ha hb.le hba (fun r hr => by
    exact (SmallBiasCoefficientData.all_coefficients_positive r (List.mem_of_mem_tail hr)).1.le)
  have hbase := weightedSecond_lower 0 ha hb.le hba
  have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg hc0 hb.le)
  have hstrict := mul_lt_mul_of_pos_right hc (show 0 < 8*a^3*b by positivity)
  rw [hrows]
  change _ < coefficient r0 * b^(2*0+1) * weightedSecond (2*0) b a + secondRows rs a b
  norm_num only [Nat.mul_zero,Nat.zero_add,pow_one] at *
  nlinarith

end GeneralCK.Reflection.SmallBiasCandidate
