import GeneralCK.Certificates.E8ComplexBallKernel

/-! Principal-log enclosures on the exact E8 contact disc. -/

namespace GeneralCK.Certificates.E8ComplexLogEnclosures

open E8ComplexBallKernel

noncomputable def contactRadius : ℝ := 1103 / 2500
noncomputable def squareRadius : ℝ := contactRadius ^ 2

theorem log_one_add_contact_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 + c)) (Complex.logTaylor 13 c)
      (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) := by
  exact log_one_add_taylor12 hc (by norm_num [contactRadius])

theorem log_one_sub_contact_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 - c)) (Complex.logTaylor 13 (-c))
      (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) := by
  apply log_one_add_taylor12 (z := -c)
  · simpa [contactRadius] using hc
  · norm_num [contactRadius]

theorem log_one_sub_square_taylor12 {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 - c ^ 2)) (Complex.logTaylor 13 (-(c ^ 2)))
      (squareRadius ^ 13 * (1 - squareRadius)⁻¹ / 13) := by
  apply log_one_add_taylor12 (z := -(c ^ 2))
  · rw [norm_neg, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg c) hc 2
  · norm_num [squareRadius, contactRadius]

/-- The three principal logarithms needed by `thetaParam` are therefore
reduced to degree-12 complex polynomial evaluation plus explicit rational
ball radii. -/
theorem e8_three_logs_enclosed {c : ℂ} (hc : ‖c‖ ≤ contactRadius) :
    InBall (Complex.log (1 + c)) (Complex.logTaylor 13 c)
        (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) ∧
    InBall (Complex.log (1 - c)) (Complex.logTaylor 13 (-c))
        (contactRadius ^ 13 * (1 - contactRadius)⁻¹ / 13) ∧
    InBall (Complex.log (1 - c ^ 2)) (Complex.logTaylor 13 (-(c ^ 2)))
        (squareRadius ^ 13 * (1 - squareRadius)⁻¹ / 13) :=
  ⟨log_one_add_contact_taylor12 hc, log_one_sub_contact_taylor12 hc,
    log_one_sub_square_taylor12 hc⟩

end GeneralCK.Certificates.E8ComplexLogEnclosures
