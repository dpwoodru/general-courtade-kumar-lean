import CKLaneA3X.Identify

/-!
# CKLaneA3X.Formula — algebraic identities for the final congr steps (R, W, coef, m11)
-/

namespace CKLaneA3X

open GeneralCK GeneralCK.Correction

/-- `regularFsGap = Fs(c)/(w-u)` with `c = contact`. -/
theorem regularFsGap_contact {t ρ : ℝ} (hd : Dom t ρ) :
    HighU.regularFsGap (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      Natural.Fs (Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t)) /
        ((1 / 2 - (1 - ρ) * t) - (1 / 2 - t)) := by
  have h := HighU.regularFsGap_mul_gap (1 / 2 - t) (1 / 2 - (1 - ρ) * t)
  have hne : (1 / 2 - (1 - ρ) * t) - (1 / 2 - t) ≠ 0 := sub_ne_zero.mpr (dom_u_lt_w hd).ne'
  have hb : HighU.regularBias (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t) := by
    rw [HighU.regularBias.eq_1, HighU.contact_eq_regularContact (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)]
  rw [hb] at h
  rw [eq_div_iff hne, mul_comm]; exact h

theorem regularWeight_contact {t ρ : ℝ} (hd : Dom t ρ) :
    HighU.regularWeight (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      2 * Natural.Fss (Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t))
        (Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t)) := by
  have hb : HighU.regularBias (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t) := by
    rw [HighU.regularBias.eq_1, HighU.contact_eq_regularContact (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)]
  unfold HighU.regularWeight; rw [hb]

/-- facts about the contact on the domain -/
theorem contact_facts {t ρ : ℝ} (hd : Dom t ρ) :
    let c := Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t)
    c ≠ 0 ∧ |c| < 1 ∧ 1 - c * c ≠ 0 ∧ Certificates.Reflection.biasB c ≠ 0 := by
  intro c
  obtain ⟨hc0, hc1, _⟩ := contact_eqn hd
  have habs : |c| < 1 := by rw [abs_of_pos hc0]; exact hc1
  refine ⟨hc0.ne', habs, ?_, (biasB_pos habs).ne'⟩
  have : c * c < 1 := by nlinarith
  linarith

theorem entropySum_pos' {t ρ : ℝ} (hd : Dom t ρ) :
    0 < Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t) := by
  have h1 := hd.1; have h2 := hd.2.1; have h3 := hd.2.2.1; have h4 := hd.2.2.2
  have hT : (Tq : ℝ) = 3 / 10 := by norm_num [Tq]
  unfold Natural.entropySum
  rw [hn_eq_binEntropy, hn_eq_binEntropy]
  have hp : 0 < (1 - ρ) * t := mul_pos (by linarith) h1
  have a1 : 0 < Real.binEntropy (1 / 2 - t) := Real.binEntropy_pos (by linarith) (by linarith)
  have a2 : 0 < Real.binEntropy (1 / 2 - (1 - ρ) * t) := Real.binEntropy_pos (by nlinarith) (by linarith)
  linarith

theorem jn_u_ne {t ρ : ℝ} (hd : Dom t ρ) : Natural.jn (1 / 2 - t) ≠ 0 :=
  HighU.natural_jn_nonzero (dom_u_pos hd) (by linarith [hd.1])

theorem jn_w_ne {t ρ : ℝ} (hd : Dom t ρ) : Natural.jn (1 / 2 - (1 - ρ) * t) ≠ 0 :=
  HighU.natural_jn_nonzero ((dom_u_pos hd).trans (dom_u_lt_w hd)) (dom_w_lt hd)

theorem jn_add_dslope {t ρ : ℝ} (hd : Dom t ρ) :
    Natural.jn (1 / 2 - t) + ((1 / 2 - (1 - ρ) * t) - (1 / 2 - t)) *
      dslope Natural.jn (1 / 2 - t) (1 / 2 - (1 - ρ) * t) = Natural.jn (1 / 2 - (1 - ρ) * t) := by
  have hne : 1 / 2 - (1 - ρ) * t ≠ 1 / 2 - t := (dom_u_lt_w hd).ne'
  rw [dslope_of_ne _ hne, slope_def_field]
  have hd' : (1 / 2 - (1 - ρ) * t) - (1 / 2 - t) ≠ 0 := sub_ne_zero.mpr hne
  rw [mul_comm, div_mul_cancel₀ _ hd']
  ring

/-- the determinant coefficient in the regular (J'-free denominator) form -/
theorem detGap_regular (d q h J j R W S Jw : ℝ) (hJ : J ≠ 0) (hJw : Jw ≠ 0) (hS : S ≠ 0)
    (hjw : J + d * j = Jw) :
    HighU.detGapCoefficient d q h J j R W S =
      (q + (q + h * d - d ^ 2) + d * ((q * (j + 2 * R) - 1) / J + d) - W * (-q * (1 + d * J / S)) ^ 2) *
        (2 * Jw + ((q * (j + 2 * R) - 1) * j - (h - d) * (j + 2 * R) * J) / J -
          Jw * W * (h - d - (q * J + (q + h * d - d ^ 2) * Jw) / S) ^ 2) -
      Jw * ((q * (j + 2 * R) - 1) / J + d - W * (-q * (1 + d * J / S)) *
          (h - d - (q * J + (q + h * d - d ^ 2) * Jw) / S)) ^ 2 := by
  unfold HighU.detGapCoefficient
  simp only []
  rw [hjw]
  field_simp

end CKLaneA3X
