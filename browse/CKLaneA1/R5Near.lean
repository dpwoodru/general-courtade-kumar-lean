import CKLaneA1.R5Cell

/-!
# CKLaneA1.R5Near — `Psi = Θ'(contact)` near `v = 1/2` (analytic)

With `y = 1 − 2v`, `z = y²`, `L = log 2`, `η = L − hn v`, `μ = kap v − L`:
* Taylor: `|2η − y² − (2/3)y⁴| ≤ 2y⁴/(1−y)` (`eta_bounds`), `z/2 ≤ μ ≤ z/(2(1−z))` (`mu_bounds`);
* `Psi v = 4 hn³ (2 kap − z) / (L² (1−z)² kap³)` (`psi_eq`);
* for `y ≤ 201/10000`: `θ₀(1 − 2.43 z) ≤ Psi v ≤ θ₀(1 − 1.78 z)`, `θ₀ = 8/L` (`psi_near`).
The core estimate (`near_core`) is a univariate polynomial inequality in `u = z/L` after normalizing
`p = hn/L`, `q = kap/L`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

theorem log_taylor3 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    |Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y) ∧
      |Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y) := by
  have h1 := Real.abs_log_sub_add_sum_range_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1) 3
  have h2 := Real.abs_log_sub_add_sum_range_le (x := -y)
    (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1) 3
  rw [abs_of_nonneg hy0] at h1
  rw [abs_neg, abs_of_nonneg hy0, sub_neg_eq_add] at h2
  have e1 : ∑ i ∈ Finset.range 3, y ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 - y) =
      Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  have e2 : ∑ i ∈ Finset.range 3, (-y) ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 + y) =
      Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem two_eta_eq {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    2 * (Real.log 2 - hn v) = (1 + (1 - 2 * v)) * Real.log (1 + (1 - 2 * v)) +
      (1 - (1 - 2 * v)) * Real.log (1 - (1 - 2 * v)) := by
  have e1 : 1 + (1 - 2 * v) = 2 * (1 - v) := by ring
  have e2 : 1 - (1 - 2 * v) = 2 * v := by ring
  rw [e1, e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) hv0.ne']
  unfold hn
  ring

theorem eta_bounds {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    (1 - 2 * v) ^ 2 / 2 + (1 - 2 * v) ^ 4 / 3 - (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) ≤
        Real.log 2 - hn v ∧
      Real.log 2 - hn v ≤
        (1 - 2 * v) ^ 2 / 2 + (1 - 2 * v) ^ 4 / 3 + (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) := by
  have hy0 : 0 ≤ 1 - 2 * v := by linarith
  have hy1 : 1 - 2 * v < 1 := by linarith
  obtain ⟨h1, h2⟩ := log_taylor3 hy0 hy1
  have he := two_eta_eq hv0 (by linarith)
  generalize 1 - 2 * v = y at *
  rw [abs_le] at h1 h2
  have key : 2 * (Real.log 2 - hn v) - y ^ 2 - 2 / 3 * y ^ 4 =
      (1 + y) * (Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3)) +
        (1 - y) * (Real.log (1 - y) + (y + y ^ 2 / 2 + y ^ 3 / 3)) := by
    rw [he]; ring
  have a1 := mul_le_mul_of_nonneg_left h2.2 (show (0 : ℝ) ≤ 1 + y by linarith)
  have a2 := mul_le_mul_of_nonneg_left h1.2 (show (0 : ℝ) ≤ 1 - y by linarith)
  have b1 := mul_le_mul_of_nonneg_left h2.1 (show (0 : ℝ) ≤ 1 + y by linarith)
  have b2 := mul_le_mul_of_nonneg_left h1.1 (show (0 : ℝ) ≤ 1 - y by linarith)
  have e3 : (1 + y) * (y ^ 4 / (1 - y)) + (1 - y) * (y ^ 4 / (1 - y)) = 2 * (y ^ 4 / (1 - y)) := by
    ring
  have e4 : (1 + y) * -(y ^ 4 / (1 - y)) + (1 - y) * -(y ^ 4 / (1 - y)) =
      -(2 * (y ^ 4 / (1 - y))) := by ring
  constructor <;> linarith

theorem mu_bounds {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    (1 - 2 * v) ^ 2 / 2 ≤ kap v - Real.log 2 ∧
      kap v - Real.log 2 ≤ (1 - 2 * v) ^ 2 / (2 * (1 - (1 - 2 * v) ^ 2)) := by
  have hq : 0 < 1 - (1 - 2 * v) ^ 2 := by nlinarith
  have e : kap v - Real.log 2 = -Real.log (1 - (1 - 2 * v) ^ 2) / 2 := by
    unfold kap
    have h4 : v * (1 - v) = (1 - (1 - 2 * v) ^ 2) / 4 := by ring
    rw [h4, Real.log_div hq.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [e]
  generalize (1 - 2 * v) ^ 2 = z at *
  have hq' : 1 - z ≠ 0 := hq.ne'
  have l1 := Real.log_le_sub_one_of_pos hq
  have l2 := Real.one_sub_inv_le_log_of_pos hq
  constructor
  · linarith
  · have e2 : 1 + z / (1 - z) = (1 - z)⁻¹ := by
      rw [inv_eq_one_div, eq_div_iff hq', add_mul, div_mul_cancel₀ _ hq']; ring
    rw [← e2] at l2
    have e3 : z / (2 * (1 - z)) = z / (1 - z) / 2 := by rw [div_div, mul_comm (1 - z) 2]
    rw [e3]
    linarith

theorem psi_eq {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) :
    Psi v = 4 * hn v ^ 3 * (2 * kap v - (1 - 2 * v) ^ 2) /
      (Real.log 2 ^ 2 * (1 - (1 - 2 * v) ^ 2) ^ 2 * kap v ^ 3) := by
  unfold Psi
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hHv : H v = hn v / Real.log 2 := by rw [hn_eq_H_mul_log]; field_simp
  rw [hHv]
  have hk : kap v ≠ 0 := (kap_pos hv0 hv).ne'
  have hq : 1 - (1 - 2 * v) ^ 2 ≠ 0 := by nlinarith
  have e : 4 * v * (1 - v) = 1 - (1 - 2 * v) ^ 2 := by ring
  rw [e]
  first | (field_simp; done) | (field_simp; ring)

/-- Powers of a small nonnegative number. -/
theorem pow_succ_le_small {u ε : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ ε) :
    ∀ n : ℕ, u ^ (n + 1) ≤ ε ^ n * u
  | 0 => by simp
  | n + 1 => by
    have ih := pow_succ_le_small hu0 hu n
    have hε : 0 ≤ ε := hu0.trans hu
    calc u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
      _ ≤ (ε ^ n * u) * ε := mul_le_mul ih hu hu0 (by positivity)
      _ = ε ^ (n + 1) * u := by ring

set_option maxHeartbeats 1000000 in
/-- The core polynomial estimate. -/
theorem near_core {L h k z : ℝ} (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808)
    (hz0 : 0 < z) (hz1 : z ≤ 1 / 2400)
    (he1 : z / 2 - 3 / 4 * z ^ 2 ≤ L - h) (he2 : L - h ≤ z / 2 + 7 / 5 * z ^ 2)
    (hm1 : z / 2 ≤ k - L) (hm2 : k - L ≤ z / 2 + z ^ 2) :
    8 / L * (1 - 243 / 100 * z) ≤ 4 * h ^ 3 * (2 * k - z) / (L ^ 2 * (1 - z) ^ 2 * k ^ 3) ∧
      4 * h ^ 3 * (2 * k - z) / (L ^ 2 * (1 - z) ^ 2 * k ^ 3) ≤ 8 / L * (1 - 178 / 100 * z) := by
  have hL0 : 0 < L := by linarith
  have hL7 : L ≤ 7 / 10 := by linarith
  obtain ⟨u, rfl⟩ : ∃ u, z = L * u := ⟨z / L, by field_simp⟩
  obtain ⟨p, rfl⟩ : ∃ p, h = L * p := ⟨h / L, by field_simp⟩
  obtain ⟨q, rfl⟩ : ∃ q, k = L * q := ⟨k / L, by field_simp⟩
  have hu0 : 0 < u := by
    by_contra hn; push Not at hn; nlinarith
  have hu1 : u ≤ 1 / 1600 := by
    by_contra hn; push Not at hn
    have : L * (1 / 1600) < L * u := mul_lt_mul_of_pos_left hn hL0
    linarith
  -- normalized bounds
  have hLu2 : L * u ^ 2 ≤ 7 / 10 * u ^ 2 := mul_le_mul_of_nonneg_right hL7 (sq_nonneg u)
  have hp_lo : 1 - u / 2 - 49 / 50 * u ^ 2 ≤ p := by
    have h' : L * (1 - p) ≤ L * (u / 2 + 7 / 5 * (L * u ^ 2)) := by
      have e1 : L * (1 - p) = L - L * p := by ring
      have e2 : L * (u / 2 + 7 / 5 * (L * u ^ 2)) = L * u / 2 + 7 / 5 * (L * u) ^ 2 := by ring
      rw [e1, e2]; exact he2
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hp_hi : p ≤ 1 - u / 2 + 53 / 100 * u ^ 2 := by
    have h' : L * (u / 2 - 3 / 4 * (L * u ^ 2)) ≤ L * (1 - p) := by
      have e1 : L * (1 - p) = L - L * p := by ring
      have e2 : L * (u / 2 - 3 / 4 * (L * u ^ 2)) = L * u / 2 - 3 / 4 * (L * u) ^ 2 := by ring
      rw [e1, e2]; exact he1
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hq_lo : 1 + u / 2 ≤ q := by
    have h' : L * (u / 2) ≤ L * (q - 1) := by
      have e1 : L * (q - 1) = L * q - L := by ring
      have e2 : L * (u / 2) = L * u / 2 := by ring
      rw [e1, e2]; exact hm1
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hq_hi : q ≤ 1 + u / 2 + 7 / 10 * u ^ 2 := by
    have h' : L * (q - 1) ≤ L * (u / 2 + L * u ^ 2) := by
      have e1 : L * (q - 1) = L * q - L := by ring
      have e2 : L * (u / 2 + L * u ^ 2) = L * u / 2 + (L * u) ^ 2 := by ring
      rw [e1, e2]; exact hm2
    have := le_of_mul_le_mul_left h' hL0
    linarith
  have hp0 : 0 < p := by nlinarith
  have hq0 : 0 < q := by linarith
  have hz1' : 0 < 1 - L * u := by nlinarith
  -- normalization
  have key : 4 * (L * p) ^ 3 * (2 * (L * q) - L * u) / (L ^ 2 * (1 - L * u) ^ 2 * (L * q) ^ 3) =
      8 / L * (p ^ 3 * (q - u / 2) / ((1 - L * u) ^ 2 * q ^ 3)) := by
    field_simp
    ring
  rw [key]
  -- small powers
  have hpw := pow_succ_le_small hu0.le hu1
  have w1 := hpw 1
  have w2 := hpw 2
  have w3 := hpw 3
  have w4 := hpw 4
  have w5 := hpw 5
  have w6 := hpw 6
  have w7 := hpw 7
  have w8 := hpw 8
  norm_num at w1 w2 w3 w4 w5 w6 w7 w8
  have g2 : 0 ≤ u ^ 2 := by positivity
  have g3 : 0 ≤ u ^ 3 := by positivity
  have g4 : 0 ≤ u ^ 4 := by positivity
  have g5 : 0 ≤ u ^ 5 := by positivity
  have g6 : 0 ≤ u ^ 6 := by positivity
  have g7 : 0 ≤ u ^ 7 := by positivity
  have g8 : 0 ≤ u ^ 8 := by positivity
  have g9 : 0 ≤ u ^ 9 := by positivity
  have hden : 0 < (1 - L * u) ^ 2 * q ^ 3 := by positivity
  have hLlo : (0.6931471803 : ℝ) * u ≤ L * u := mul_le_mul_of_nonneg_right hL1.le hu0.le
  have hLhi : L * u ≤ (0.6931471808 : ℝ) * u := mul_le_mul_of_nonneg_right hL2.le hu0.le
  constructor
  · -- lower bound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ hden]
    have poly : (1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2 *
        (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 ≤ (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 := by
      ring_nf
      ring_nf at w1 w2 w3 w4 w5 w6 w7 w8
      linarith
    have m1 : (1 - 243 / 100 * (L * u)) * (1 - L * u) ^ 2 ≤
        (1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2 := by
      apply mul_le_mul (by linarith) _ (by positivity) (by nlinarith)
      exact pow_le_pow_left₀ hz1'.le (by linarith) 2
    have m2 : q ^ 3 ≤ (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 := pow_le_pow_left₀ hq0.le hq_hi 3
    have m3 : (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by nlinarith) hp_lo 3
    have m4 : p ^ 3 ≤ p ^ 3 * (q - u / 2) := by
      have : 1 ≤ q - u / 2 := by linarith
      nlinarith [pow_pos hp0 3]
    have hA : 0 ≤ 1 - 243 / 100 * (L * u) := by nlinarith
    calc (1 - 243 / 100 * (L * u)) * ((1 - L * u) ^ 2 * q ^ 3)
        = ((1 - 243 / 100 * (L * u)) * (1 - L * u) ^ 2) * q ^ 3 := by ring
      _ ≤ ((1 - 243 / 100 * (0.6931471803 * u)) * (1 - 0.6931471803 * u) ^ 2) *
            (1 + u / 2 + 7 / 10 * u ^ 2) ^ 3 :=
          mul_le_mul m1 m2 (by positivity) (by nlinarith)
      _ ≤ (1 - u / 2 - 49 / 50 * u ^ 2) ^ 3 := poly
      _ ≤ p ^ 3 := m3
      _ ≤ p ^ 3 * (q - u / 2) := m4
  · -- upper bound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hden]
    have poly : (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 * (1 + 7 / 10 * u ^ 2) ≤
        (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 * (1 + u / 2) ^ 3 := by
      ring_nf
      ring_nf at w1 w2 w3 w4 w5 w6 w7 w8
      linarith
    have m1 : (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 ≤
        (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 := by
      apply mul_le_mul (by linarith) _ (by nlinarith) (by nlinarith)
      exact pow_le_pow_left₀ (by nlinarith) (by linarith) 2
    have m2 : (1 + u / 2) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hq_lo 3
    have m3 : p ^ 3 ≤ (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 := pow_le_pow_left₀ hp0.le hp_hi 3
    have m4 : q - u / 2 ≤ 1 + 7 / 10 * u ^ 2 := by linarith
    have hB : 0 ≤ (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 := by
      apply mul_nonneg (by nlinarith) (by positivity)
    calc p ^ 3 * (q - u / 2) ≤ (1 - u / 2 + 53 / 100 * u ^ 2) ^ 3 * (1 + 7 / 10 * u ^ 2) :=
          mul_le_mul m3 m4 (by linarith) (pow_nonneg (by nlinarith [sq_nonneg u]) 3)
      _ ≤ (1 - 178 / 100 * (0.6931471808 * u)) * (1 - 0.6931471808 * u) ^ 2 * (1 + u / 2) ^ 3 := poly
      _ ≤ (1 - 178 / 100 * (L * u)) * (1 - L * u) ^ 2 * q ^ 3 :=
          mul_le_mul m1 m2 (by positivity) hB
      _ = (1 - 178 / 100 * (L * u)) * ((1 - L * u) ^ 2 * q ^ 3) := by ring

/-- **Near-`1/2` bounds for `Psi`.** -/
theorem psi_near {v : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) (hy : 1 - 2 * v ≤ 201 / 10000) :
    8 / Real.log 2 * (1 - 243 / 100 * (1 - 2 * v) ^ 2) ≤ Psi v ∧
      Psi v ≤ 8 / Real.log 2 * (1 - 178 / 100 * (1 - 2 * v) ^ 2) := by
  obtain ⟨he1, he2⟩ := eta_bounds hv0 hv
  obtain ⟨hm1, hm2⟩ := mu_bounds hv0 hv
  rw [psi_eq hv0 hv]
  have hy0 : 0 < 1 - 2 * v := by linarith
  have hz1 : (1 - 2 * v) ^ 2 ≤ 1 / 2400 := by nlinarith
  have hq4 : (1 - 2 * v) ^ 4 / (1 - (1 - 2 * v)) ≤ 16 / 15 * (1 - 2 * v) ^ 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hy0 4]
  have e4 : (1 - 2 * v) ^ 4 = ((1 - 2 * v) ^ 2) ^ 2 := by ring
  have hq5 : (1 - 2 * v) ^ 2 / (2 * (1 - (1 - 2 * v) ^ 2)) ≤
      (1 - 2 * v) ^ 2 / 2 + ((1 - 2 * v) ^ 2) ^ 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith [pow_pos hy0 2]
  have hg4 : 0 ≤ (1 - 2 * v) ^ 4 := by positivity
  refine near_core Real.log_two_gt_d9 Real.log_two_lt_d9 (by positivity) hz1 ?_ ?_ hm1 (hm2.trans hq5)
  · rw [← e4]; linarith
  · rw [← e4]; linarith

#print axioms psi_near

end CKLaneA1.R5
