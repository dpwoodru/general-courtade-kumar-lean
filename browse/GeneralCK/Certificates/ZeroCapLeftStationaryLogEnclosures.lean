import GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs

/-! Outward-rounded real-log intervals transferred from the exact rational
20-term series witnesses. Pending direct Lean compilation and named audit. -/

namespace GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures
open ZeroCapLeftStationaryAnchorLogs

private theorem neg_log_from_reduced {v s lo hi : ℝ} {k : ℕ}
    (hv : 0 < v) (hs : 0 < s)
    (hscale : (2 : ℝ)^k * s = 1 / v)
    (hlog : lo ≤ Real.log s ∧ Real.log s ≤ hi) :
    (k : ℝ) * (34657359 / 50000000) + lo ≤ -Real.log v ∧
      -Real.log v ≤ (k : ℝ) * (693147181 / 1000000000) + hi := by
  have htwo := PilotData.log_two
  norm_num only [div_one] at htwo
  have he := Mixed.log_scaled s k hs
  rw [hscale, one_div, Real.log_inv] at he
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl := mul_le_mul_of_nonneg_left htwo.1 hk
  have hu := mul_le_mul_of_nonneg_left htwo.2 hk
  constructor <;> linarith only [he, hlog.1, hlog.2, hl, hu]

theorem theta1_A :
    (92912271 / 100000000 : ℝ) ≤ -Real.log (3949 / 10000) ∧
    -Real.log (3949 / 10000 : ℝ) ≤ (116140339 / 125000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (3949 / 10000 : ℝ))
    (s := (5000 / 3949 : ℝ)) (k := 1) (by norm_num) (by norm_num)
    (by norm_num) theta1_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta1_B :
    (100472309 / 200000000 : ℝ) ≤ -Real.log (1 - (3949 / 10000 : ℝ)) ∧
    -Real.log (1 - (3949 / 10000 : ℝ)) ≤ (251180773 / 500000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (3949 / 10000 : ℝ)))
    (s := (10000 / 6051 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta1_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta2_A :
    (286091051 / 200000000 : ℝ) ≤ -Real.log (299 / 1250) ∧
    -Real.log (299 / 1250 : ℝ) ≤ (715227629 / 500000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (299 / 1250 : ℝ))
    (s := (625 / 598 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) theta2_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta2_B :
    (273384767 / 1000000000 : ℝ) ≤ -Real.log (1 - (299 / 1250 : ℝ)) ∧
    -Real.log (1 - (299 / 1250 : ℝ)) ≤ (4271637 / 15625000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (299 / 1250 : ℝ)))
    (s := (1250 / 951 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta2_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta3_A :
    (477635751 / 250000000 : ℝ) ≤ -Real.log (37 / 250) ∧
    -Real.log (37 / 250 : ℝ) ≤ (1910543007 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (37 / 250 : ℝ))
    (s := (125 / 74 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) theta3_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta3_B :
    (10010547 / 62500000 : ℝ) ≤ -Real.log (1 - (37 / 250 : ℝ)) ∧
    -Real.log (1 - (37 / 250 : ℝ)) ≤ (160168753 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (37 / 250 : ℝ)))
    (s := (250 / 213 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta3_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem entropy_Bmax_A :
    (1031968677 / 500000000 : ℝ) ≤ -Real.log (65 / 512) ∧
    -Real.log (65 / 512 : ℝ) ≤ (2063937357 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (65 / 512 : ℝ))
    (s := (128 / 65 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) entropy_Bmax_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem entropy_Bmax_B :
    (13576603 / 100000000 : ℝ) ≤ -Real.log (1 - (65 / 512 : ℝ)) ∧
    -Real.log (1 - (65 / 512 : ℝ)) ≤ (135766031 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (65 / 512 : ℝ)))
    (s := (512 / 447 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) entropy_Bmax_B_reduced
  constructor <;> linarith only [h.1, h.2]

#print axioms theta1_A
#print axioms theta1_B
#print axioms theta2_A
#print axioms theta2_B
#print axioms theta3_A
#print axioms theta3_B
#print axioms entropy_Bmax_A
#print axioms entropy_Bmax_B

end GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures
