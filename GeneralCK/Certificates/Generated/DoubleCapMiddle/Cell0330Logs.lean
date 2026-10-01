import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0330
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (108436969 / 500000000) ≤ -Real.log (128 / 159) ∧
    -Real.log (128 / 159) ≤ (216873939 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 287)) (n := 12)
    (lo := (108436969 / 500000000)) (hi := (216873939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 128) = 1/(128 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (108436969 / 500000000) (216873939 / 1000000000) (Real.log (159 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (159 / 128) = -Real.log (128 / 159) := by
    rw [show ((159 / 128) : ℝ) = ((128 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55463857 / 200000000) ≤ -Real.log (97 / 128) ∧
    -Real.log (97 / 128) ≤ (138659643 / 500000000) := by
  have h := checkLog_sound (w := (31 / 225)) (n := 12)
    (lo := (55463857 / 200000000)) (hi := (138659643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 97) = 1/(97 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-138659643 / 500000000) (-55463857 / 200000000) (Real.log (97 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (216638061 / 1000000000) ≤ -Real.log (10240 / 12717) ∧
    -Real.log (10240 / 12717) ≤ (108319031 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 22957)) (n := 12)
    (lo := (216638061 / 1000000000)) (hi := (108319031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12717 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12717 / 10240) = 1/(10240 / 12717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (216638061 / 1000000000) (108319031 / 500000000) (Real.log (12717 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12717 / 10240) = -Real.log (10240 / 12717) := by
    rw [show ((12717 / 10240) : ℝ) = ((10240 / 12717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138466381 / 500000000) ≤ -Real.log (7763 / 10240) ∧
    -Real.log (7763 / 10240) ≤ (276932763 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 18003)) (n := 12)
    (lo := (138466381 / 500000000)) (hi := (276932763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7763) = 1/(7763 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276932763 / 1000000000) (-138466381 / 500000000) (Real.log (7763 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24687113 / 62500000) ≤ -Real.log (64 / 95) ∧
    -Real.log (64 / 95) ≤ (394993809 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 159)) (n := 12)
    (lo := (24687113 / 62500000)) (hi := (394993809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95 / 64) = 1/(64 / 95) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24687113 / 62500000) (394993809 / 1000000000) (Real.log (95 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (95 / 64) = -Real.log (64 / 95) := by
    rw [show ((95 / 64) : ℝ) = ((64 / 95) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (662375521 / 1000000000) ≤ -Real.log (33 / 64) ∧
    -Real.log (33 / 64) ≤ (331187761 / 500000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 33) = 1/(33 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-331187761 / 500000000) (-662375521 / 1000000000) (Real.log (33 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (394598993 / 1000000000) ≤ -Real.log (5120 / 7597) ∧
    -Real.log (5120 / 7597) ≤ (197299497 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 12717)) (n := 12)
    (lo := (394598993 / 1000000000)) (hi := (197299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7597 / 5120) = 1/(5120 / 7597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (394598993 / 1000000000) (197299497 / 500000000) (Real.log (7597 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7597 / 5120) = -Real.log (5120 / 7597) := by
    rw [show ((7597 / 5120) : ℝ) = ((5120 / 7597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (661239803 / 1000000000) ≤ -Real.log (2643 / 5120) ∧
    -Real.log (2643 / 5120) ≤ (165309951 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 7763)) (n := 12)
    (lo := (661239803 / 1000000000)) (hi := (165309951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2643) = 1/(2643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165309951 / 250000000) (-661239803 / 1000000000) (Real.log (2643 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148493201 / 500000000) ≤ -Real.log (1000000 / 1345797) ∧
    -Real.log (1000000 / 1345797) ≤ (296986403 / 1000000000) := by
  have h := checkLog_sound (w := (345797 / 2345797)) (n := 12)
    (lo := (148493201 / 500000000)) (hi := (296986403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345797 / 1000000) = 1/(1000000 / 1345797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148493201 / 500000000) (296986403 / 1000000000) (Real.log (1345797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1345797 / 1000000) = -Real.log (1000000 / 1345797) := by
    rw [show ((1345797 / 1000000) : ℝ) = ((1000000 / 1345797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212168789 / 500000000) ≤ -Real.log (654203 / 1000000) ∧
    -Real.log (654203 / 1000000) ≤ (424337579 / 1000000000) := by
  have h := checkLog_sound (w := (345797 / 1654203)) (n := 12)
    (lo := (212168789 / 500000000)) (hi := (424337579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654203) = 1/(654203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-424337579 / 1000000000) (-212168789 / 500000000) (Real.log (654203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37163233 / 125000000) ≤ -Real.log (1000000 / 1346227) ∧
    -Real.log (1000000 / 1346227) ≤ (59461173 / 200000000) := by
  have h := checkLog_sound (w := (346227 / 2346227)) (n := 12)
    (lo := (37163233 / 125000000)) (hi := (59461173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1346227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1346227 / 1000000) = 1/(1000000 / 1346227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37163233 / 125000000) (59461173 / 200000000) (Real.log (1346227 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1346227 / 1000000) = -Real.log (1000000 / 1346227) := by
    rw [show ((1346227 / 1000000) : ℝ) = ((1000000 / 1346227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (212497541 / 500000000) ≤ -Real.log (653773 / 1000000) ∧
    -Real.log (653773 / 1000000) ≤ (424995083 / 1000000000) := by
  have h := checkLog_sound (w := (346227 / 1653773)) (n := 12)
    (lo := (212497541 / 500000000)) (hi := (424995083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 653773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 653773) = 1/(653773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-424995083 / 1000000000) (-212497541 / 500000000) (Real.log (653773 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45089459 / 200000000) ≤ -Real.log (1000000 / 1252883) ∧
    -Real.log (1000000 / 1252883) ≤ (1761307 / 7812500) := by
  have h := checkLog_sound (w := (252883 / 2252883)) (n := 12)
    (lo := (45089459 / 200000000)) (hi := (1761307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252883 / 1000000) = 1/(1000000 / 1252883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45089459 / 200000000) (1761307 / 7812500) (Real.log (1252883 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1252883 / 1000000) = -Real.log (1000000 / 1252883) := by
    rw [show ((1252883 / 1000000) : ℝ) = ((1000000 / 1252883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291533479 / 1000000000) ≤ -Real.log (747117 / 1000000) ∧
    -Real.log (747117 / 1000000) ≤ (7288337 / 25000000) := by
  have h := checkLog_sound (w := (252883 / 1747117)) (n := 12)
    (lo := (291533479 / 1000000000)) (hi := (7288337 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747117) = 1/(747117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7288337 / 25000000) (-291533479 / 1000000000) (Real.log (747117 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225715441 / 1000000000) ≤ -Real.log (1000000 / 1253219) ∧
    -Real.log (1000000 / 1253219) ≤ (112857721 / 500000000) := by
  have h := checkLog_sound (w := (253219 / 2253219)) (n := 12)
    (lo := (225715441 / 1000000000)) (hi := (112857721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253219 / 1000000) = 1/(1000000 / 1253219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225715441 / 1000000000) (112857721 / 500000000) (Real.log (1253219 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1253219 / 1000000) = -Real.log (1000000 / 1253219) := by
    rw [show ((1253219 / 1000000) : ℝ) = ((1000000 / 1253219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291983309 / 1000000000) ≤ -Real.log (746781 / 1000000) ∧
    -Real.log (746781 / 1000000) ≤ (29198331 / 100000000) := by
  have h := checkLog_sound (w := (253219 / 1746781)) (n := 12)
    (lo := (291983309 / 1000000000)) (hi := (29198331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746781) = 1/(746781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-29198331 / 100000000) (-291983309 / 1000000000) (Real.log (746781 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36066199 / 50000000) ≤ -Real.log (125000000000 / 257144380261) ∧
    -Real.log (125000000000 / 257144380261) ≤ (360661991 / 500000000) := by
  have h := checkLog_sound (w := (7144380261 / 507144380261)) (n := 12)
    (lo := (35221 / 1250000)) (hi := (28176801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257144380261 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(257144380261 / 250000000000) = 1/(125000000000 / 257144380261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36066199 / 50000000) (360661991 / 500000000) (Real.log (257144380261 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (257144380261 / 125000000000) = -Real.log (125000000000 / 257144380261) := by
    rw [show ((257144380261 / 125000000000) : ℝ) = ((125000000000 / 257144380261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (361150473 / 500000000) ≤ -Real.log (12500000000 / 25739572451) ∧
    -Real.log (12500000000 / 25739572451) ≤ (180575237 / 250000000) := by
  have h := checkLog_sound (w := (739572451 / 50739572451)) (n := 12)
    (lo := (14576883 / 500000000)) (hi := (29153767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25739572451 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25739572451 / 25000000000) = 1/(12500000000 / 25739572451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (361150473 / 500000000) (180575237 / 250000000) (Real.log (25739572451 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25739572451 / 12500000000) = -Real.log (12500000000 / 25739572451) := by
    rw [show ((25739572451 / 12500000000) : ℝ) = ((12500000000 / 25739572451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20679231 / 40000000) ≤ -Real.log (500000000000 / 838478444473) ∧
    -Real.log (500000000000 / 838478444473) ≤ (64622597 / 125000000) := by
  have h := checkLog_sound (w := (338478444473 / 1338478444473)) (n := 12)
    (lo := (20679231 / 40000000)) (hi := (64622597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838478444473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838478444473 / 500000000000) = 1/(500000000000 / 838478444473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (20679231 / 40000000) (64622597 / 125000000) (Real.log (838478444473 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (838478444473 / 500000000000) = -Real.log (500000000000 / 838478444473) := by
    rw [show ((838478444473 / 500000000000) : ℝ) = ((500000000000 / 838478444473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (414159 / 800000) ≤ -Real.log (500000000000 / 839080667559) ∧
    -Real.log (500000000000 / 839080667559) ≤ (517698751 / 1000000000) := by
  have h := checkLog_sound (w := (339080667559 / 1339080667559)) (n := 12)
    (lo := (414159 / 800000)) (hi := (517698751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839080667559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839080667559 / 500000000000) = 1/(500000000000 / 839080667559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (414159 / 800000) (517698751 / 1000000000) (Real.log (839080667559 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (839080667559 / 500000000000) = -Real.log (500000000000 / 839080667559) := by
    rw [show ((839080667559 / 500000000000) : ℝ) = ((500000000000 / 839080667559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0330
