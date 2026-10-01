import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0351
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

theorem reflection_log_1_neg : (105954401 / 500000000) ≤ -Real.log (10240 / 12657) ∧
    -Real.log (10240 / 12657) ≤ (211908803 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 22897)) (n := 12)
    (lo := (105954401 / 500000000)) (hi := (211908803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10240) = 1/(10240 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (105954401 / 500000000) (211908803 / 1000000000) (Real.log (12657 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12657 / 10240) = -Real.log (10240 / 12657) := by
    rw [show ((12657 / 10240) : ℝ) = ((10240 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (134616753 / 500000000) ≤ -Real.log (7823 / 10240) ∧
    -Real.log (7823 / 10240) ≤ (269233507 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 18063)) (n := 12)
    (lo := (134616753 / 500000000)) (hi := (269233507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7823) = 1/(7823 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-269233507 / 1000000000) (-134616753 / 500000000) (Real.log (7823 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (211671751 / 1000000000) ≤ -Real.log (5120 / 6327) ∧
    -Real.log (5120 / 6327) ≤ (26458969 / 125000000) := by
  have h := checkLog_sound (w := (1207 / 11447)) (n := 12)
    (lo := (211671751 / 1000000000)) (hi := (26458969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6327 / 5120) = 1/(5120 / 6327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (211671751 / 1000000000) (26458969 / 125000000) (Real.log (6327 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6327 / 5120) = -Real.log (5120 / 6327) := by
    rw [show ((6327 / 5120) : ℝ) = ((5120 / 6327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53770019 / 200000000) ≤ -Real.log (3913 / 5120) ∧
    -Real.log (3913 / 5120) ≤ (16803131 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 9033)) (n := 12)
    (lo := (53770019 / 200000000)) (hi := (16803131 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3913) = 1/(3913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16803131 / 62500000) (-53770019 / 200000000) (Real.log (3913 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77333957 / 200000000) ≤ -Real.log (5120 / 7537) ∧
    -Real.log (5120 / 7537) ≤ (193334893 / 500000000) := by
  have h := checkLog_sound (w := (2417 / 12657)) (n := 12)
    (lo := (77333957 / 200000000)) (hi := (193334893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7537 / 5120) = 1/(5120 / 7537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77333957 / 200000000) (193334893 / 500000000) (Real.log (7537 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7537 / 5120) = -Real.log (5120 / 7537) := by
    rw [show ((7537 / 5120) : ℝ) = ((5120 / 7537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638792171 / 1000000000) ≤ -Real.log (2703 / 5120) ∧
    -Real.log (2703 / 5120) ≤ (159698043 / 250000000) := by
  have h := checkLog_sound (w := (2417 / 7823)) (n := 12)
    (lo := (638792171 / 1000000000)) (hi := (159698043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2703) = 1/(2703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159698043 / 250000000) (-638792171 / 1000000000) (Real.log (2703 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (38627167 / 100000000) ≤ -Real.log (2560 / 3767) ∧
    -Real.log (2560 / 3767) ≤ (386271671 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 6327)) (n := 12)
    (lo := (38627167 / 100000000)) (hi := (386271671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3767 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3767 / 2560) = 1/(2560 / 3767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (38627167 / 100000000) (386271671 / 1000000000) (Real.log (3767 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3767 / 2560) = -Real.log (2560 / 3767) := by
    rw [show ((3767 / 2560) : ℝ) = ((2560 / 3767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (637682909 / 1000000000) ≤ -Real.log (1353 / 2560) ∧
    -Real.log (1353 / 2560) ≤ (63768291 / 100000000) := by
  have h := checkLog_sound (w := (1207 / 3913)) (n := 12)
    (lo := (637682909 / 1000000000)) (hi := (63768291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1353) = 1/(1353 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63768291 / 100000000) (-637682909 / 1000000000) (Real.log (1353 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145139723 / 500000000) ≤ -Real.log (1000000 / 1336801) ∧
    -Real.log (1000000 / 1336801) ≤ (290279447 / 1000000000) := by
  have h := checkLog_sound (w := (336801 / 2336801)) (n := 12)
    (lo := (145139723 / 500000000)) (hi := (290279447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336801 / 1000000) = 1/(1000000 / 1336801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145139723 / 500000000) (290279447 / 1000000000) (Real.log (1336801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1336801 / 1000000) = -Real.log (1000000 / 1336801) := by
    rw [show ((1336801 / 1000000) : ℝ) = ((1000000 / 1336801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (410680183 / 1000000000) ≤ -Real.log (663199 / 1000000) ∧
    -Real.log (663199 / 1000000) ≤ (51335023 / 125000000) := by
  have h := checkLog_sound (w := (336801 / 1663199)) (n := 12)
    (lo := (410680183 / 1000000000)) (hi := (51335023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663199) = 1/(663199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-51335023 / 125000000) (-410680183 / 1000000000) (Real.log (663199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29060031 / 100000000) ≤ -Real.log (100000 / 133723) ∧
    -Real.log (100000 / 133723) ≤ (290600311 / 1000000000) := by
  have h := checkLog_sound (w := (33723 / 233723)) (n := 12)
    (lo := (29060031 / 100000000)) (hi := (290600311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133723 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133723 / 100000) = 1/(100000 / 133723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29060031 / 100000000) (290600311 / 1000000000) (Real.log (133723 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (133723 / 100000) = -Real.log (100000 / 133723) := by
    rw [show ((133723 / 100000) : ℝ) = ((100000 / 133723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (51415907 / 125000000) ≤ -Real.log (66277 / 100000) ∧
    -Real.log (66277 / 100000) ≤ (411327257 / 1000000000) := by
  have h := checkLog_sound (w := (33723 / 166277)) (n := 12)
    (lo := (51415907 / 125000000)) (hi := (411327257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66277) = 1/(66277 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-411327257 / 1000000000) (-51415907 / 125000000) (Real.log (66277 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (219836489 / 1000000000) ≤ -Real.log (1000000 / 1245873) ∧
    -Real.log (1000000 / 1245873) ≤ (21983649 / 100000000) := by
  have h := checkLog_sound (w := (245873 / 2245873)) (n := 12)
    (lo := (219836489 / 1000000000)) (hi := (21983649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245873 / 1000000) = 1/(1000000 / 1245873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (219836489 / 1000000000) (21983649 / 100000000) (Real.log (1245873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1245873 / 1000000) = -Real.log (1000000 / 1245873) := by
    rw [show ((1245873 / 1000000) : ℝ) = ((1000000 / 1245873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28219449 / 100000000) ≤ -Real.log (754127 / 1000000) ∧
    -Real.log (754127 / 1000000) ≤ (282194491 / 1000000000) := by
  have h := checkLog_sound (w := (245873 / 1754127)) (n := 12)
    (lo := (28219449 / 100000000)) (hi := (282194491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754127) = 1/(754127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-282194491 / 1000000000) (-28219449 / 100000000) (Real.log (754127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (110052269 / 500000000) ≤ -Real.log (1000000 / 1246207) ∧
    -Real.log (1000000 / 1246207) ≤ (220104539 / 1000000000) := by
  have h := checkLog_sound (w := (246207 / 2246207)) (n := 12)
    (lo := (110052269 / 500000000)) (hi := (220104539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246207 / 1000000) = 1/(1000000 / 1246207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (110052269 / 500000000) (220104539 / 1000000000) (Real.log (1246207 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1246207 / 1000000) = -Real.log (1000000 / 1246207) := by
    rw [show ((1246207 / 1000000) : ℝ) = ((1000000 / 1246207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (70659371 / 250000000) ≤ -Real.log (753793 / 1000000) ∧
    -Real.log (753793 / 1000000) ≤ (56527497 / 200000000) := by
  have h := checkLog_sound (w := (246207 / 1753793)) (n := 12)
    (lo := (70659371 / 250000000)) (hi := (56527497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753793) = 1/(753793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-56527497 / 200000000) (-70659371 / 250000000) (Real.log (753793 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (175239907 / 250000000) ≤ -Real.log (500000000000 / 1007843045601) ∧
    -Real.log (500000000000 / 1007843045601) ≤ (70095963 / 100000000) := by
  have h := checkLog_sound (w := (7843045601 / 2007843045601)) (n := 12)
    (lo := (244139 / 31250000)) (hi := (7812449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007843045601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1007843045601 / 1000000000000) = 1/(500000000000 / 1007843045601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (175239907 / 250000000) (70095963 / 100000000) (Real.log (1007843045601 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1007843045601 / 500000000000) = -Real.log (500000000000 / 1007843045601) := by
    rw [show ((1007843045601 / 500000000000) : ℝ) = ((500000000000 / 1007843045601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (350963783 / 500000000) ≤ -Real.log (125000000000 / 252204761833) ∧
    -Real.log (125000000000 / 252204761833) ≤ (43870473 / 62500000) := by
  have h := checkLog_sound (w := (2204761833 / 502204761833)) (n := 12)
    (lo := (4390193 / 500000000)) (hi := (8780387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252204761833 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252204761833 / 250000000000) = 1/(125000000000 / 252204761833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (350963783 / 500000000) (43870473 / 62500000) (Real.log (252204761833 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (252204761833 / 125000000000) = -Real.log (125000000000 / 252204761833) := by
    rw [show ((252204761833 / 125000000000) : ℝ) = ((125000000000 / 252204761833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (502030979 / 1000000000) ≤ -Real.log (500000000000 / 826036595957) ∧
    -Real.log (500000000000 / 826036595957) ≤ (25101549 / 50000000) := by
  have h := checkLog_sound (w := (326036595957 / 1326036595957)) (n := 12)
    (lo := (502030979 / 1000000000)) (hi := (25101549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826036595957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826036595957 / 500000000000) = 1/(500000000000 / 826036595957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (502030979 / 1000000000) (25101549 / 50000000) (Real.log (826036595957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (826036595957 / 500000000000) = -Real.log (500000000000 / 826036595957) := by
    rw [show ((826036595957 / 500000000000) : ℝ) = ((500000000000 / 826036595957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (251371011 / 500000000) ≤ -Real.log (100000000000 / 165324830557) ∧
    -Real.log (100000000000 / 165324830557) ≤ (502742023 / 1000000000) := by
  have h := checkLog_sound (w := (65324830557 / 265324830557)) (n := 12)
    (lo := (251371011 / 500000000)) (hi := (502742023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165324830557 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165324830557 / 100000000000) = 1/(100000000000 / 165324830557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (251371011 / 500000000) (502742023 / 1000000000) (Real.log (165324830557 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (165324830557 / 100000000000) = -Real.log (100000000000 / 165324830557) := by
    rw [show ((165324830557 / 100000000000) : ℝ) = ((100000000000 / 165324830557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0351
