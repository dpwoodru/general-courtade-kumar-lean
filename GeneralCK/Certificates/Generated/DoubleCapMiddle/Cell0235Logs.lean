import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0235
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

theorem reflection_log_1_neg : (24981591 / 100000000) ≤ -Real.log (5120 / 6573) ∧
    -Real.log (5120 / 6573) ≤ (249815911 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 11693)) (n := 12)
    (lo := (24981591 / 100000000)) (hi := (249815911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5120) = 1/(5120 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24981591 / 100000000) (249815911 / 1000000000) (Real.log (6573 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6573 / 5120) = -Real.log (5120 / 6573) := by
    rw [show ((6573 / 5120) : ℝ) = ((5120 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333780549 / 1000000000) ≤ -Real.log (3667 / 5120) ∧
    -Real.log (3667 / 5120) ≤ (6675611 / 20000000) := by
  have h := checkLog_sound (w := (1453 / 8787)) (n := 12)
    (lo := (333780549 / 1000000000)) (hi := (6675611 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3667) = 1/(3667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6675611 / 20000000) (-333780549 / 1000000000) (Real.log (3667 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (249359393 / 1000000000) ≤ -Real.log (512 / 657) ∧
    -Real.log (512 / 657) ≤ (124679697 / 500000000) := by
  have h := checkLog_sound (w := (145 / 1169)) (n := 12)
    (lo := (249359393 / 1000000000)) (hi := (124679697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 512) = 1/(512 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (249359393 / 1000000000) (124679697 / 500000000) (Real.log (657 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (657 / 512) = -Real.log (512 / 657) := by
    rw [show ((657 / 512) : ℝ) = ((512 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41620347 / 125000000) ≤ -Real.log (367 / 512) ∧
    -Real.log (367 / 512) ≤ (332962777 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 879)) (n := 12)
    (lo := (41620347 / 125000000)) (hi := (332962777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 367) = 1/(367 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332962777 / 1000000000) (-41620347 / 125000000) (Real.log (367 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (56191479 / 125000000) ≤ -Real.log (2560 / 4013) ∧
    -Real.log (2560 / 4013) ≤ (449531833 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 6573)) (n := 12)
    (lo := (56191479 / 125000000)) (hi := (449531833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4013 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4013 / 2560) = 1/(2560 / 4013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (56191479 / 125000000) (449531833 / 1000000000) (Real.log (4013 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4013 / 2560) = -Real.log (2560 / 4013) := by
    rw [show ((4013 / 2560) : ℝ) = ((2560 / 4013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209588401 / 250000000) ≤ -Real.log (1107 / 2560) ∧
    -Real.log (1107 / 2560) ≤ (419176803 / 500000000) := by
  have h := checkLog_sound (w := (173 / 2387)) (n := 12)
    (lo := (18150803 / 125000000)) (hi := (5808257 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1107) = 1/(1107 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-419176803 / 500000000) (-209588401 / 250000000) (Real.log (1107 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224391991 / 500000000) ≤ -Real.log (256 / 401) ∧
    -Real.log (256 / 401) ≤ (448783983 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 657)) (n := 12)
    (lo := (224391991 / 500000000)) (hi := (448783983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401 / 256) = 1/(256 / 401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224391991 / 500000000) (448783983 / 1000000000) (Real.log (401 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (401 / 256) = -Real.log (256 / 401) := by
    rw [show ((401 / 256) : ℝ) = ((256 / 401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (417823621 / 500000000) ≤ -Real.log (111 / 256) ∧
    -Real.log (111 / 256) ≤ (208911811 / 250000000) := by
  have h := checkLog_sound (w := (17 / 239)) (n := 12)
    (lo := (71250031 / 500000000)) (hi := (142500063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 111) = 1/(111 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208911811 / 250000000) (-417823621 / 500000000) (Real.log (111 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85317143 / 250000000) ≤ -Real.log (1000000 / 1406731) ∧
    -Real.log (1000000 / 1406731) ≤ (341268573 / 1000000000) := by
  have h := checkLog_sound (w := (406731 / 2406731)) (n := 12)
    (lo := (85317143 / 250000000)) (hi := (341268573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1406731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1406731 / 1000000) = 1/(1000000 / 1406731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85317143 / 250000000) (341268573 / 1000000000) (Real.log (1406731 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1406731 / 1000000) = -Real.log (1000000 / 1406731) := by
    rw [show ((1406731 / 1000000) : ℝ) = ((1000000 / 1406731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (522107357 / 1000000000) ≤ -Real.log (593269 / 1000000) ∧
    -Real.log (593269 / 1000000) ≤ (261053679 / 500000000) := by
  have h := checkLog_sound (w := (406731 / 1593269)) (n := 12)
    (lo := (522107357 / 1000000000)) (hi := (261053679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 593269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 593269) = 1/(593269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-261053679 / 500000000) (-522107357 / 1000000000) (Real.log (593269 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42736121 / 125000000) ≤ -Real.log (250000 / 351901) ∧
    -Real.log (250000 / 351901) ≤ (341888969 / 1000000000) := by
  have h := checkLog_sound (w := (101901 / 601901)) (n := 12)
    (lo := (42736121 / 125000000)) (hi := (341888969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351901 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351901 / 250000) = 1/(250000 / 351901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42736121 / 125000000) (341888969 / 1000000000) (Real.log (351901 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (351901 / 250000) = -Real.log (250000 / 351901) := by
    rw [show ((351901 / 250000) : ℝ) = ((250000 / 351901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (130894987 / 250000000) ≤ -Real.log (148099 / 250000) ∧
    -Real.log (148099 / 250000) ≤ (523579949 / 1000000000) := by
  have h := checkLog_sound (w := (101901 / 398099)) (n := 12)
    (lo := (130894987 / 250000000)) (hi := (523579949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148099) = 1/(148099 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-523579949 / 1000000000) (-130894987 / 250000000) (Real.log (148099 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263428313 / 1000000000) ≤ -Real.log (125000 / 162673) ∧
    -Real.log (125000 / 162673) ≤ (131714157 / 500000000) := by
  have h := checkLog_sound (w := (37673 / 287673)) (n := 12)
    (lo := (263428313 / 1000000000)) (hi := (131714157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162673 / 125000) = 1/(125000 / 162673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263428313 / 1000000000) (131714157 / 500000000) (Real.log (162673 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (162673 / 125000) = -Real.log (125000 / 162673) := by
    rw [show ((162673 / 125000) : ℝ) = ((125000 / 162673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (358654043 / 1000000000) ≤ -Real.log (87327 / 125000) ∧
    -Real.log (87327 / 125000) ≤ (89663511 / 250000000) := by
  have h := checkLog_sound (w := (37673 / 212327)) (n := 12)
    (lo := (358654043 / 1000000000)) (hi := (89663511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87327) = 1/(87327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89663511 / 250000000) (-358654043 / 1000000000) (Real.log (87327 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (263972969 / 1000000000) ≤ -Real.log (1000000 / 1302093) ∧
    -Real.log (1000000 / 1302093) ≤ (26397297 / 100000000) := by
  have h := checkLog_sound (w := (302093 / 2302093)) (n := 12)
    (lo := (263972969 / 1000000000)) (hi := (26397297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302093 / 1000000) = 1/(1000000 / 1302093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (263972969 / 1000000000) (26397297 / 100000000) (Real.log (1302093 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1302093 / 1000000) = -Real.log (1000000 / 1302093) := by
    rw [show ((1302093 / 1000000) : ℝ) = ((1000000 / 1302093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (179834711 / 500000000) ≤ -Real.log (697907 / 1000000) ∧
    -Real.log (697907 / 1000000) ≤ (359669423 / 1000000000) := by
  have h := checkLog_sound (w := (302093 / 1697907)) (n := 12)
    (lo := (179834711 / 500000000)) (hi := (359669423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697907) = 1/(697907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-359669423 / 1000000000) (-179834711 / 500000000) (Real.log (697907 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (863375929 / 1000000000) ≤ -Real.log (500000000000 / 1185576020321) ∧
    -Real.log (500000000000 / 1185576020321) ≤ (863375931 / 1000000000) := by
  have h := checkLog_sound (w := (185576020321 / 2185576020321)) (n := 12)
    (lo := (170228749 / 1000000000)) (hi := (136183 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185576020321 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1185576020321 / 1000000000000) = 1/(500000000000 / 1185576020321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (863375929 / 1000000000) (863375931 / 1000000000) (Real.log (1185576020321 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1185576020321 / 500000000000) = -Real.log (500000000000 / 1185576020321) := by
    rw [show ((1185576020321 / 500000000000) : ℝ) = ((500000000000 / 1185576020321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (216367229 / 250000000) ≤ -Real.log (50000000000 / 118806001391) ∧
    -Real.log (50000000000 / 118806001391) ≤ (432734459 / 500000000) := by
  have h := checkLog_sound (w := (18806001391 / 218806001391)) (n := 12)
    (lo := (21540217 / 125000000)) (hi := (172321737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118806001391 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118806001391 / 100000000000) = 1/(50000000000 / 118806001391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (216367229 / 250000000) (432734459 / 500000000) (Real.log (118806001391 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118806001391 / 50000000000) = -Real.log (50000000000 / 118806001391) := by
    rw [show ((118806001391 / 50000000000) : ℝ) = ((50000000000 / 118806001391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (622082357 / 1000000000) ≤ -Real.log (10000000000 / 18628030277) ∧
    -Real.log (10000000000 / 18628030277) ≤ (311041179 / 500000000) := by
  have h := checkLog_sound (w := (8628030277 / 28628030277)) (n := 12)
    (lo := (622082357 / 1000000000)) (hi := (311041179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18628030277 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18628030277 / 10000000000) = 1/(10000000000 / 18628030277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (622082357 / 1000000000) (311041179 / 500000000) (Real.log (18628030277 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18628030277 / 10000000000) = -Real.log (10000000000 / 18628030277) := by
    rw [show ((18628030277 / 10000000000) : ℝ) = ((10000000000 / 18628030277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (77955299 / 125000000) ≤ -Real.log (62500000000 / 116606958377) ∧
    -Real.log (62500000000 / 116606958377) ≤ (623642393 / 1000000000) := by
  have h := checkLog_sound (w := (54106958377 / 179106958377)) (n := 12)
    (lo := (77955299 / 125000000)) (hi := (623642393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116606958377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116606958377 / 62500000000) = 1/(62500000000 / 116606958377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (77955299 / 125000000) (623642393 / 1000000000) (Real.log (116606958377 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (116606958377 / 62500000000) = -Real.log (62500000000 / 116606958377) := by
    rw [show ((116606958377 / 62500000000) : ℝ) = ((62500000000 / 116606958377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0235
