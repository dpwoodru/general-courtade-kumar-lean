import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell199
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (31275571 / 100000000) ≤ -Real.log (128 / 175) ∧
    -Real.log (128 / 175) ≤ (312755711 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 303)) (n := 12)
    (lo := (31275571 / 100000000)) (hi := (312755711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175 / 128) = 1/(128 / 175) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31275571 / 100000000) (312755711 / 1000000000) (Real.log (175 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (175 / 128) = -Real.log (128 / 175) := by
    rw [show ((175 / 128) : ℝ) = ((128 / 175) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (457581109 / 1000000000) ≤ -Real.log (81 / 128) ∧
    -Real.log (81 / 128) ≤ (45758111 / 100000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 81) = 1/(81 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45758111 / 100000000) (-457581109 / 1000000000) (Real.log (81 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156163523 / 500000000) ≤ -Real.log (5120 / 6997) ∧
    -Real.log (5120 / 6997) ≤ (312327047 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 12117)) (n := 12)
    (lo := (156163523 / 500000000)) (hi := (312327047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6997 / 5120) = 1/(5120 / 6997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156163523 / 500000000) (312327047 / 1000000000) (Real.log (6997 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6997 / 5120) = -Real.log (5120 / 6997) := by
    rw [show ((6997 / 5120) : ℝ) = ((5120 / 6997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (456655611 / 1000000000) ≤ -Real.log (3243 / 5120) ∧
    -Real.log (3243 / 5120) ≤ (114163903 / 250000000) := by
  have h := checkLog_sound (w := (1877 / 8363)) (n := 12)
    (lo := (456655611 / 1000000000)) (hi := (114163903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3243) = 1/(3243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-114163903 / 250000000) (-456655611 / 1000000000) (Real.log (3243 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (231718679 / 1000000000) ≤ -Real.log (200000 / 252153) ∧
    -Real.log (200000 / 252153) ≤ (5792967 / 25000000) := by
  have h := checkLog_sound (w := (52153 / 452153)) (n := 12)
    (lo := (231718679 / 1000000000)) (hi := (5792967 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252153 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252153 / 200000) = 1/(200000 / 252153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (231718679 / 1000000000) (5792967 / 25000000) (Real.log (252153 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (252153 / 200000) = -Real.log (200000 / 252153) := by
    rw [show ((252153 / 200000) : ℝ) = ((200000 / 252153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302139411 / 1000000000) ≤ -Real.log (147847 / 200000) ∧
    -Real.log (147847 / 200000) ≤ (75534853 / 250000000) := by
  have h := checkLog_sound (w := (52153 / 347847)) (n := 12)
    (lo := (302139411 / 1000000000)) (hi := (75534853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147847) = 1/(147847 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-75534853 / 250000000) (-302139411 / 1000000000) (Real.log (147847 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232054133 / 1000000000) ≤ -Real.log (250000 / 315297) ∧
    -Real.log (250000 / 315297) ≤ (116027067 / 500000000) := by
  have h := checkLog_sound (w := (65297 / 565297)) (n := 12)
    (lo := (232054133 / 1000000000)) (hi := (116027067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315297 / 250000) = 1/(250000 / 315297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232054133 / 1000000000) (116027067 / 500000000) (Real.log (315297 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (315297 / 250000) = -Real.log (250000 / 315297) := by
    rw [show ((315297 / 250000) : ℝ) = ((250000 / 315297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75677947 / 250000000) ≤ -Real.log (184703 / 250000) ∧
    -Real.log (184703 / 250000) ≤ (302711789 / 1000000000) := by
  have h := checkLog_sound (w := (65297 / 434703)) (n := 12)
    (lo := (75677947 / 250000000)) (hi := (302711789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184703) = 1/(184703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-302711789 / 1000000000) (-75677947 / 250000000) (Real.log (184703 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (172210613 / 1000000000) ≤ -Real.log (125000 / 148491) ∧
    -Real.log (125000 / 148491) ≤ (86105307 / 500000000) := by
  have h := checkLog_sound (w := (23491 / 273491)) (n := 12)
    (lo := (172210613 / 1000000000)) (hi := (86105307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148491 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148491 / 125000) = 1/(125000 / 148491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (172210613 / 1000000000) (86105307 / 500000000) (Real.log (148491 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (148491 / 125000) = -Real.log (125000 / 148491) := by
    rw [show ((148491 / 125000) : ℝ) = ((125000 / 148491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1626299 / 7812500) ≤ -Real.log (101509 / 125000) ∧
    -Real.log (101509 / 125000) ≤ (208166273 / 1000000000) := by
  have h := checkLog_sound (w := (23491 / 226509)) (n := 12)
    (lo := (1626299 / 7812500)) (hi := (208166273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101509) = 1/(101509 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-208166273 / 1000000000) (-1626299 / 7812500) (Real.log (101509 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43119357 / 250000000) ≤ -Real.log (200000 / 237649) ∧
    -Real.log (200000 / 237649) ≤ (172477429 / 1000000000) := by
  have h := checkLog_sound (w := (37649 / 437649)) (n := 12)
    (lo := (43119357 / 250000000)) (hi := (172477429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237649 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237649 / 200000) = 1/(200000 / 237649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43119357 / 250000000) (172477429 / 1000000000) (Real.log (237649 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (237649 / 200000) = -Real.log (200000 / 237649) := by
    rw [show ((237649 / 200000) : ℝ) = ((200000 / 237649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (52139177 / 250000000) ≤ -Real.log (162351 / 200000) ∧
    -Real.log (162351 / 200000) ≤ (208556709 / 1000000000) := by
  have h := checkLog_sound (w := (37649 / 362351)) (n := 12)
    (lo := (52139177 / 250000000)) (hi := (208556709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162351) = 1/(162351 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208556709 / 1000000000) (-52139177 / 250000000) (Real.log (162351 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (768982657 / 1000000000) ≤ -Real.log (500000000000 / 1078785075547) ∧
    -Real.log (500000000000 / 1078785075547) ≤ (768982659 / 1000000000) := by
  have h := checkLog_sound (w := (78785075547 / 2078785075547)) (n := 12)
    (lo := (75835477 / 1000000000)) (hi := (37917739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078785075547 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078785075547 / 1000000000000) = 1/(500000000000 / 1078785075547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (768982657 / 1000000000) (768982659 / 1000000000) (Real.log (1078785075547 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1078785075547 / 500000000000) = -Real.log (500000000000 / 1078785075547) := by
    rw [show ((1078785075547 / 500000000000) : ℝ) = ((500000000000 / 1078785075547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (385168409 / 500000000) ≤ -Real.log (500000000000 / 1080246913581) ∧
    -Real.log (500000000000 / 1080246913581) ≤ (38516841 / 50000000) := by
  have h := checkLog_sound (w := (80246913581 / 2080246913581)) (n := 12)
    (lo := (38594819 / 500000000)) (hi := (77189639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080246913581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1080246913581 / 1000000000000) = 1/(500000000000 / 1080246913581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (385168409 / 500000000) (38516841 / 50000000) (Real.log (1080246913581 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1080246913581 / 500000000000) = -Real.log (500000000000 / 1080246913581) := by
    rw [show ((1080246913581 / 500000000000) : ℝ) = ((500000000000 / 1080246913581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (53385809 / 100000000) ≤ -Real.log (6250000000 / 10659372527) ∧
    -Real.log (6250000000 / 10659372527) ≤ (533858091 / 1000000000) := by
  have h := checkLog_sound (w := (4409372527 / 16909372527)) (n := 12)
    (lo := (53385809 / 100000000)) (hi := (533858091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10659372527 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10659372527 / 6250000000) = 1/(6250000000 / 10659372527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53385809 / 100000000) (533858091 / 1000000000) (Real.log (10659372527 / 6250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (10659372527 / 6250000000) = -Real.log (6250000000 / 10659372527) := by
    rw [show ((10659372527 / 6250000000) : ℝ) = ((6250000000 / 10659372527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (267382961 / 500000000) ≤ -Real.log (50000000000 / 85352430659) ∧
    -Real.log (50000000000 / 85352430659) ≤ (534765923 / 1000000000) := by
  have h := checkLog_sound (w := (35352430659 / 135352430659)) (n := 12)
    (lo := (267382961 / 500000000)) (hi := (534765923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85352430659 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85352430659 / 50000000000) = 1/(50000000000 / 85352430659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (267382961 / 500000000) (534765923 / 1000000000) (Real.log (85352430659 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (85352430659 / 50000000000) = -Real.log (50000000000 / 85352430659) := by
    rw [show ((85352430659 / 50000000000) : ℝ) = ((50000000000 / 85352430659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (76075377 / 200000000) ≤ -Real.log (500000000000 / 731417903831) ∧
    -Real.log (500000000000 / 731417903831) ≤ (190188443 / 500000000) := by
  have h := checkLog_sound (w := (231417903831 / 1231417903831)) (n := 12)
    (lo := (76075377 / 200000000)) (hi := (190188443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731417903831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731417903831 / 500000000000) = 1/(500000000000 / 731417903831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (76075377 / 200000000) (190188443 / 500000000) (Real.log (731417903831 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (731417903831 / 500000000000) = -Real.log (500000000000 / 731417903831) := by
    rw [show ((731417903831 / 500000000000) : ℝ) = ((500000000000 / 731417903831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381034137 / 1000000000) ≤ -Real.log (125000000000 / 182974696799) ∧
    -Real.log (125000000000 / 182974696799) ≤ (190517069 / 500000000) := by
  have h := checkLog_sound (w := (57974696799 / 307974696799)) (n := 12)
    (lo := (381034137 / 1000000000)) (hi := (190517069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182974696799 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182974696799 / 125000000000) = 1/(125000000000 / 182974696799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381034137 / 1000000000) (190517069 / 500000000) (Real.log (182974696799 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (182974696799 / 125000000000) = -Real.log (125000000000 / 182974696799) := by
    rw [show ((182974696799 / 125000000000) : ℝ) = ((125000000000 / 182974696799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36079279 / 1000000000) ≤ -Real.log (38582552799 / 40000000000) ∧
    -Real.log (38582552799 / 40000000000) ≤ (450991 / 12500000) := by
  have h := checkLog_sound (w := (1417447201 / 78582552799)) (n := 12)
    (lo := (36079279 / 1000000000)) (hi := (450991 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38582552799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38582552799) = 1/(38582552799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-450991 / 12500000) (-36079279 / 1000000000) (Real.log (38582552799 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (35955659 / 1000000000) ≤ -Real.log (15073172919 / 15625000000) ∧
    -Real.log (15073172919 / 15625000000) ≤ (1797783 / 50000000) := by
  have h := checkLog_sound (w := (551827081 / 30698172919)) (n := 12)
    (lo := (35955659 / 1000000000)) (hi := (1797783 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15073172919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15073172919) = 1/(15073172919 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1797783 / 50000000) (-35955659 / 1000000000) (Real.log (15073172919 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell199
