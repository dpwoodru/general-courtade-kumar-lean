import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0212
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

theorem reflection_log_1_neg : (260258683 / 1000000000) ≤ -Real.log (2560 / 3321) ∧
    -Real.log (2560 / 3321) ≤ (65064671 / 250000000) := by
  have h := checkLog_sound (w := (761 / 5881)) (n := 12)
    (lo := (260258683 / 1000000000)) (hi := (65064671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3321 / 2560) = 1/(2560 / 3321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (260258683 / 1000000000) (65064671 / 250000000) (Real.log (3321 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3321 / 2560) = -Real.log (2560 / 3321) := by
    rw [show ((3321 / 2560) : ℝ) = ((2560 / 3321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352776303 / 1000000000) ≤ -Real.log (1799 / 2560) ∧
    -Real.log (1799 / 2560) ≤ (22048519 / 62500000) := by
  have h := checkLog_sound (w := (761 / 4359)) (n := 12)
    (lo := (352776303 / 1000000000)) (hi := (22048519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1799) = 1/(1799 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22048519 / 62500000) (-352776303 / 1000000000) (Real.log (1799 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25980691 / 100000000) ≤ -Real.log (5120 / 6639) ∧
    -Real.log (5120 / 6639) ≤ (259806911 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 11759)) (n := 12)
    (lo := (25980691 / 100000000)) (hi := (259806911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6639 / 5120) = 1/(5120 / 6639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25980691 / 100000000) (259806911 / 1000000000) (Real.log (6639 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6639 / 5120) = -Real.log (5120 / 6639) := by
    rw [show ((6639 / 5120) : ℝ) = ((5120 / 6639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (175971427 / 500000000) ≤ -Real.log (3601 / 5120) ∧
    -Real.log (3601 / 5120) ≤ (70388571 / 200000000) := by
  have h := checkLog_sound (w := (1519 / 8721)) (n := 12)
    (lo := (175971427 / 500000000)) (hi := (70388571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3601) = 1/(3601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-70388571 / 200000000) (-175971427 / 500000000) (Real.log (3601 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93315961 / 200000000) ≤ -Real.log (1280 / 2041) ∧
    -Real.log (1280 / 2041) ≤ (233289903 / 500000000) := by
  have h := checkLog_sound (w := (761 / 3321)) (n := 12)
    (lo := (93315961 / 200000000)) (hi := (233289903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2041 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2041 / 1280) = 1/(1280 / 2041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93315961 / 200000000) (233289903 / 500000000) (Real.log (2041 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2041 / 1280) = -Real.log (1280 / 2041) := by
    rw [show ((2041 / 1280) : ℝ) = ((1280 / 2041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (902711473 / 1000000000) ≤ -Real.log (519 / 1280) ∧
    -Real.log (519 / 1280) ≤ (36108459 / 40000000) := by
  have h := checkLog_sound (w := (121 / 1159)) (n := 12)
    (lo := (209564293 / 1000000000)) (hi := (104782147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 519) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 519) = 1/(519 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-36108459 / 40000000) (-902711473 / 1000000000) (Real.log (519 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (465844601 / 1000000000) ≤ -Real.log (2560 / 4079) ∧
    -Real.log (2560 / 4079) ≤ (232922301 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 6639)) (n := 12)
    (lo := (465844601 / 1000000000)) (hi := (232922301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4079 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4079 / 2560) = 1/(2560 / 4079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (465844601 / 1000000000) (232922301 / 500000000) (Real.log (4079 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4079 / 2560) = -Real.log (2560 / 4079) := by
    rw [show ((4079 / 2560) : ℝ) = ((2560 / 4079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (224956367 / 250000000) ≤ -Real.log (1041 / 2560) ∧
    -Real.log (1041 / 2560) ≤ (89982547 / 100000000) := by
  have h := checkLog_sound (w := (239 / 2321)) (n := 12)
    (lo := (12917393 / 62500000)) (hi := (206678289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1041) = 1/(1041 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89982547 / 100000000) (-224956367 / 250000000) (Real.log (1041 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88866253 / 250000000) ≤ -Real.log (250000 / 356711) ∧
    -Real.log (250000 / 356711) ≤ (355465013 / 1000000000) := by
  have h := checkLog_sound (w := (106711 / 606711)) (n := 12)
    (lo := (88866253 / 250000000)) (hi := (355465013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356711 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356711 / 250000) = 1/(250000 / 356711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88866253 / 250000000) (355465013 / 1000000000) (Real.log (356711 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (356711 / 250000) = -Real.log (250000 / 356711) := by
    rw [show ((356711 / 250000) : ℝ) = ((250000 / 356711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139149337 / 250000000) ≤ -Real.log (143289 / 250000) ∧
    -Real.log (143289 / 250000) ≤ (556597349 / 1000000000) := by
  have h := checkLog_sound (w := (106711 / 393289)) (n := 12)
    (lo := (139149337 / 250000000)) (hi := (556597349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 143289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 143289) = 1/(143289 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-556597349 / 1000000000) (-139149337 / 250000000) (Real.log (143289 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (356080167 / 1000000000) ≤ -Real.log (500000 / 713861) ∧
    -Real.log (500000 / 713861) ≤ (44510021 / 125000000) := by
  have h := checkLog_sound (w := (213861 / 1213861)) (n := 12)
    (lo := (356080167 / 1000000000)) (hi := (44510021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713861 / 500000) = 1/(500000 / 713861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (356080167 / 1000000000) (44510021 / 125000000) (Real.log (713861 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (713861 / 500000) = -Real.log (500000 / 713861) := by
    rw [show ((713861 / 500000) : ℝ) = ((500000 / 713861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (558130391 / 1000000000) ≤ -Real.log (286139 / 500000) ∧
    -Real.log (286139 / 500000) ≤ (69766299 / 125000000) := by
  have h := checkLog_sound (w := (213861 / 786139)) (n := 12)
    (lo := (558130391 / 1000000000)) (hi := (69766299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 286139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 286139) = 1/(286139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69766299 / 125000000) (-558130391 / 1000000000) (Real.log (286139 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (275981891 / 1000000000) ≤ -Real.log (15625 / 20591) ∧
    -Real.log (15625 / 20591) ≤ (68995473 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 18108)) (n := 12)
    (lo := (275981891 / 1000000000)) (hi := (68995473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20591 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20591 / 15625) = 1/(15625 / 20591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (275981891 / 1000000000) (68995473 / 250000000) (Real.log (20591 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (20591 / 15625) = -Real.log (15625 / 20591) := by
    rw [show ((20591 / 15625) : ℝ) = ((15625 / 20591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (382467589 / 1000000000) ≤ -Real.log (10659 / 15625) ∧
    -Real.log (10659 / 15625) ≤ (38246759 / 100000000) := by
  have h := checkLog_sound (w := (2483 / 13142)) (n := 12)
    (lo := (382467589 / 1000000000)) (hi := (38246759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10659) = 1/(10659 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38246759 / 100000000) (-382467589 / 1000000000) (Real.log (10659 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (69132593 / 250000000) ≤ -Real.log (1000000 / 1318547) ∧
    -Real.log (1000000 / 1318547) ≤ (276530373 / 1000000000) := by
  have h := checkLog_sound (w := (318547 / 2318547)) (n := 12)
    (lo := (69132593 / 250000000)) (hi := (276530373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318547 / 1000000) = 1/(1000000 / 1318547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69132593 / 250000000) (276530373 / 1000000000) (Real.log (1318547 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1318547 / 1000000) = -Real.log (1000000 / 1318547) := by
    rw [show ((1318547 / 1000000) : ℝ) = ((1000000 / 1318547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76705599 / 200000000) ≤ -Real.log (681453 / 1000000) ∧
    -Real.log (681453 / 1000000) ≤ (95881999 / 250000000) := by
  have h := checkLog_sound (w := (318547 / 1681453)) (n := 12)
    (lo := (76705599 / 200000000)) (hi := (95881999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681453) = 1/(681453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-95881999 / 250000000) (-76705599 / 200000000) (Real.log (681453 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (912062359 / 1000000000) ≤ -Real.log (250000000000 / 622362847113) ∧
    -Real.log (250000000000 / 622362847113) ≤ (912062361 / 1000000000) := by
  have h := checkLog_sound (w := (122362847113 / 1122362847113)) (n := 12)
    (lo := (218915179 / 1000000000)) (hi := (10945759 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622362847113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(622362847113 / 500000000000) = 1/(250000000000 / 622362847113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (912062359 / 1000000000) (912062361 / 1000000000) (Real.log (622362847113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (622362847113 / 250000000000) = -Real.log (250000000000 / 622362847113) := by
    rw [show ((622362847113 / 250000000000) : ℝ) = ((250000000000 / 622362847113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (457105279 / 500000000) ≤ -Real.log (100000000000 / 249480497241) ∧
    -Real.log (100000000000 / 249480497241) ≤ (714227 / 781250) := by
  have h := checkLog_sound (w := (49480497241 / 449480497241)) (n := 12)
    (lo := (110531689 / 500000000)) (hi := (221063379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249480497241 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(249480497241 / 200000000000) = 1/(100000000000 / 249480497241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (457105279 / 500000000) (714227 / 781250) (Real.log (249480497241 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (249480497241 / 100000000000) = -Real.log (100000000000 / 249480497241) := by
    rw [show ((249480497241 / 100000000000) : ℝ) = ((100000000000 / 249480497241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (658449481 / 1000000000) ≤ -Real.log (50000000000 / 96589736373) ∧
    -Real.log (50000000000 / 96589736373) ≤ (329224741 / 500000000) := by
  have h := checkLog_sound (w := (46589736373 / 146589736373)) (n := 12)
    (lo := (658449481 / 1000000000)) (hi := (329224741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96589736373 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96589736373 / 50000000000) = 1/(50000000000 / 96589736373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (658449481 / 1000000000) (329224741 / 500000000) (Real.log (96589736373 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96589736373 / 50000000000) = -Real.log (50000000000 / 96589736373) := by
    rw [show ((96589736373 / 50000000000) : ℝ) = ((50000000000 / 96589736373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2578353 / 3906250) ≤ -Real.log (250000000000 / 483726317149) ∧
    -Real.log (250000000000 / 483726317149) ≤ (660058369 / 1000000000) := by
  have h := checkLog_sound (w := (233726317149 / 733726317149)) (n := 12)
    (lo := (2578353 / 3906250)) (hi := (660058369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483726317149 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483726317149 / 250000000000) = 1/(250000000000 / 483726317149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2578353 / 3906250) (660058369 / 1000000000) (Real.log (483726317149 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (483726317149 / 250000000000) = -Real.log (250000000000 / 483726317149) := by
    rw [show ((483726317149 / 250000000000) : ℝ) = ((250000000000 / 483726317149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0212
