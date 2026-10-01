import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0314
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

theorem reflection_log_1_neg : (220640421 / 1000000000) ≤ -Real.log (320 / 399) ∧
    -Real.log (320 / 399) ≤ (110320211 / 500000000) := by
  have h := checkLog_sound (w := (79 / 719)) (n := 12)
    (lo := (220640421 / 1000000000)) (hi := (110320211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 320) = 1/(320 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (220640421 / 1000000000) (110320211 / 500000000) (Real.log (399 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (399 / 320) = -Real.log (320 / 399) := by
    rw [show ((399 / 320) : ℝ) = ((320 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141762031 / 500000000) ≤ -Real.log (241 / 320) ∧
    -Real.log (241 / 320) ≤ (283524063 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 561)) (n := 12)
    (lo := (141762031 / 500000000)) (hi := (283524063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 241) = 1/(241 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-283524063 / 1000000000) (-141762031 / 500000000) (Real.log (241 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (220405431 / 1000000000) ≤ -Real.log (2048 / 2553) ∧
    -Real.log (2048 / 2553) ≤ (27550679 / 125000000) := by
  have h := checkLog_sound (w := (505 / 4601)) (n := 12)
    (lo := (220405431 / 1000000000)) (hi := (27550679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2553 / 2048) = 1/(2048 / 2553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (220405431 / 1000000000) (27550679 / 125000000) (Real.log (2553 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2553 / 2048) = -Real.log (2048 / 2553) := by
    rw [show ((2553 / 2048) : ℝ) = ((2048 / 2553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (283135133 / 1000000000) ≤ -Real.log (1543 / 2048) ∧
    -Real.log (1543 / 2048) ≤ (141567567 / 500000000) := by
  have h := checkLog_sound (w := (505 / 3591)) (n := 12)
    (lo := (283135133 / 1000000000)) (hi := (141567567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1543) = 1/(1543 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-141567567 / 500000000) (-283135133 / 1000000000) (Real.log (1543 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50161217 / 125000000) ≤ -Real.log (160 / 239) ∧
    -Real.log (160 / 239) ≤ (401289737 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399)) (n := 12)
    (lo := (50161217 / 125000000)) (hi := (401289737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 160) = 1/(160 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50161217 / 125000000) (401289737 / 1000000000) (Real.log (239 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (239 / 160) = -Real.log (160 / 239) := by
    rw [show ((239 / 160) : ℝ) = ((160 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (34036233 / 50000000) ≤ -Real.log (81 / 160) ∧
    -Real.log (81 / 160) ≤ (680724661 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 81) = 1/(81 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-680724661 / 1000000000) (-34036233 / 50000000) (Real.log (81 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2004487 / 5000000) ≤ -Real.log (1024 / 1529) ∧
    -Real.log (1024 / 1529) ≤ (400897401 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 2553)) (n := 12)
    (lo := (2004487 / 5000000)) (hi := (400897401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1529 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1529 / 1024) = 1/(1024 / 1529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2004487 / 5000000) (400897401 / 1000000000) (Real.log (1529 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1529 / 1024) = -Real.log (1024 / 1529) := by
    rw [show ((1529 / 1024) : ℝ) = ((1024 / 1529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (339783961 / 500000000) ≤ -Real.log (519 / 1024) ∧
    -Real.log (519 / 1024) ≤ (679567923 / 1000000000) := by
  have h := checkLog_sound (w := (505 / 1543)) (n := 12)
    (lo := (339783961 / 500000000)) (hi := (679567923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 519) = 1/(519 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-679567923 / 1000000000) (-339783961 / 500000000) (Real.log (519 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (302075981 / 1000000000) ≤ -Real.log (125000 / 169083) ∧
    -Real.log (125000 / 169083) ≤ (151037991 / 500000000) := by
  have h := checkLog_sound (w := (44083 / 294083)) (n := 12)
    (lo := (302075981 / 1000000000)) (hi := (151037991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169083 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169083 / 125000) = 1/(125000 / 169083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (302075981 / 1000000000) (151037991 / 500000000) (Real.log (169083 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169083 / 125000) = -Real.log (125000 / 169083) := by
    rw [show ((169083 / 125000) : ℝ) = ((125000 / 169083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (434889799 / 1000000000) ≤ -Real.log (80917 / 125000) ∧
    -Real.log (80917 / 125000) ≤ (2174449 / 5000000) := by
  have h := checkLog_sound (w := (44083 / 205917)) (n := 12)
    (lo := (434889799 / 1000000000)) (hi := (2174449 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80917) = 1/(80917 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2174449 / 5000000) (-434889799 / 1000000000) (Real.log (80917 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (302394561 / 1000000000) ≤ -Real.log (200000 / 270619) ∧
    -Real.log (200000 / 270619) ≤ (151197281 / 500000000) := by
  have h := checkLog_sound (w := (70619 / 470619)) (n := 12)
    (lo := (302394561 / 1000000000)) (hi := (151197281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270619 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270619 / 200000) = 1/(200000 / 270619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (302394561 / 1000000000) (151197281 / 500000000) (Real.log (270619 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (270619 / 200000) = -Real.log (200000 / 270619) := by
    rw [show ((270619 / 200000) : ℝ) = ((200000 / 270619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (217777913 / 500000000) ≤ -Real.log (129381 / 200000) ∧
    -Real.log (129381 / 200000) ≤ (435555827 / 1000000000) := by
  have h := checkLog_sound (w := (70619 / 329381)) (n := 12)
    (lo := (217777913 / 500000000)) (hi := (435555827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129381) = 1/(129381 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-435555827 / 1000000000) (-217777913 / 500000000) (Real.log (129381 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7179007 / 31250000) ≤ -Real.log (500000 / 629129) ∧
    -Real.log (500000 / 629129) ≤ (9189129 / 40000000) := by
  have h := checkLog_sound (w := (129129 / 1129129)) (n := 12)
    (lo := (7179007 / 31250000)) (hi := (9189129 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629129 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629129 / 500000) = 1/(500000 / 629129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7179007 / 31250000) (9189129 / 40000000) (Real.log (629129 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (629129 / 500000) = -Real.log (500000 / 629129) := by
    rw [show ((629129 / 500000) : ℝ) = ((500000 / 629129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (59750761 / 200000000) ≤ -Real.log (370871 / 500000) ∧
    -Real.log (370871 / 500000) ≤ (149376903 / 500000000) := by
  have h := checkLog_sound (w := (129129 / 870871)) (n := 12)
    (lo := (59750761 / 200000000)) (hi := (149376903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370871) = 1/(370871 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-149376903 / 500000000) (-59750761 / 200000000) (Real.log (370871 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (229996813 / 1000000000) ≤ -Real.log (250000 / 314649) ∧
    -Real.log (250000 / 314649) ≤ (114998407 / 500000000) := by
  have h := checkLog_sound (w := (64649 / 564649)) (n := 12)
    (lo := (229996813 / 1000000000)) (hi := (114998407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314649 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314649 / 250000) = 1/(250000 / 314649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229996813 / 1000000000) (114998407 / 500000000) (Real.log (314649 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (314649 / 250000) = -Real.log (250000 / 314649) := by
    rw [show ((314649 / 250000) : ℝ) = ((250000 / 314649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299209593 / 1000000000) ≤ -Real.log (185351 / 250000) ∧
    -Real.log (185351 / 250000) ≤ (149604797 / 500000000) := by
  have h := checkLog_sound (w := (64649 / 435351)) (n := 12)
    (lo := (299209593 / 1000000000)) (hi := (149604797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185351) = 1/(185351 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-149604797 / 500000000) (-299209593 / 1000000000) (Real.log (185351 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36848289 / 50000000) ≤ -Real.log (125000000000 / 261198203097) ∧
    -Real.log (125000000000 / 261198203097) ≤ (368482891 / 500000000) := by
  have h := checkLog_sound (w := (11198203097 / 511198203097)) (n := 12)
    (lo := (219093 / 5000000)) (hi := (43818601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261198203097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261198203097 / 250000000000) = 1/(125000000000 / 261198203097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36848289 / 50000000) (368482891 / 500000000) (Real.log (261198203097 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (261198203097 / 125000000000) = -Real.log (125000000000 / 261198203097) := by
    rw [show ((261198203097 / 125000000000) : ℝ) = ((125000000000 / 261198203097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (737950387 / 1000000000) ≤ -Real.log (50000000000 / 104582202951) ∧
    -Real.log (50000000000 / 104582202951) ≤ (737950389 / 1000000000) := by
  have h := checkLog_sound (w := (4582202951 / 204582202951)) (n := 12)
    (lo := (44803207 / 1000000000)) (hi := (5600401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104582202951 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104582202951 / 100000000000) = 1/(50000000000 / 104582202951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (737950387 / 1000000000) (737950389 / 1000000000) (Real.log (104582202951 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (104582202951 / 50000000000) = -Real.log (50000000000 / 104582202951) := by
    rw [show ((104582202951 / 50000000000) : ℝ) = ((50000000000 / 104582202951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (528482029 / 1000000000) ≤ -Real.log (100000000000 / 169635533649) ∧
    -Real.log (100000000000 / 169635533649) ≤ (52848203 / 100000000) := by
  have h := checkLog_sound (w := (69635533649 / 269635533649)) (n := 12)
    (lo := (528482029 / 1000000000)) (hi := (52848203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169635533649 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169635533649 / 100000000000) = 1/(100000000000 / 169635533649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (528482029 / 1000000000) (52848203 / 100000000) (Real.log (169635533649 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (169635533649 / 100000000000) = -Real.log (100000000000 / 169635533649) := by
    rw [show ((169635533649 / 100000000000) : ℝ) = ((100000000000 / 169635533649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (529206407 / 1000000000) ≤ -Real.log (500000000000 / 848792291383) ∧
    -Real.log (500000000000 / 848792291383) ≤ (66150801 / 125000000) := by
  have h := checkLog_sound (w := (348792291383 / 1348792291383)) (n := 12)
    (lo := (529206407 / 1000000000)) (hi := (66150801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848792291383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848792291383 / 500000000000) = 1/(500000000000 / 848792291383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (529206407 / 1000000000) (66150801 / 125000000) (Real.log (848792291383 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (848792291383 / 500000000000) = -Real.log (500000000000 / 848792291383) := by
    rw [show ((848792291383 / 500000000000) : ℝ) = ((500000000000 / 848792291383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0314
