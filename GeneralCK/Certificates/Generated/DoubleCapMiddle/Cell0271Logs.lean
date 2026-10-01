import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0271
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

theorem reflection_log_1_neg : (233248573 / 1000000000) ≤ -Real.log (1024 / 1293) ∧
    -Real.log (1024 / 1293) ≤ (116624287 / 500000000) := by
  have h := checkLog_sound (w := (269 / 2317)) (n := 12)
    (lo := (233248573 / 1000000000)) (hi := (116624287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1024) = 1/(1024 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (233248573 / 1000000000) (116624287 / 500000000) (Real.log (1293 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1293 / 1024) = -Real.log (1024 / 1293) := by
    rw [show ((1293 / 1024) : ℝ) = ((1024 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38094257 / 125000000) ≤ -Real.log (755 / 1024) ∧
    -Real.log (755 / 1024) ≤ (304754057 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1779)) (n := 12)
    (lo := (38094257 / 125000000)) (hi := (304754057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 755) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 755) = 1/(755 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-304754057 / 1000000000) (-38094257 / 125000000) (Real.log (755 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58196107 / 250000000) ≤ -Real.log (2560 / 3231) ∧
    -Real.log (2560 / 3231) ≤ (232784429 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 5791)) (n := 12)
    (lo := (58196107 / 250000000)) (hi := (232784429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3231 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3231 / 2560) = 1/(2560 / 3231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58196107 / 250000000) (232784429 / 1000000000) (Real.log (3231 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3231 / 2560) = -Real.log (2560 / 3231) := by
    rw [show ((3231 / 2560) : ℝ) = ((2560 / 3231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (303959669 / 1000000000) ≤ -Real.log (1889 / 2560) ∧
    -Real.log (1889 / 2560) ≤ (30395967 / 100000000) := by
  have h := checkLog_sound (w := (671 / 4449)) (n := 12)
    (lo := (303959669 / 1000000000)) (hi := (30395967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1889) = 1/(1889 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30395967 / 100000000) (-303959669 / 1000000000) (Real.log (1889 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (105562631 / 250000000) ≤ -Real.log (512 / 781) ∧
    -Real.log (512 / 781) ≤ (16890021 / 40000000) := by
  have h := checkLog_sound (w := (269 / 1293)) (n := 12)
    (lo := (105562631 / 250000000)) (hi := (16890021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781 / 512) = 1/(512 / 781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (105562631 / 250000000) (16890021 / 40000000) (Real.log (781 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (781 / 512) = -Real.log (512 / 781) := by
    rw [show ((781 / 512) : ℝ) = ((512 / 781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (745263181 / 1000000000) ≤ -Real.log (243 / 512) ∧
    -Real.log (243 / 512) ≤ (745263183 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 499)) (n := 12)
    (lo := (52116001 / 1000000000)) (hi := (26058001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 243) = 1/(243 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-745263183 / 1000000000) (-745263181 / 1000000000) (Real.log (243 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (421481983 / 1000000000) ≤ -Real.log (1280 / 1951) ∧
    -Real.log (1280 / 1951) ≤ (823207 / 1953125) := by
  have h := checkLog_sound (w := (671 / 3231)) (n := 12)
    (lo := (421481983 / 1000000000)) (hi := (823207 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1280) = 1/(1280 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (421481983 / 1000000000) (823207 / 1953125) (Real.log (1951 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1951 / 1280) = -Real.log (1280 / 1951) := by
    rw [show ((1951 / 1280) : ℝ) = ((1280 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23212409 / 31250000) ≤ -Real.log (609 / 1280) ∧
    -Real.log (609 / 1280) ≤ (74279709 / 100000000) := by
  have h := checkLog_sound (w := (31 / 1249)) (n := 12)
    (lo := (12412477 / 250000000)) (hi := (49649909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 609) = 1/(609 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-74279709 / 100000000) (-23212409 / 31250000) (Real.log (609 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79703053 / 250000000) ≤ -Real.log (1000000 / 1375493) ∧
    -Real.log (1000000 / 1375493) ≤ (318812213 / 1000000000) := by
  have h := checkLog_sound (w := (375493 / 2375493)) (n := 12)
    (lo := (79703053 / 250000000)) (hi := (318812213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1375493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1375493 / 1000000) = 1/(1000000 / 1375493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79703053 / 250000000) (318812213 / 1000000000) (Real.log (1375493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1375493 / 1000000) = -Real.log (1000000 / 1375493) := by
    rw [show ((1375493 / 1000000) : ℝ) = ((1000000 / 1375493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23539637 / 50000000) ≤ -Real.log (624507 / 1000000) ∧
    -Real.log (624507 / 1000000) ≤ (470792741 / 1000000000) := by
  have h := checkLog_sound (w := (375493 / 1624507)) (n := 12)
    (lo := (23539637 / 50000000)) (hi := (470792741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 624507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 624507) = 1/(624507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-470792741 / 1000000000) (-23539637 / 50000000) (Real.log (624507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3993011 / 12500000) ≤ -Real.log (500000 / 688179) ∧
    -Real.log (500000 / 688179) ≤ (319440881 / 1000000000) := by
  have h := checkLog_sound (w := (188179 / 1188179)) (n := 12)
    (lo := (3993011 / 12500000)) (hi := (319440881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688179 / 500000) = 1/(500000 / 688179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3993011 / 12500000) (319440881 / 1000000000) (Real.log (688179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (688179 / 500000) = -Real.log (500000 / 688179) := by
    rw [show ((688179 / 500000) : ℝ) = ((500000 / 688179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (472178793 / 1000000000) ≤ -Real.log (311821 / 500000) ∧
    -Real.log (311821 / 500000) ≤ (236089397 / 500000000) := by
  have h := checkLog_sound (w := (188179 / 811821)) (n := 12)
    (lo := (472178793 / 1000000000)) (hi := (236089397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311821) = 1/(311821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-236089397 / 500000000) (-472178793 / 1000000000) (Real.log (311821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (30494483 / 125000000) ≤ -Real.log (15625 / 19942) ∧
    -Real.log (15625 / 19942) ≤ (48791173 / 200000000) := by
  have h := checkLog_sound (w := (4317 / 35567)) (n := 12)
    (lo := (30494483 / 125000000)) (hi := (48791173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19942 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19942 / 15625) = 1/(15625 / 19942) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (30494483 / 125000000) (48791173 / 200000000) (Real.log (19942 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19942 / 15625) = -Real.log (15625 / 19942) := by
    rw [show ((19942 / 15625) : ℝ) = ((15625 / 19942) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64672351 / 200000000) ≤ -Real.log (11308 / 15625) ∧
    -Real.log (11308 / 15625) ≤ (80840439 / 250000000) := by
  have h := checkLog_sound (w := (4317 / 26933)) (n := 12)
    (lo := (64672351 / 200000000)) (hi := (80840439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11308) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11308) = 1/(11308 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-80840439 / 250000000) (-64672351 / 200000000) (Real.log (11308 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (122247391 / 500000000) ≤ -Real.log (62500 / 79811) ∧
    -Real.log (62500 / 79811) ≤ (244494783 / 1000000000) := by
  have h := checkLog_sound (w := (17311 / 142311)) (n := 12)
    (lo := (122247391 / 500000000)) (hi := (244494783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79811 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79811 / 62500) = 1/(62500 / 79811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (122247391 / 500000000) (244494783 / 1000000000) (Real.log (79811 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79811 / 62500) = -Real.log (62500 / 79811) := by
    rw [show ((79811 / 62500) : ℝ) = ((62500 / 79811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162156431 / 500000000) ≤ -Real.log (45189 / 62500) ∧
    -Real.log (45189 / 62500) ≤ (324312863 / 1000000000) := by
  have h := checkLog_sound (w := (17311 / 107689)) (n := 12)
    (lo := (162156431 / 500000000)) (hi := (324312863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45189) = 1/(45189 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-324312863 / 1000000000) (-162156431 / 500000000) (Real.log (45189 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (98700619 / 125000000) ≤ -Real.log (250000000000 / 550631538157) ∧
    -Real.log (250000000000 / 550631538157) ≤ (394802477 / 500000000) := by
  have h := checkLog_sound (w := (50631538157 / 1050631538157)) (n := 12)
    (lo := (24114443 / 250000000)) (hi := (96457773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550631538157 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(550631538157 / 500000000000) = 1/(250000000000 / 550631538157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (98700619 / 125000000) (394802477 / 500000000) (Real.log (550631538157 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (550631538157 / 250000000000) = -Real.log (250000000000 / 550631538157) := by
    rw [show ((550631538157 / 250000000000) : ℝ) = ((250000000000 / 550631538157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (98952459 / 125000000) ≤ -Real.log (100000000000 / 220696810029) ∧
    -Real.log (100000000000 / 220696810029) ≤ (395809837 / 500000000) := by
  have h := checkLog_sound (w := (20696810029 / 420696810029)) (n := 12)
    (lo := (24618123 / 250000000)) (hi := (98472493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220696810029 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(220696810029 / 200000000000) = 1/(100000000000 / 220696810029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (98952459 / 125000000) (395809837 / 500000000) (Real.log (220696810029 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (220696810029 / 100000000000) = -Real.log (100000000000 / 220696810029) := by
    rw [show ((220696810029 / 100000000000) : ℝ) = ((100000000000 / 220696810029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28365881 / 50000000) ≤ -Real.log (500000000000 / 881765122037) ∧
    -Real.log (500000000000 / 881765122037) ≤ (567317621 / 1000000000) := by
  have h := checkLog_sound (w := (381765122037 / 1381765122037)) (n := 12)
    (lo := (28365881 / 50000000)) (hi := (567317621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881765122037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881765122037 / 500000000000) = 1/(500000000000 / 881765122037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (28365881 / 50000000) (567317621 / 1000000000) (Real.log (881765122037 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (881765122037 / 500000000000) = -Real.log (500000000000 / 881765122037) := by
    rw [show ((881765122037 / 500000000000) : ℝ) = ((500000000000 / 881765122037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (113761529 / 200000000) ≤ -Real.log (250000000000 / 441539976543) ∧
    -Real.log (250000000000 / 441539976543) ≤ (284403823 / 500000000) := by
  have h := checkLog_sound (w := (191539976543 / 691539976543)) (n := 12)
    (lo := (113761529 / 200000000)) (hi := (284403823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441539976543 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441539976543 / 250000000000) = 1/(250000000000 / 441539976543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (113761529 / 200000000) (284403823 / 500000000) (Real.log (441539976543 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (441539976543 / 250000000000) = -Real.log (250000000000 / 441539976543) := by
    rw [show ((441539976543 / 250000000000) : ℝ) = ((250000000000 / 441539976543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0271
