import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0466
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

theorem reflection_log_1_neg : (23034097 / 125000000) ≤ -Real.log (1280 / 1539) ∧
    -Real.log (1280 / 1539) ≤ (184272777 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2819)) (n := 12)
    (lo := (23034097 / 125000000)) (hi := (184272777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1280) = 1/(1280 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23034097 / 125000000) (184272777 / 1000000000) (Real.log (1539 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1539 / 1280) = -Real.log (1280 / 1539) := by
    rw [show ((1539 / 1280) : ℝ) = ((1280 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113038769 / 500000000) ≤ -Real.log (1021 / 1280) ∧
    -Real.log (1021 / 1280) ≤ (226077539 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2301)) (n := 12)
    (lo := (113038769 / 500000000)) (hi := (226077539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1021) = 1/(1021 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-226077539 / 1000000000) (-113038769 / 500000000) (Real.log (1021 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92014541 / 500000000) ≤ -Real.log (10240 / 12309) ∧
    -Real.log (10240 / 12309) ≤ (184029083 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 22549)) (n := 12)
    (lo := (92014541 / 500000000)) (hi := (184029083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12309 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12309 / 10240) = 1/(10240 / 12309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92014541 / 500000000) (184029083 / 1000000000) (Real.log (12309 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12309 / 10240) = -Real.log (10240 / 12309) := by
    rw [show ((12309 / 10240) : ℝ) = ((10240 / 12309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225710319 / 1000000000) ≤ -Real.log (8171 / 10240) ∧
    -Real.log (8171 / 10240) ≤ (2821379 / 12500000) := by
  have h := checkLog_sound (w := (2069 / 18411)) (n := 12)
    (lo := (225710319 / 1000000000)) (hi := (2821379 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8171) = 1/(8171 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2821379 / 12500000) (-225710319 / 1000000000) (Real.log (8171 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169907429 / 500000000) ≤ -Real.log (640 / 899) ∧
    -Real.log (640 / 899) ≤ (339814859 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1539)) (n := 12)
    (lo := (169907429 / 500000000)) (hi := (339814859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899 / 640) = 1/(640 / 899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169907429 / 500000000) (339814859 / 1000000000) (Real.log (899 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (899 / 640) = -Real.log (640 / 899) := by
    rw [show ((899 / 640) : ℝ) = ((640 / 899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518668801 / 1000000000) ≤ -Real.log (381 / 640) ∧
    -Real.log (381 / 640) ≤ (259334401 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 381) = 1/(381 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259334401 / 500000000) (-518668801 / 1000000000) (Real.log (381 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8484941 / 25000000) ≤ -Real.log (5120 / 7189) ∧
    -Real.log (5120 / 7189) ≤ (339397641 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 12309)) (n := 12)
    (lo := (8484941 / 25000000)) (hi := (339397641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7189 / 5120) = 1/(5120 / 7189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8484941 / 25000000) (339397641 / 1000000000) (Real.log (7189 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7189 / 5120) = -Real.log (5120 / 7189) := by
    rw [show ((7189 / 5120) : ℝ) = ((5120 / 7189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (517685033 / 1000000000) ≤ -Real.log (3051 / 5120) ∧
    -Real.log (3051 / 5120) ≤ (258842517 / 500000000) := by
  have h := checkLog_sound (w := (2069 / 8171)) (n := 12)
    (lo := (517685033 / 1000000000)) (hi := (258842517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3051) = 1/(3051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258842517 / 500000000) (-517685033 / 1000000000) (Real.log (3051 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252959407 / 1000000000) ≤ -Real.log (1000000 / 1287831) ∧
    -Real.log (1000000 / 1287831) ≤ (15809963 / 62500000) := by
  have h := checkLog_sound (w := (287831 / 2287831)) (n := 12)
    (lo := (252959407 / 1000000000)) (hi := (15809963 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287831 / 1000000) = 1/(1000000 / 1287831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252959407 / 1000000000) (15809963 / 62500000) (Real.log (1287831 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1287831 / 1000000) = -Real.log (1000000 / 1287831) := by
    rw [show ((1287831 / 1000000) : ℝ) = ((1000000 / 1287831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84860009 / 250000000) ≤ -Real.log (712169 / 1000000) ∧
    -Real.log (712169 / 1000000) ≤ (339440037 / 1000000000) := by
  have h := checkLog_sound (w := (287831 / 1712169)) (n := 12)
    (lo := (84860009 / 250000000)) (hi := (339440037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712169) = 1/(712169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-339440037 / 1000000000) (-84860009 / 250000000) (Real.log (712169 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50657873 / 200000000) ≤ -Real.log (15625 / 20129) ∧
    -Real.log (15625 / 20129) ≤ (126644683 / 500000000) := by
  have h := checkLog_sound (w := (2252 / 17877)) (n := 12)
    (lo := (50657873 / 200000000)) (hi := (126644683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20129 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20129 / 15625) = 1/(15625 / 20129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50657873 / 200000000) (126644683 / 500000000) (Real.log (20129 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20129 / 15625) = -Real.log (15625 / 20129) := by
    rw [show ((20129 / 15625) : ℝ) = ((15625 / 20129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170018491 / 500000000) ≤ -Real.log (11121 / 15625) ∧
    -Real.log (11121 / 15625) ≤ (340036983 / 1000000000) := by
  have h := checkLog_sound (w := (2252 / 13373)) (n := 12)
    (lo := (170018491 / 500000000)) (hi := (340036983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11121) = 1/(11121 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-340036983 / 1000000000) (-170018491 / 500000000) (Real.log (11121 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94609689 / 500000000) ≤ -Real.log (500000 / 604153) ∧
    -Real.log (500000 / 604153) ≤ (189219379 / 1000000000) := by
  have h := checkLog_sound (w := (104153 / 1104153)) (n := 12)
    (lo := (94609689 / 500000000)) (hi := (189219379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604153 / 500000) = 1/(500000 / 604153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94609689 / 500000000) (189219379 / 1000000000) (Real.log (604153 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (604153 / 500000) = -Real.log (500000 / 604153) := by
    rw [show ((604153 / 500000) : ℝ) = ((500000 / 604153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9343213 / 40000000) ≤ -Real.log (395847 / 500000) ∧
    -Real.log (395847 / 500000) ≤ (116790163 / 500000000) := by
  have h := checkLog_sound (w := (104153 / 895847)) (n := 12)
    (lo := (9343213 / 40000000)) (hi := (116790163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395847) = 1/(395847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116790163 / 500000000) (-9343213 / 40000000) (Real.log (395847 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (189485831 / 1000000000) ≤ -Real.log (250000 / 302157) ∧
    -Real.log (250000 / 302157) ≤ (23685729 / 125000000) := by
  have h := checkLog_sound (w := (52157 / 552157)) (n := 12)
    (lo := (189485831 / 1000000000)) (hi := (23685729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302157 / 250000) = 1/(250000 / 302157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (189485831 / 1000000000) (23685729 / 125000000) (Real.log (302157 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (302157 / 250000) = -Real.log (250000 / 302157) := by
    rw [show ((302157 / 250000) : ℝ) = ((250000 / 302157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23398713 / 100000000) ≤ -Real.log (197843 / 250000) ∧
    -Real.log (197843 / 250000) ≤ (233987131 / 1000000000) := by
  have h := checkLog_sound (w := (52157 / 447843)) (n := 12)
    (lo := (23398713 / 100000000)) (hi := (233987131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197843) = 1/(197843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-233987131 / 1000000000) (-23398713 / 100000000) (Real.log (197843 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (148099861 / 250000000) ≤ -Real.log (500000000000 / 904161090977) ∧
    -Real.log (500000000000 / 904161090977) ≤ (118479889 / 200000000) := by
  have h := checkLog_sound (w := (404161090977 / 1404161090977)) (n := 12)
    (lo := (148099861 / 250000000)) (hi := (118479889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904161090977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904161090977 / 500000000000) = 1/(500000000000 / 904161090977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (148099861 / 250000000) (118479889 / 200000000) (Real.log (904161090977 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (904161090977 / 500000000000) = -Real.log (500000000000 / 904161090977) := by
    rw [show ((904161090977 / 500000000000) : ℝ) = ((500000000000 / 904161090977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (148331587 / 250000000) ≤ -Real.log (500000000000 / 904999550401) ∧
    -Real.log (500000000000 / 904999550401) ≤ (593326349 / 1000000000) := by
  have h := checkLog_sound (w := (404999550401 / 1404999550401)) (n := 12)
    (lo := (148331587 / 250000000)) (hi := (593326349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904999550401 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904999550401 / 500000000000) = 1/(500000000000 / 904999550401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (148331587 / 250000000) (593326349 / 1000000000) (Real.log (904999550401 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (904999550401 / 500000000000) = -Real.log (500000000000 / 904999550401) := by
    rw [show ((904999550401 / 500000000000) : ℝ) = ((500000000000 / 904999550401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52849963 / 125000000) ≤ -Real.log (250000000000 / 381557142027) ∧
    -Real.log (250000000000 / 381557142027) ≤ (84559941 / 200000000) := by
  have h := checkLog_sound (w := (131557142027 / 631557142027)) (n := 12)
    (lo := (52849963 / 125000000)) (hi := (84559941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381557142027 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381557142027 / 250000000000) = 1/(250000000000 / 381557142027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52849963 / 125000000) (84559941 / 200000000) (Real.log (381557142027 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (381557142027 / 250000000000) = -Real.log (250000000000 / 381557142027) := by
    rw [show ((381557142027 / 250000000000) : ℝ) = ((250000000000 / 381557142027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (211736481 / 500000000) ≤ -Real.log (250000000000 / 381814115233) ∧
    -Real.log (250000000000 / 381814115233) ≤ (423472963 / 1000000000) := by
  have h := checkLog_sound (w := (131814115233 / 631814115233)) (n := 12)
    (lo := (211736481 / 500000000)) (hi := (423472963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381814115233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381814115233 / 250000000000) = 1/(250000000000 / 381814115233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (211736481 / 500000000) (423472963 / 1000000000) (Real.log (381814115233 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381814115233 / 250000000000) = -Real.log (250000000000 / 381814115233) := by
    rw [show ((381814115233 / 250000000000) : ℝ) = ((250000000000 / 381814115233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0466
