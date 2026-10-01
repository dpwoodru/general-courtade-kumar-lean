import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0138
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

theorem reflection_log_1_neg : (300972271 / 1000000000) ≤ -Real.log (2560 / 3459) ∧
    -Real.log (2560 / 3459) ≤ (18810767 / 62500000) := by
  have h := checkLog_sound (w := (899 / 6019)) (n := 12)
    (lo := (300972271 / 1000000000)) (hi := (18810767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3459 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3459 / 2560) = 1/(2560 / 3459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (300972271 / 1000000000) (18810767 / 62500000) (Real.log (3459 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3459 / 2560) = -Real.log (2560 / 3459) := by
    rw [show ((3459 / 2560) : ℝ) = ((2560 / 3459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (432587427 / 1000000000) ≤ -Real.log (1661 / 2560) ∧
    -Real.log (1661 / 2560) ≤ (108146857 / 250000000) := by
  have h := checkLog_sound (w := (899 / 4221)) (n := 12)
    (lo := (432587427 / 1000000000)) (hi := (108146857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1661) = 1/(1661 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-108146857 / 250000000) (-432587427 / 1000000000) (Real.log (1661 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (266002989 / 500000000) ≤ -Real.log (1280 / 2179) ∧
    -Real.log (1280 / 2179) ≤ (532005979 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 3459)) (n := 12)
    (lo := (266002989 / 500000000)) (hi := (532005979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 1280) = 1/(1280 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (266002989 / 500000000) (532005979 / 1000000000) (Real.log (2179 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2179 / 1280) = -Real.log (1280 / 2179) := by
    rw [show ((2179 / 1280) : ℝ) = ((1280 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1211815981 / 1000000000) ≤ -Real.log (381 / 1280) ∧
    -Real.log (381 / 1280) ≤ (1211815983 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 381) = 1/(381 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1211815983 / 1000000000) (-1211815981 / 1000000000) (Real.log (381 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (530628251 / 1000000000) ≤ -Real.log (10 / 17) ∧
    -Real.log (10 / 17) ≤ (132657063 / 250000000) := by
  have h := checkLog_sound (w := (7 / 27)) (n := 12)
    (lo := (530628251 / 1000000000)) (hi := (132657063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17 / 10) = 1/(10 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (530628251 / 1000000000) (132657063 / 250000000) (Real.log (17 / 10)) := by
  have h := reflection_log_7_neg
  have he : Real.log (17 / 10) = -Real.log (10 / 17) := by
    rw [show ((17 / 10) : ℝ) = ((10 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1203972803 / 1000000000) ≤ -Real.log (3 / 10) ∧
    -Real.log (3 / 10) ≤ (240794561 / 200000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 3) = 1/(3 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240794561 / 200000000) (-1203972803 / 1000000000) (Real.log (3 / 10)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (102686949 / 250000000) ≤ -Real.log (200000 / 301589) ∧
    -Real.log (200000 / 301589) ≤ (410747797 / 1000000000) := by
  have h := checkLog_sound (w := (101589 / 501589)) (n := 12)
    (lo := (102686949 / 250000000)) (hi := (410747797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301589 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301589 / 200000) = 1/(200000 / 301589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (102686949 / 250000000) (410747797 / 1000000000) (Real.log (301589 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (301589 / 200000) = -Real.log (200000 / 301589) := by
    rw [show ((301589 / 200000) : ℝ) = ((200000 / 301589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (709164779 / 1000000000) ≤ -Real.log (98411 / 200000) ∧
    -Real.log (98411 / 200000) ≤ (709164781 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 198411)) (n := 12)
    (lo := (16017599 / 1000000000)) (hi := (10011 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 98411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 98411) = 1/(98411 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-709164781 / 1000000000) (-709164779 / 1000000000) (Real.log (98411 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (205976011 / 500000000) ≤ -Real.log (500000 / 754881) ∧
    -Real.log (500000 / 754881) ≤ (411952023 / 1000000000) := by
  have h := checkLog_sound (w := (254881 / 1254881)) (n := 12)
    (lo := (205976011 / 500000000)) (hi := (411952023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754881 / 500000) = 1/(500000 / 754881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (205976011 / 500000000) (411952023 / 1000000000) (Real.log (754881 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (754881 / 500000) = -Real.log (500000 / 754881) := by
    rw [show ((754881 / 500000) : ℝ) = ((500000 / 754881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71286429 / 100000000) ≤ -Real.log (245119 / 500000) ∧
    -Real.log (245119 / 500000) ≤ (178216073 / 250000000) := by
  have h := checkLog_sound (w := (4881 / 495119)) (n := 12)
    (lo := (1971711 / 100000000)) (hi := (19717111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 245119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 245119) = 1/(245119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-178216073 / 250000000) (-71286429 / 100000000) (Real.log (245119 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (163456561 / 500000000) ≤ -Real.log (1000000 / 1386681) ∧
    -Real.log (1000000 / 1386681) ≤ (326913123 / 1000000000) := by
  have h := checkLog_sound (w := (386681 / 2386681)) (n := 12)
    (lo := (163456561 / 500000000)) (hi := (326913123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1386681 / 1000000) = 1/(1000000 / 1386681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (163456561 / 500000000) (326913123 / 1000000000) (Real.log (1386681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1386681 / 1000000) = -Real.log (1000000 / 1386681) := by
    rw [show ((1386681 / 1000000) : ℝ) = ((1000000 / 1386681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (244435043 / 500000000) ≤ -Real.log (613319 / 1000000) ∧
    -Real.log (613319 / 1000000) ≤ (488870087 / 1000000000) := by
  have h := checkLog_sound (w := (386681 / 1613319)) (n := 12)
    (lo := (244435043 / 500000000)) (hi := (488870087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 613319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 613319) = 1/(613319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-488870087 / 1000000000) (-244435043 / 500000000) (Real.log (613319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (328062689 / 1000000000) ≤ -Real.log (250000 / 347069) ∧
    -Real.log (250000 / 347069) ≤ (32806269 / 100000000) := by
  have h := checkLog_sound (w := (97069 / 597069)) (n := 12)
    (lo := (328062689 / 1000000000)) (hi := (32806269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347069 / 250000) = 1/(250000 / 347069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (328062689 / 1000000000) (32806269 / 100000000) (Real.log (347069 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (347069 / 250000) = -Real.log (250000 / 347069) := by
    rw [show ((347069 / 250000) : ℝ) = ((250000 / 347069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245737039 / 500000000) ≤ -Real.log (152931 / 250000) ∧
    -Real.log (152931 / 250000) ≤ (491474079 / 1000000000) := by
  have h := checkLog_sound (w := (97069 / 402931)) (n := 12)
    (lo := (245737039 / 500000000)) (hi := (491474079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152931) = 1/(152931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-491474079 / 1000000000) (-245737039 / 500000000) (Real.log (152931 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (8749317 / 7812500) ≤ -Real.log (250000000000 / 766146568981) ∧
    -Real.log (250000000000 / 766146568981) ≤ (559956289 / 500000000) := by
  have h := checkLog_sound (w := (266146568981 / 1266146568981)) (n := 12)
    (lo := (106691349 / 250000000)) (hi := (426765397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766146568981 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(766146568981 / 500000000000) = 1/(250000000000 / 766146568981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8749317 / 7812500) (559956289 / 500000000) (Real.log (766146568981 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (766146568981 / 250000000000) = -Real.log (250000000000 / 766146568981) := by
    rw [show ((766146568981 / 250000000000) : ℝ) = ((250000000000 / 766146568981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1124816313 / 1000000000) ≤ -Real.log (500000000000 / 1539825554119) ∧
    -Real.log (500000000000 / 1539825554119) ≤ (224963263 / 200000000) := by
  have h := checkLog_sound (w := (539825554119 / 2539825554119)) (n := 12)
    (lo := (431669133 / 1000000000)) (hi := (215834567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539825554119 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1539825554119 / 1000000000000) = 1/(500000000000 / 1539825554119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1124816313 / 1000000000) (224963263 / 200000000) (Real.log (1539825554119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1539825554119 / 500000000000) = -Real.log (500000000000 / 1539825554119) := by
    rw [show ((1539825554119 / 500000000000) : ℝ) = ((500000000000 / 1539825554119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (101972901 / 125000000) ≤ -Real.log (500000000000 / 1130472886051) ∧
    -Real.log (500000000000 / 1130472886051) ≤ (81578321 / 100000000) := by
  have h := checkLog_sound (w := (130472886051 / 2130472886051)) (n := 12)
    (lo := (30659007 / 250000000)) (hi := (122636029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130472886051 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1130472886051 / 1000000000000) = 1/(500000000000 / 1130472886051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (101972901 / 125000000) (81578321 / 100000000) (Real.log (1130472886051 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1130472886051 / 500000000000) = -Real.log (500000000000 / 1130472886051) := by
    rw [show ((1130472886051 / 500000000000) : ℝ) = ((500000000000 / 1130472886051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (819536767 / 1000000000) ≤ -Real.log (250000000000 / 567362078323) ∧
    -Real.log (250000000000 / 567362078323) ≤ (819536769 / 1000000000) := by
  have h := checkLog_sound (w := (67362078323 / 1067362078323)) (n := 12)
    (lo := (126389587 / 1000000000)) (hi := (31597397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567362078323 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567362078323 / 500000000000) = 1/(250000000000 / 567362078323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (819536767 / 1000000000) (819536769 / 1000000000) (Real.log (567362078323 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (567362078323 / 250000000000) = -Real.log (250000000000 / 567362078323) := by
    rw [show ((567362078323 / 250000000000) : ℝ) = ((250000000000 / 567362078323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0138
