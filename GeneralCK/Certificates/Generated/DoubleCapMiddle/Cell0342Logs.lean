import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0342
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

theorem reflection_log_1_neg : (214039737 / 1000000000) ≤ -Real.log (2560 / 3171) ∧
    -Real.log (2560 / 3171) ≤ (107019869 / 500000000) := by
  have h := checkLog_sound (w := (611 / 5731)) (n := 12)
    (lo := (214039737 / 1000000000)) (hi := (107019869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3171 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3171 / 2560) = 1/(2560 / 3171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (214039737 / 1000000000) (107019869 / 500000000) (Real.log (3171 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3171 / 2560) = -Real.log (2560 / 3171) := by
    rw [show ((3171 / 2560) : ℝ) = ((2560 / 3171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (272690837 / 1000000000) ≤ -Real.log (1949 / 2560) ∧
    -Real.log (1949 / 2560) ≤ (136345419 / 500000000) := by
  have h := checkLog_sound (w := (611 / 4509)) (n := 12)
    (lo := (272690837 / 1000000000)) (hi := (136345419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1949) = 1/(1949 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-136345419 / 500000000) (-272690837 / 1000000000) (Real.log (1949 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21380319 / 100000000) ≤ -Real.log (10240 / 12681) ∧
    -Real.log (10240 / 12681) ≤ (213803191 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 22921)) (n := 12)
    (lo := (21380319 / 100000000)) (hi := (213803191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12681 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12681 / 10240) = 1/(10240 / 12681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21380319 / 100000000) (213803191 / 1000000000) (Real.log (12681 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12681 / 10240) = -Real.log (10240 / 12681) := by
    rw [show ((12681 / 10240) : ℝ) = ((10240 / 12681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (272306099 / 1000000000) ≤ -Real.log (7799 / 10240) ∧
    -Real.log (7799 / 10240) ≤ (2723061 / 10000000) := by
  have h := checkLog_sound (w := (2441 / 18039)) (n := 12)
    (lo := (272306099 / 1000000000)) (hi := (2723061 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7799) = 1/(7799 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2723061 / 10000000) (-272306099 / 1000000000) (Real.log (7799 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (390245711 / 1000000000) ≤ -Real.log (1280 / 1891) ∧
    -Real.log (1280 / 1891) ≤ (24390357 / 62500000) := by
  have h := checkLog_sound (w := (611 / 3171)) (n := 12)
    (lo := (390245711 / 1000000000)) (hi := (24390357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1891 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1891 / 1280) = 1/(1280 / 1891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (390245711 / 1000000000) (24390357 / 62500000) (Real.log (1891 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1891 / 1280) = -Real.log (1280 / 1891) := by
    rw [show ((1891 / 1280) : ℝ) = ((1280 / 1891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10137989 / 15625000) ≤ -Real.log (669 / 1280) ∧
    -Real.log (669 / 1280) ≤ (648831297 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1949)) (n := 12)
    (lo := (10137989 / 15625000)) (hi := (648831297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 669) = 1/(669 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-648831297 / 1000000000) (-10137989 / 15625000) (Real.log (669 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (389849017 / 1000000000) ≤ -Real.log (5120 / 7561) ∧
    -Real.log (5120 / 7561) ≤ (194924509 / 500000000) := by
  have h := checkLog_sound (w := (2441 / 12681)) (n := 12)
    (lo := (389849017 / 1000000000)) (hi := (194924509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7561 / 5120) = 1/(5120 / 7561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (389849017 / 1000000000) (194924509 / 500000000) (Real.log (7561 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7561 / 5120) = -Real.log (5120 / 7561) := by
    rw [show ((7561 / 5120) : ℝ) = ((5120 / 7561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5060241 / 7812500) ≤ -Real.log (2679 / 5120) ∧
    -Real.log (2679 / 5120) ≤ (647710849 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 7799)) (n := 12)
    (lo := (5060241 / 7812500)) (hi := (647710849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2679) = 1/(2679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-647710849 / 1000000000) (-5060241 / 7812500) (Real.log (2679 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2931583 / 10000000) ≤ -Real.log (200000 / 268131) ∧
    -Real.log (200000 / 268131) ≤ (293158301 / 1000000000) := by
  have h := checkLog_sound (w := (68131 / 468131)) (n := 12)
    (lo := (2931583 / 10000000)) (hi := (293158301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268131 / 200000) = 1/(200000 / 268131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2931583 / 10000000) (293158301 / 1000000000) (Real.log (268131 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (268131 / 200000) = -Real.log (200000 / 268131) := by
    rw [show ((268131 / 200000) : ℝ) = ((200000 / 268131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10412709 / 25000000) ≤ -Real.log (131869 / 200000) ∧
    -Real.log (131869 / 200000) ≤ (416508361 / 1000000000) := by
  have h := checkLog_sound (w := (68131 / 331869)) (n := 12)
    (lo := (10412709 / 25000000)) (hi := (416508361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 131869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 131869) = 1/(131869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-416508361 / 1000000000) (-10412709 / 25000000) (Real.log (131869 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146739121 / 500000000) ≤ -Real.log (250000 / 335271) ∧
    -Real.log (250000 / 335271) ≤ (293478243 / 1000000000) := by
  have h := checkLog_sound (w := (85271 / 585271)) (n := 12)
    (lo := (146739121 / 500000000)) (hi := (293478243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335271 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335271 / 250000) = 1/(250000 / 335271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146739121 / 500000000) (293478243 / 1000000000) (Real.log (335271 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (335271 / 250000) = -Real.log (250000 / 335271) := by
    rw [show ((335271 / 250000) : ℝ) = ((250000 / 335271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (208579609 / 500000000) ≤ -Real.log (164729 / 250000) ∧
    -Real.log (164729 / 250000) ≤ (417159219 / 1000000000) := by
  have h := checkLog_sound (w := (85271 / 414729)) (n := 12)
    (lo := (208579609 / 500000000)) (hi := (417159219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164729) = 1/(164729 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-417159219 / 1000000000) (-208579609 / 500000000) (Real.log (164729 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222239943 / 1000000000) ≤ -Real.log (1000000 / 1248871) ∧
    -Real.log (1000000 / 1248871) ≤ (27779993 / 125000000) := by
  have h := checkLog_sound (w := (248871 / 2248871)) (n := 12)
    (lo := (222239943 / 1000000000)) (hi := (27779993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248871 / 1000000) = 1/(1000000 / 1248871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222239943 / 1000000000) (27779993 / 125000000) (Real.log (1248871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1248871 / 1000000) = -Real.log (1000000 / 1248871) := by
    rw [show ((1248871 / 1000000) : ℝ) = ((1000000 / 1248871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28617787 / 100000000) ≤ -Real.log (751129 / 1000000) ∧
    -Real.log (751129 / 1000000) ≤ (286177871 / 1000000000) := by
  have h := checkLog_sound (w := (248871 / 1751129)) (n := 12)
    (lo := (28617787 / 100000000)) (hi := (286177871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751129) = 1/(751129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-286177871 / 1000000000) (-28617787 / 100000000) (Real.log (751129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222508149 / 1000000000) ≤ -Real.log (500000 / 624603) ∧
    -Real.log (500000 / 624603) ≤ (4450163 / 20000000) := by
  have h := checkLog_sound (w := (124603 / 1124603)) (n := 12)
    (lo := (222508149 / 1000000000)) (hi := (4450163 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624603 / 500000) = 1/(500000 / 624603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222508149 / 1000000000) (4450163 / 20000000) (Real.log (624603 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (624603 / 500000) = -Real.log (500000 / 624603) := by
    rw [show ((624603 / 500000) : ℝ) = ((500000 / 624603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57324793 / 200000000) ≤ -Real.log (375397 / 500000) ∧
    -Real.log (375397 / 500000) ≤ (143311983 / 500000000) := by
  have h := checkLog_sound (w := (124603 / 875397)) (n := 12)
    (lo := (57324793 / 200000000)) (hi := (143311983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375397) = 1/(375397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-143311983 / 500000000) (-57324793 / 200000000) (Real.log (375397 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (35483333 / 50000000) ≤ -Real.log (50000000000 / 101665668201) ∧
    -Real.log (50000000000 / 101665668201) ≤ (354833331 / 500000000) := by
  have h := checkLog_sound (w := (1665668201 / 201665668201)) (n := 12)
    (lo := (412987 / 25000000)) (hi := (16519481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101665668201 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101665668201 / 100000000000) = 1/(50000000000 / 101665668201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (35483333 / 50000000) (354833331 / 500000000) (Real.log (101665668201 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (101665668201 / 50000000000) = -Real.log (50000000000 / 101665668201) := by
    rw [show ((101665668201 / 50000000000) : ℝ) = ((50000000000 / 101665668201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35531873 / 50000000) ≤ -Real.log (62500000000 / 127205516333) ∧
    -Real.log (62500000000 / 127205516333) ≤ (355318731 / 500000000) := by
  have h := checkLog_sound (w := (2205516333 / 252205516333)) (n := 12)
    (lo := (437257 / 25000000)) (hi := (17490281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127205516333 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127205516333 / 125000000000) = 1/(62500000000 / 127205516333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35531873 / 50000000) (355318731 / 500000000) (Real.log (127205516333 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (127205516333 / 62500000000) = -Real.log (62500000000 / 127205516333) := by
    rw [show ((127205516333 / 62500000000) : ℝ) = ((62500000000 / 127205516333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254208907 / 500000000) ≤ -Real.log (125000000000 / 207832309763) ∧
    -Real.log (125000000000 / 207832309763) ≤ (101683563 / 200000000) := by
  have h := checkLog_sound (w := (82832309763 / 332832309763)) (n := 12)
    (lo := (254208907 / 500000000)) (hi := (101683563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207832309763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207832309763 / 125000000000) = 1/(125000000000 / 207832309763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254208907 / 500000000) (101683563 / 200000000) (Real.log (207832309763 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (207832309763 / 125000000000) = -Real.log (125000000000 / 207832309763) := by
    rw [show ((207832309763 / 125000000000) : ℝ) = ((125000000000 / 207832309763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (101826423 / 200000000) ≤ -Real.log (100000000000 / 166384654113) ∧
    -Real.log (100000000000 / 166384654113) ≤ (127283029 / 250000000) := by
  have h := checkLog_sound (w := (66384654113 / 266384654113)) (n := 12)
    (lo := (101826423 / 200000000)) (hi := (127283029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166384654113 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166384654113 / 100000000000) = 1/(100000000000 / 166384654113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (101826423 / 200000000) (127283029 / 250000000) (Real.log (166384654113 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (166384654113 / 100000000000) = -Real.log (100000000000 / 166384654113) := by
    rw [show ((166384654113 / 100000000000) : ℝ) = ((100000000000 / 166384654113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0342
