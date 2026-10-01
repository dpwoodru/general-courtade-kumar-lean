import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell244
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

theorem reflection_log_1_neg : (331857811 / 1000000000) ≤ -Real.log (1024 / 1427) ∧
    -Real.log (1024 / 1427) ≤ (82964453 / 250000000) := by
  have h := checkLog_sound (w := (403 / 2451)) (n := 12)
    (lo := (331857811 / 1000000000)) (hi := (82964453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427 / 1024) = 1/(1024 / 1427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331857811 / 1000000000) (82964453 / 250000000) (Real.log (1427 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1427 / 1024) = -Real.log (1024 / 1427) := by
    rw [show ((1427 / 1024) : ℝ) = ((1024 / 1427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (500140723 / 1000000000) ≤ -Real.log (621 / 1024) ∧
    -Real.log (621 / 1024) ≤ (125035181 / 250000000) := by
  have h := checkLog_sound (w := (403 / 1645)) (n := 12)
    (lo := (500140723 / 1000000000)) (hi := (125035181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 621) = 1/(621 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125035181 / 250000000) (-500140723 / 1000000000) (Real.log (621 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16571863 / 50000000) ≤ -Real.log (1280 / 1783) ∧
    -Real.log (1280 / 1783) ≤ (331437261 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 3063)) (n := 12)
    (lo := (16571863 / 50000000)) (hi := (331437261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1783 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1783 / 1280) = 1/(1280 / 1783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16571863 / 50000000) (331437261 / 1000000000) (Real.log (1783 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1783 / 1280) = -Real.log (1280 / 1783) := by
    rw [show ((1783 / 1280) : ℝ) = ((1280 / 1783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249587503 / 500000000) ≤ -Real.log (777 / 1280) ∧
    -Real.log (777 / 1280) ≤ (499175007 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2057)) (n := 12)
    (lo := (249587503 / 500000000)) (hi := (499175007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 777) = 1/(777 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-499175007 / 1000000000) (-249587503 / 500000000) (Real.log (777 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (61672633 / 250000000) ≤ -Real.log (1000000 / 1279783) ∧
    -Real.log (1000000 / 1279783) ≤ (246690533 / 1000000000) := by
  have h := checkLog_sound (w := (279783 / 2279783)) (n := 12)
    (lo := (61672633 / 250000000)) (hi := (246690533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279783 / 1000000) = 1/(1000000 / 1279783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (61672633 / 250000000) (246690533 / 1000000000) (Real.log (1279783 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1279783 / 1000000) = -Real.log (1000000 / 1279783) := by
    rw [show ((1279783 / 1000000) : ℝ) = ((1000000 / 1279783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328202723 / 1000000000) ≤ -Real.log (720217 / 1000000) ∧
    -Real.log (720217 / 1000000) ≤ (82050681 / 250000000) := by
  have h := checkLog_sound (w := (279783 / 1720217)) (n := 12)
    (lo := (328202723 / 1000000000)) (hi := (82050681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720217) = 1/(720217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82050681 / 250000000) (-328202723 / 1000000000) (Real.log (720217 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (247021783 / 1000000000) ≤ -Real.log (1000000 / 1280207) ∧
    -Real.log (1000000 / 1280207) ≤ (30877723 / 125000000) := by
  have h := checkLog_sound (w := (280207 / 2280207)) (n := 12)
    (lo := (247021783 / 1000000000)) (hi := (30877723 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280207 / 1000000) = 1/(1000000 / 1280207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (247021783 / 1000000000) (30877723 / 125000000) (Real.log (1280207 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1280207 / 1000000) = -Real.log (1000000 / 1280207) := by
    rw [show ((1280207 / 1000000) : ℝ) = ((1000000 / 1280207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (41098951 / 125000000) ≤ -Real.log (719793 / 1000000) ∧
    -Real.log (719793 / 1000000) ≤ (328791609 / 1000000000) := by
  have h := checkLog_sound (w := (280207 / 1719793)) (n := 12)
    (lo := (41098951 / 125000000)) (hi := (328791609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 719793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 719793) = 1/(719793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-328791609 / 1000000000) (-41098951 / 125000000) (Real.log (719793 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (184169847 / 1000000000) ≤ -Real.log (50000 / 60111) ∧
    -Real.log (50000 / 60111) ≤ (23021231 / 125000000) := by
  have h := checkLog_sound (w := (10111 / 110111)) (n := 12)
    (lo := (184169847 / 1000000000)) (hi := (23021231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60111 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60111 / 50000) = 1/(50000 / 60111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (184169847 / 1000000000) (23021231 / 125000000) (Real.log (60111 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60111 / 50000) = -Real.log (50000 / 60111) := by
    rw [show ((60111 / 50000) : ℝ) = ((50000 / 60111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28240301 / 125000000) ≤ -Real.log (39889 / 50000) ∧
    -Real.log (39889 / 50000) ≤ (225922409 / 1000000000) := by
  have h := checkLog_sound (w := (10111 / 89889)) (n := 12)
    (lo := (28240301 / 125000000)) (hi := (225922409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39889) = 1/(39889 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225922409 / 1000000000) (-28240301 / 125000000) (Real.log (39889 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92218409 / 500000000) ≤ -Real.log (1000000 / 1202541) ∧
    -Real.log (1000000 / 1202541) ≤ (184436819 / 1000000000) := by
  have h := checkLog_sound (w := (202541 / 2202541)) (n := 12)
    (lo := (92218409 / 500000000)) (hi := (184436819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202541 / 1000000) = 1/(1000000 / 1202541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92218409 / 500000000) (184436819 / 1000000000) (Real.log (1202541 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1202541 / 1000000) = -Real.log (1000000 / 1202541) := by
    rw [show ((1202541 / 1000000) : ℝ) = ((1000000 / 1202541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28290607 / 125000000) ≤ -Real.log (797459 / 1000000) ∧
    -Real.log (797459 / 1000000) ≤ (226324857 / 1000000000) := by
  have h := checkLog_sound (w := (202541 / 1797459)) (n := 12)
    (lo := (28290607 / 125000000)) (hi := (226324857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797459) = 1/(797459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-226324857 / 1000000000) (-28290607 / 125000000) (Real.log (797459 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (415306133 / 500000000) ≤ -Real.log (500000000000 / 1147361647361) ∧
    -Real.log (500000000000 / 1147361647361) ≤ (207653067 / 250000000) := by
  have h := checkLog_sound (w := (147361647361 / 2147361647361)) (n := 12)
    (lo := (68732543 / 500000000)) (hi := (137465087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147361647361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147361647361 / 1000000000000) = 1/(500000000000 / 1147361647361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (415306133 / 500000000) (207653067 / 250000000) (Real.log (1147361647361 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1147361647361 / 500000000000) = -Real.log (500000000000 / 1147361647361) := by
    rw [show ((1147361647361 / 500000000000) : ℝ) = ((500000000000 / 1147361647361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (415999267 / 500000000) ≤ -Real.log (62500000000 / 143619162641) ∧
    -Real.log (62500000000 / 143619162641) ≤ (103999817 / 125000000) := by
  have h := checkLog_sound (w := (18619162641 / 268619162641)) (n := 12)
    (lo := (69425677 / 500000000)) (hi := (27770271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143619162641 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143619162641 / 125000000000) = 1/(62500000000 / 143619162641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (415999267 / 500000000) (103999817 / 125000000) (Real.log (143619162641 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (143619162641 / 62500000000) = -Real.log (62500000000 / 143619162641) := by
    rw [show ((143619162641 / 62500000000) : ℝ) = ((62500000000 / 143619162641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (114978651 / 200000000) ≤ -Real.log (500000000000 / 888470419331) ∧
    -Real.log (500000000000 / 888470419331) ≤ (71861657 / 125000000) := by
  have h := checkLog_sound (w := (388470419331 / 1388470419331)) (n := 12)
    (lo := (114978651 / 200000000)) (hi := (71861657 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((888470419331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(888470419331 / 500000000000) = 1/(500000000000 / 888470419331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114978651 / 200000000) (71861657 / 125000000) (Real.log (888470419331 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (888470419331 / 500000000000) = -Real.log (500000000000 / 888470419331) := by
    rw [show ((888470419331 / 500000000000) : ℝ) = ((500000000000 / 888470419331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (575813391 / 1000000000) ≤ -Real.log (250000000000 / 444644154639) ∧
    -Real.log (250000000000 / 444644154639) ≤ (35988337 / 62500000) := by
  have h := checkLog_sound (w := (194644154639 / 694644154639)) (n := 12)
    (lo := (575813391 / 1000000000)) (hi := (35988337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444644154639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444644154639 / 250000000000) = 1/(250000000000 / 444644154639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (575813391 / 1000000000) (35988337 / 62500000) (Real.log (444644154639 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (444644154639 / 250000000000) = -Real.log (250000000000 / 444644154639) := by
    rw [show ((444644154639 / 250000000000) : ℝ) = ((250000000000 / 444644154639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (12815383 / 31250000) ≤ -Real.log (500000000000 / 753478402567) ∧
    -Real.log (500000000000 / 753478402567) ≤ (410092257 / 1000000000) := by
  have h := checkLog_sound (w := (253478402567 / 1253478402567)) (n := 12)
    (lo := (12815383 / 31250000)) (hi := (410092257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753478402567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753478402567 / 500000000000) = 1/(500000000000 / 753478402567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (12815383 / 31250000) (410092257 / 1000000000) (Real.log (753478402567 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (753478402567 / 500000000000) = -Real.log (500000000000 / 753478402567) := by
    rw [show ((753478402567 / 500000000000) : ℝ) = ((500000000000 / 753478402567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (205380837 / 500000000) ≤ -Real.log (125000000000 / 188495740847) ∧
    -Real.log (125000000000 / 188495740847) ≤ (16430467 / 40000000) := by
  have h := checkLog_sound (w := (63495740847 / 313495740847)) (n := 12)
    (lo := (205380837 / 500000000)) (hi := (16430467 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188495740847 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188495740847 / 125000000000) = 1/(125000000000 / 188495740847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (205380837 / 500000000) (16430467 / 40000000) (Real.log (188495740847 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (188495740847 / 125000000000) = -Real.log (125000000000 / 188495740847) := by
    rw [show ((188495740847 / 125000000000) : ℝ) = ((125000000000 / 188495740847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20944019 / 500000000) ≤ -Real.log (958977143319 / 1000000000000) ∧
    -Real.log (958977143319 / 1000000000000) ≤ (41888039 / 1000000000) := by
  have h := checkLog_sound (w := (41022856681 / 1958977143319)) (n := 12)
    (lo := (20944019 / 500000000)) (hi := (41888039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958977143319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958977143319) = 1/(958977143319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41888039 / 1000000000) (-20944019 / 500000000) (Real.log (958977143319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41752561 / 1000000000) ≤ -Real.log (2397767679 / 2500000000) ∧
    -Real.log (2397767679 / 2500000000) ≤ (20876281 / 500000000) := by
  have h := checkLog_sound (w := (102232321 / 4897767679)) (n := 12)
    (lo := (41752561 / 1000000000)) (hi := (20876281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2397767679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2397767679) = 1/(2397767679 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20876281 / 500000000) (-41752561 / 1000000000) (Real.log (2397767679 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell244
