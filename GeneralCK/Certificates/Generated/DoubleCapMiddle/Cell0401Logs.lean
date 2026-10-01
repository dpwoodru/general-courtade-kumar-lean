import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0401
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

theorem reflection_log_1_neg : (199986867 / 1000000000) ≤ -Real.log (10240 / 12507) ∧
    -Real.log (10240 / 12507) ≤ (49996717 / 250000000) := by
  have h := checkLog_sound (w := (2267 / 22747)) (n := 12)
    (lo := (199986867 / 1000000000)) (hi := (49996717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 10240) = 1/(10240 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199986867 / 1000000000) (49996717 / 250000000) (Real.log (12507 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12507 / 10240) = -Real.log (10240 / 12507) := by
    rw [show ((12507 / 10240) : ℝ) = ((10240 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (125120393 / 500000000) ≤ -Real.log (7973 / 10240) ∧
    -Real.log (7973 / 10240) ≤ (250240787 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 18213)) (n := 12)
    (lo := (125120393 / 500000000)) (hi := (250240787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7973) = 1/(7973 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-250240787 / 1000000000) (-125120393 / 500000000) (Real.log (7973 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199746973 / 1000000000) ≤ -Real.log (1280 / 1563) ∧
    -Real.log (1280 / 1563) ≤ (99873487 / 500000000) := by
  have h := checkLog_sound (w := (283 / 2843)) (n := 12)
    (lo := (199746973 / 1000000000)) (hi := (99873487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1280) = 1/(1280 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199746973 / 1000000000) (99873487 / 500000000) (Real.log (1563 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1563 / 1280) = -Real.log (1280 / 1563) := by
    rw [show ((1563 / 1280) : ℝ) = ((1280 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (124932293 / 500000000) ≤ -Real.log (997 / 1280) ∧
    -Real.log (997 / 1280) ≤ (249864587 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2277)) (n := 12)
    (lo := (124932293 / 500000000)) (hi := (249864587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 997) = 1/(997 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249864587 / 1000000000) (-124932293 / 500000000) (Real.log (997 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (366567259 / 1000000000) ≤ -Real.log (5120 / 7387) ∧
    -Real.log (5120 / 7387) ≤ (18328363 / 50000000) := by
  have h := checkLog_sound (w := (2267 / 12507)) (n := 12)
    (lo := (366567259 / 1000000000)) (hi := (18328363 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7387 / 5120) = 1/(5120 / 7387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (366567259 / 1000000000) (18328363 / 50000000) (Real.log (7387 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7387 / 5120) = -Real.log (5120 / 7387) := by
    rw [show ((7387 / 5120) : ℝ) = ((5120 / 7387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (292391683 / 500000000) ≤ -Real.log (2853 / 5120) ∧
    -Real.log (2853 / 5120) ≤ (584783367 / 1000000000) := by
  have h := checkLog_sound (w := (2267 / 7973)) (n := 12)
    (lo := (292391683 / 500000000)) (hi := (584783367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2853) = 1/(2853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-584783367 / 1000000000) (-292391683 / 500000000) (Real.log (2853 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183080529 / 500000000) ≤ -Real.log (640 / 923) ∧
    -Real.log (640 / 923) ≤ (366161059 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1563)) (n := 12)
    (lo := (183080529 / 500000000)) (hi := (366161059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923 / 640) = 1/(640 / 923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183080529 / 500000000) (366161059 / 1000000000) (Real.log (923 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (923 / 640) = -Real.log (640 / 923) := by
    rw [show ((923 / 640) : ℝ) = ((640 / 923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (291866197 / 500000000) ≤ -Real.log (357 / 640) ∧
    -Real.log (357 / 640) ≤ (116746479 / 200000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 357) = 1/(357 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-116746479 / 200000000) (-291866197 / 500000000) (Real.log (357 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68545083 / 250000000) ≤ -Real.log (250000 / 328863) ∧
    -Real.log (250000 / 328863) ≤ (274180333 / 1000000000) := by
  have h := checkLog_sound (w := (78863 / 578863)) (n := 12)
    (lo := (68545083 / 250000000)) (hi := (274180333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328863 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328863 / 250000) = 1/(250000 / 328863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68545083 / 250000000) (274180333 / 1000000000) (Real.log (328863 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (328863 / 250000) = -Real.log (250000 / 328863) := by
    rw [show ((328863 / 250000) : ℝ) = ((250000 / 328863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11843641 / 31250000) ≤ -Real.log (171137 / 250000) ∧
    -Real.log (171137 / 250000) ≤ (378996513 / 1000000000) := by
  have h := checkLog_sound (w := (78863 / 421137)) (n := 12)
    (lo := (11843641 / 31250000)) (hi := (378996513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171137) = 1/(171137 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-378996513 / 1000000000) (-11843641 / 31250000) (Real.log (171137 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (274504883 / 1000000000) ≤ -Real.log (1000000 / 1315879) ∧
    -Real.log (1000000 / 1315879) ≤ (68626221 / 250000000) := by
  have h := checkLog_sound (w := (315879 / 2315879)) (n := 12)
    (lo := (274504883 / 1000000000)) (hi := (68626221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315879 / 1000000) = 1/(1000000 / 1315879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (274504883 / 1000000000) (68626221 / 250000000) (Real.log (1315879 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315879 / 1000000) = -Real.log (1000000 / 1315879) := by
    rw [show ((1315879 / 1000000) : ℝ) = ((1000000 / 1315879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94905119 / 250000000) ≤ -Real.log (684121 / 1000000) ∧
    -Real.log (684121 / 1000000) ≤ (379620477 / 1000000000) := by
  have h := checkLog_sound (w := (315879 / 1684121)) (n := 12)
    (lo := (94905119 / 250000000)) (hi := (379620477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684121) = 1/(684121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-379620477 / 1000000000) (-94905119 / 250000000) (Real.log (684121 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (206506723 / 1000000000) ≤ -Real.log (15625 / 19209) ∧
    -Real.log (15625 / 19209) ≤ (51626681 / 250000000) := by
  have h := checkLog_sound (w := (1792 / 17417)) (n := 12)
    (lo := (206506723 / 1000000000)) (hi := (51626681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19209 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19209 / 15625) = 1/(15625 / 19209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (206506723 / 1000000000) (51626681 / 250000000) (Real.log (19209 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19209 / 15625) = -Real.log (15625 / 19209) := by
    rw [show ((19209 / 15625) : ℝ) = ((15625 / 19209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130277351 / 500000000) ≤ -Real.log (12041 / 15625) ∧
    -Real.log (12041 / 15625) ≤ (260554703 / 1000000000) := by
  have h := checkLog_sound (w := (1792 / 13833)) (n := 12)
    (lo := (130277351 / 500000000)) (hi := (260554703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12041) = 1/(12041 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260554703 / 1000000000) (-130277351 / 500000000) (Real.log (12041 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206774303 / 1000000000) ≤ -Real.log (200000 / 245941) ∧
    -Real.log (200000 / 245941) ≤ (6461697 / 31250000) := by
  have h := checkLog_sound (w := (45941 / 445941)) (n := 12)
    (lo := (206774303 / 1000000000)) (hi := (6461697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245941 / 200000) = 1/(200000 / 245941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206774303 / 1000000000) (6461697 / 31250000) (Real.log (245941 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (245941 / 200000) = -Real.log (200000 / 245941) := by
    rw [show ((245941 / 200000) : ℝ) = ((200000 / 245941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6524543 / 25000000) ≤ -Real.log (154059 / 200000) ∧
    -Real.log (154059 / 200000) ≤ (260981721 / 1000000000) := by
  have h := checkLog_sound (w := (45941 / 354059)) (n := 12)
    (lo := (6524543 / 25000000)) (hi := (260981721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154059) = 1/(154059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260981721 / 1000000000) (-6524543 / 25000000) (Real.log (154059 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (130635369 / 200000000) ≤ -Real.log (500000000000 / 960817941181) ∧
    -Real.log (500000000000 / 960817941181) ≤ (326588423 / 500000000) := by
  have h := checkLog_sound (w := (460817941181 / 1460817941181)) (n := 12)
    (lo := (130635369 / 200000000)) (hi := (326588423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960817941181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960817941181 / 500000000000) = 1/(500000000000 / 960817941181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (130635369 / 200000000) (326588423 / 500000000) (Real.log (960817941181 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (960817941181 / 500000000000) = -Real.log (500000000000 / 960817941181) := by
    rw [show ((960817941181 / 500000000000) : ℝ) = ((500000000000 / 960817941181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (654125359 / 1000000000) ≤ -Real.log (500000000000 / 961729723251) ∧
    -Real.log (500000000000 / 961729723251) ≤ (8176567 / 12500000) := by
  have h := checkLog_sound (w := (461729723251 / 1461729723251)) (n := 12)
    (lo := (654125359 / 1000000000)) (hi := (8176567 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961729723251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961729723251 / 500000000000) = 1/(500000000000 / 961729723251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (654125359 / 1000000000) (8176567 / 12500000) (Real.log (961729723251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (961729723251 / 500000000000) = -Real.log (500000000000 / 961729723251) := by
    rw [show ((961729723251 / 500000000000) : ℝ) = ((500000000000 / 961729723251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (233530713 / 500000000) ≤ -Real.log (500000000000 / 797649696869) ∧
    -Real.log (500000000000 / 797649696869) ≤ (467061427 / 1000000000) := by
  have h := checkLog_sound (w := (297649696869 / 1297649696869)) (n := 12)
    (lo := (233530713 / 500000000)) (hi := (467061427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797649696869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797649696869 / 500000000000) = 1/(500000000000 / 797649696869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (233530713 / 500000000) (467061427 / 1000000000) (Real.log (797649696869 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (797649696869 / 500000000000) = -Real.log (500000000000 / 797649696869) := by
    rw [show ((797649696869 / 500000000000) : ℝ) = ((500000000000 / 797649696869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (467756023 / 1000000000) ≤ -Real.log (500000000000 / 798203934857) ∧
    -Real.log (500000000000 / 798203934857) ≤ (58469503 / 125000000) := by
  have h := checkLog_sound (w := (298203934857 / 1298203934857)) (n := 12)
    (lo := (467756023 / 1000000000)) (hi := (58469503 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798203934857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798203934857 / 500000000000) = 1/(500000000000 / 798203934857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (467756023 / 1000000000) (58469503 / 125000000) (Real.log (798203934857 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (798203934857 / 500000000000) = -Real.log (500000000000 / 798203934857) := by
    rw [show ((798203934857 / 500000000000) : ℝ) = ((500000000000 / 798203934857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0401
