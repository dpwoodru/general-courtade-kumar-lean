import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0182
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

theorem reflection_log_1_neg : (38927629 / 62500000) ≤ -Real.log (6400 / 11931) ∧
    -Real.log (6400 / 11931) ≤ (124568413 / 200000000) := by
  have h := checkLog_sound (w := (5531 / 18331)) (n := 12)
    (lo := (38927629 / 62500000)) (hi := (124568413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 6400) = 1/(6400 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (38927629 / 62500000) (124568413 / 200000000) (Real.log (11931 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11931 / 6400) = -Real.log (6400 / 11931) := by
    rw [show ((11931 / 6400) : ℝ) = ((6400 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (998355071 / 500000000) ≤ -Real.log (869 / 6400) ∧
    -Real.log (869 / 6400) ≤ (399342029 / 200000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 869) = 1/(869 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-399342029 / 200000000) (-998355071 / 500000000) (Real.log (869 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (124249661 / 200000000) ≤ -Real.log (800 / 1489) ∧
    -Real.log (800 / 1489) ≤ (310624153 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2289)) (n := 12)
    (lo := (124249661 / 200000000)) (hi := (310624153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 800) = 1/(800 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (124249661 / 200000000) (310624153 / 500000000) (Real.log (1489 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1489 / 800) = -Real.log (800 / 1489) := by
    rw [show ((1489 / 800) : ℝ) = ((800 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79003261 / 40000000) ≤ -Real.log (111 / 800) ∧
    -Real.log (111 / 800) ≤ (246885191 / 125000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 111) = 1/(111 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-246885191 / 125000000) (-79003261 / 40000000) (Real.log (111 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (547217821 / 1000000000) ≤ -Real.log (3200 / 5531) ∧
    -Real.log (3200 / 5531) ≤ (273608911 / 500000000) := by
  have h := checkLog_sound (w := (2331 / 8731)) (n := 12)
    (lo := (547217821 / 1000000000)) (hi := (273608911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5531 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5531 / 3200) = 1/(3200 / 5531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (547217821 / 1000000000) (273608911 / 500000000) (Real.log (5531 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5531 / 3200) = -Real.log (3200 / 5531) := by
    rw [show ((5531 / 3200) : ℝ) = ((3200 / 5531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (651781481 / 500000000) ≤ -Real.log (869 / 3200) ∧
    -Real.log (869 / 3200) ≤ (325890741 / 250000000) := by
  have h := checkLog_sound (w := (731 / 2469)) (n := 12)
    (lo := (305207891 / 500000000)) (hi := (610415783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 869) = 1/(869 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-325890741 / 250000000) (-651781481 / 500000000) (Real.log (869 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (543776723 / 1000000000) ≤ -Real.log (400 / 689) ∧
    -Real.log (400 / 689) ≤ (135944181 / 250000000) := by
  have h := checkLog_sound (w := (289 / 1089)) (n := 12)
    (lo := (543776723 / 1000000000)) (hi := (135944181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 400) = 1/(400 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (543776723 / 1000000000) (135944181 / 250000000) (Real.log (689 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (689 / 400) = -Real.log (400 / 689) := by
    rw [show ((689 / 400) : ℝ) = ((400 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256386869 / 200000000) ≤ -Real.log (111 / 400) ∧
    -Real.log (111 / 400) ≤ (1281934347 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 111) = 1/(111 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1281934347 / 1000000000) (-256386869 / 200000000) (Real.log (111 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (320419317 / 500000000) ≤ -Real.log (125000 / 237259) ∧
    -Real.log (125000 / 237259) ≤ (128167727 / 200000000) := by
  have h := checkLog_sound (w := (112259 / 362259)) (n := 12)
    (lo := (320419317 / 500000000)) (hi := (128167727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237259 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237259 / 125000) = 1/(125000 / 237259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (320419317 / 500000000) (128167727 / 200000000) (Real.log (237259 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (237259 / 125000) = -Real.log (125000 / 237259) := by
    rw [show ((237259 / 125000) : ℝ) = ((125000 / 237259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (456697719 / 200000000) ≤ -Real.log (12741 / 125000) ∧
    -Real.log (12741 / 125000) ≤ (2283488599 / 1000000000) := by
  have h := checkLog_sound (w := (1442 / 14183)) (n := 12)
    (lo := (40809411 / 200000000)) (hi := (12752941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 12741) = 1/(12741 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2283488599 / 1000000000) (-456697719 / 200000000) (Real.log (12741 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (320909311 / 500000000) ≤ -Real.log (1000000 / 1899933) ∧
    -Real.log (1000000 / 1899933) ≤ (641818623 / 1000000000) := by
  have h := checkLog_sound (w := (899933 / 2899933)) (n := 12)
    (lo := (320909311 / 500000000)) (hi := (641818623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899933 / 1000000) = 1/(1000000 / 1899933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (320909311 / 500000000) (641818623 / 1000000000) (Real.log (1899933 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1899933 / 1000000) = -Real.log (1000000 / 1899933) := by
    rw [show ((1899933 / 1000000) : ℝ) = ((1000000 / 1899933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (460383063 / 200000000) ≤ -Real.log (100067 / 1000000) ∧
    -Real.log (100067 / 1000000) ≤ (2301915319 / 1000000000) := by
  have h := checkLog_sound (w := (24933 / 225067)) (n := 12)
    (lo := (8898951 / 40000000)) (hi := (13904611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100067) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 100067) = 1/(100067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2301915319 / 1000000000) (-460383063 / 200000000) (Real.log (100067 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (159534907 / 250000000) ≤ -Real.log (250000 / 473239) ∧
    -Real.log (250000 / 473239) ≤ (638139629 / 1000000000) := by
  have h := checkLog_sound (w := (223239 / 723239)) (n := 12)
    (lo := (159534907 / 250000000)) (hi := (638139629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473239 / 250000) = 1/(250000 / 473239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (159534907 / 250000000) (638139629 / 1000000000) (Real.log (473239 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (473239 / 250000) = -Real.log (250000 / 473239) := by
    rw [show ((473239 / 250000) : ℝ) = ((250000 / 473239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139657207 / 62500000) ≤ -Real.log (26761 / 250000) ∧
    -Real.log (26761 / 250000) ≤ (558628829 / 250000000) := by
  have h := checkLog_sound (w := (4489 / 58011)) (n := 12)
    (lo := (38768443 / 250000000)) (hi := (155073773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26761) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 26761) = 1/(26761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-558628829 / 250000000) (-139657207 / 62500000) (Real.log (26761 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7990717 / 12500000) ≤ -Real.log (1000000 / 1895073) ∧
    -Real.log (1000000 / 1895073) ≤ (639257361 / 1000000000) := by
  have h := checkLog_sound (w := (895073 / 2895073)) (n := 12)
    (lo := (7990717 / 12500000)) (hi := (639257361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1895073 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1895073 / 1000000) = 1/(1000000 / 1895073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7990717 / 12500000) (639257361 / 1000000000) (Real.log (1895073 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1895073 / 1000000) = -Real.log (1000000 / 1895073) := by
    rw [show ((1895073 / 1000000) : ℝ) = ((1000000 / 1895073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2254490407 / 1000000000) ≤ -Real.log (104927 / 1000000) ∧
    -Real.log (104927 / 1000000) ≤ (2254490411 / 1000000000) := by
  have h := checkLog_sound (w := (20073 / 229927)) (n := 12)
    (lo := (175048867 / 1000000000)) (hi := (43762217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104927) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 104927) = 1/(104927 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2254490411 / 1000000000) (-2254490407 / 1000000000) (Real.log (104927 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2924327229 / 1000000000) ≤ -Real.log (250000000000 / 4655423436151) ∧
    -Real.log (250000000000 / 4655423436151) ≤ (1462163617 / 500000000) := by
  have h := checkLog_sound (w := (655423436151 / 8655423436151)) (n := 12)
    (lo := (151738509 / 1000000000)) (hi := (15173851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4655423436151 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4655423436151 / 4000000000000) = 1/(250000000000 / 4655423436151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2924327229 / 1000000000) (1462163617 / 500000000) (Real.log (4655423436151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4655423436151 / 250000000000) = -Real.log (250000000000 / 4655423436151) := by
    rw [show ((4655423436151 / 250000000000) : ℝ) = ((250000000000 / 4655423436151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2943733937 / 1000000000) ≤ -Real.log (100000000000 / 1898660897199) ∧
    -Real.log (100000000000 / 1898660897199) ≤ (1471866971 / 500000000) := by
  have h := checkLog_sound (w := (298660897199 / 3498660897199)) (n := 12)
    (lo := (171145217 / 1000000000)) (hi := (85572609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1898660897199 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1898660897199 / 1600000000000) = 1/(100000000000 / 1898660897199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2943733937 / 1000000000) (1471866971 / 500000000) (Real.log (1898660897199 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1898660897199 / 100000000000) = -Real.log (100000000000 / 1898660897199) := by
    rw [show ((1898660897199 / 100000000000) : ℝ) = ((100000000000 / 1898660897199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (143632747 / 50000000) ≤ -Real.log (250000000000 / 4420976420911) ∧
    -Real.log (250000000000 / 4420976420911) ≤ (574530989 / 200000000) := by
  have h := checkLog_sound (w := (420976420911 / 8420976420911)) (n := 12)
    (lo := (5003311 / 50000000)) (hi := (100066221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4420976420911 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4420976420911 / 4000000000000) = 1/(250000000000 / 4420976420911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (143632747 / 50000000) (574530989 / 200000000) (Real.log (4420976420911 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4420976420911 / 250000000000) = -Real.log (250000000000 / 4420976420911) := by
    rw [show ((4420976420911 / 250000000000) : ℝ) = ((250000000000 / 4420976420911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1446873883 / 500000000) ≤ -Real.log (125000000000 / 2257608861399) ∧
    -Real.log (125000000000 / 2257608861399) ≤ (2893747771 / 1000000000) := by
  have h := checkLog_sound (w := (257608861399 / 4257608861399)) (n := 12)
    (lo := (60579523 / 500000000)) (hi := (121159047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257608861399 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2257608861399 / 2000000000000) = 1/(125000000000 / 2257608861399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1446873883 / 500000000) (2893747771 / 1000000000) (Real.log (2257608861399 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2257608861399 / 125000000000) = -Real.log (125000000000 / 2257608861399) := by
    rw [show ((2257608861399 / 125000000000) : ℝ) = ((125000000000 / 2257608861399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0182
