import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell237
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

theorem reflection_log_1_neg : (164455117 / 500000000) ≤ -Real.log (2560 / 3557) ∧
    -Real.log (2560 / 3557) ≤ (65782047 / 200000000) := by
  have h := checkLog_sound (w := (997 / 6117)) (n := 12)
    (lo := (164455117 / 500000000)) (hi := (65782047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3557 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3557 / 2560) = 1/(2560 / 3557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164455117 / 500000000) (65782047 / 200000000) (Real.log (3557 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3557 / 2560) = -Real.log (2560 / 3557) := by
    rw [show ((3557 / 2560) : ℝ) = ((2560 / 3557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (493400207 / 1000000000) ≤ -Real.log (1563 / 2560) ∧
    -Real.log (1563 / 2560) ≤ (30837513 / 62500000) := by
  have h := checkLog_sound (w := (997 / 4123)) (n := 12)
    (lo := (493400207 / 1000000000)) (hi := (30837513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1563) = 1/(1563 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30837513 / 62500000) (-493400207 / 1000000000) (Real.log (1563 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (328488441 / 1000000000) ≤ -Real.log (5120 / 7111) ∧
    -Real.log (5120 / 7111) ≤ (164244221 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 12231)) (n := 12)
    (lo := (328488441 / 1000000000)) (hi := (164244221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7111 / 5120) = 1/(5120 / 7111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (328488441 / 1000000000) (164244221 / 500000000) (Real.log (7111 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7111 / 5120) = -Real.log (5120 / 7111) := by
    rw [show ((7111 / 5120) : ℝ) = ((5120 / 7111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246220487 / 500000000) ≤ -Real.log (3129 / 5120) ∧
    -Real.log (3129 / 5120) ≤ (19697639 / 40000000) := by
  have h := checkLog_sound (w := (1991 / 8249)) (n := 12)
    (lo := (246220487 / 500000000)) (hi := (19697639 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3129) = 1/(3129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-19697639 / 40000000) (-246220487 / 500000000) (Real.log (3129 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122186697 / 500000000) ≤ -Real.log (1000000 / 1276821) ∧
    -Real.log (1000000 / 1276821) ≤ (48874679 / 200000000) := by
  have h := checkLog_sound (w := (276821 / 2276821)) (n := 12)
    (lo := (122186697 / 500000000)) (hi := (48874679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276821 / 1000000) = 1/(1000000 / 1276821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122186697 / 500000000) (48874679 / 200000000) (Real.log (1276821 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1276821 / 1000000) = -Real.log (1000000 / 1276821) := by
    rw [show ((1276821 / 1000000) : ℝ) = ((1000000 / 1276821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (324098507 / 1000000000) ≤ -Real.log (723179 / 1000000) ∧
    -Real.log (723179 / 1000000) ≤ (81024627 / 250000000) := by
  have h := checkLog_sound (w := (276821 / 1723179)) (n := 12)
    (lo := (324098507 / 1000000000)) (hi := (81024627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723179) = 1/(723179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-81024627 / 250000000) (-324098507 / 1000000000) (Real.log (723179 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122352707 / 500000000) ≤ -Real.log (200000 / 255449) ∧
    -Real.log (200000 / 255449) ≤ (48941083 / 200000000) := by
  have h := checkLog_sound (w := (55449 / 455449)) (n := 12)
    (lo := (122352707 / 500000000)) (hi := (48941083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255449 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(255449 / 200000) = 1/(200000 / 255449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122352707 / 500000000) (48941083 / 200000000) (Real.log (255449 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (255449 / 200000) = -Real.log (200000 / 255449) := by
    rw [show ((255449 / 200000) : ℝ) = ((200000 / 255449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16234249 / 50000000) ≤ -Real.log (144551 / 200000) ∧
    -Real.log (144551 / 200000) ≤ (324684981 / 1000000000) := by
  have h := checkLog_sound (w := (55449 / 344551)) (n := 12)
    (lo := (16234249 / 50000000)) (hi := (324684981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 144551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 144551) = 1/(144551 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-324684981 / 1000000000) (-16234249 / 50000000) (Real.log (144551 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18230989 / 100000000) ≤ -Real.log (500000 / 599993) ∧
    -Real.log (500000 / 599993) ≤ (182309891 / 1000000000) := by
  have h := checkLog_sound (w := (99993 / 1099993)) (n := 12)
    (lo := (18230989 / 100000000)) (hi := (182309891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599993 / 500000) = 1/(500000 / 599993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18230989 / 100000000) (182309891 / 1000000000) (Real.log (599993 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (599993 / 500000) = -Real.log (500000 / 599993) := by
    rw [show ((599993 / 500000) : ℝ) = ((500000 / 599993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (223126051 / 1000000000) ≤ -Real.log (400007 / 500000) ∧
    -Real.log (400007 / 500000) ≤ (55781513 / 250000000) := by
  have h := checkLog_sound (w := (99993 / 900007)) (n := 12)
    (lo := (223126051 / 1000000000)) (hi := (55781513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400007) = 1/(400007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55781513 / 250000000) (-223126051 / 1000000000) (Real.log (400007 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45644131 / 250000000) ≤ -Real.log (500000 / 600153) ∧
    -Real.log (500000 / 600153) ≤ (7303061 / 40000000) := by
  have h := checkLog_sound (w := (100153 / 1100153)) (n := 12)
    (lo := (45644131 / 250000000)) (hi := (7303061 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600153 / 500000) = 1/(500000 / 600153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45644131 / 250000000) (7303061 / 40000000) (Real.log (600153 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600153 / 500000) = -Real.log (500000 / 600153) := by
    rw [show ((600153 / 500000) : ℝ) = ((500000 / 600153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55881531 / 250000000) ≤ -Real.log (399847 / 500000) ∧
    -Real.log (399847 / 500000) ≤ (1788209 / 8000000) := by
  have h := checkLog_sound (w := (100153 / 899847)) (n := 12)
    (lo := (55881531 / 250000000)) (hi := (1788209 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399847) = 1/(399847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1788209 / 8000000) (-55881531 / 250000000) (Real.log (399847 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (164185883 / 200000000) ≤ -Real.log (250000000000 / 568152764461) ∧
    -Real.log (250000000000 / 568152764461) ≤ (820929417 / 1000000000) := by
  have h := checkLog_sound (w := (68152764461 / 1068152764461)) (n := 12)
    (lo := (25556447 / 200000000)) (hi := (31945559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568152764461 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568152764461 / 500000000000) = 1/(250000000000 / 568152764461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (164185883 / 200000000) (820929417 / 1000000000) (Real.log (568152764461 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (568152764461 / 250000000000) = -Real.log (250000000000 / 568152764461) := by
    rw [show ((568152764461 / 250000000000) : ℝ) = ((250000000000 / 568152764461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20557761 / 25000000) ≤ -Real.log (500000000000 / 1137875879719) ∧
    -Real.log (500000000000 / 1137875879719) ≤ (411155221 / 500000000) := by
  have h := checkLog_sound (w := (137875879719 / 2137875879719)) (n := 12)
    (lo := (6458163 / 50000000)) (hi := (129163261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137875879719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1137875879719 / 1000000000000) = 1/(500000000000 / 1137875879719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (20557761 / 25000000) (411155221 / 500000000) (Real.log (1137875879719 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1137875879719 / 500000000000) = -Real.log (500000000000 / 1137875879719) := by
    rw [show ((1137875879719 / 500000000000) : ℝ) = ((500000000000 / 1137875879719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (284235951 / 500000000) ≤ -Real.log (500000000000 / 882783515561) ∧
    -Real.log (500000000000 / 882783515561) ≤ (568471903 / 1000000000) := by
  have h := checkLog_sound (w := (382783515561 / 1382783515561)) (n := 12)
    (lo := (284235951 / 500000000)) (hi := (568471903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((882783515561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(882783515561 / 500000000000) = 1/(500000000000 / 882783515561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (284235951 / 500000000) (568471903 / 1000000000) (Real.log (882783515561 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (882783515561 / 500000000000) = -Real.log (500000000000 / 882783515561) := by
    rw [show ((882783515561 / 500000000000) : ℝ) = ((500000000000 / 882783515561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (284695197 / 500000000) ≤ -Real.log (125000000000 / 220898679359) ∧
    -Real.log (125000000000 / 220898679359) ≤ (113878079 / 200000000) := by
  have h := checkLog_sound (w := (95898679359 / 345898679359)) (n := 12)
    (lo := (284695197 / 500000000)) (hi := (113878079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220898679359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220898679359 / 125000000000) = 1/(125000000000 / 220898679359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (284695197 / 500000000) (113878079 / 200000000) (Real.log (220898679359 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (220898679359 / 125000000000) = -Real.log (125000000000 / 220898679359) := by
    rw [show ((220898679359 / 125000000000) : ℝ) = ((125000000000 / 220898679359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (405435941 / 1000000000) ≤ -Real.log (250000000000 / 374989062691) ∧
    -Real.log (250000000000 / 374989062691) ≤ (202717971 / 500000000) := by
  have h := checkLog_sound (w := (124989062691 / 624989062691)) (n := 12)
    (lo := (405435941 / 1000000000)) (hi := (202717971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374989062691 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374989062691 / 250000000000) = 1/(250000000000 / 374989062691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (405435941 / 1000000000) (202717971 / 500000000) (Real.log (374989062691 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (374989062691 / 250000000000) = -Real.log (250000000000 / 374989062691) := by
    rw [show ((374989062691 / 250000000000) : ℝ) = ((250000000000 / 374989062691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (50762831 / 125000000) ≤ -Real.log (500000000000 / 750478307953) ∧
    -Real.log (500000000000 / 750478307953) ≤ (406102649 / 1000000000) := by
  have h := checkLog_sound (w := (250478307953 / 1250478307953)) (n := 12)
    (lo := (50762831 / 125000000)) (hi := (406102649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750478307953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750478307953 / 500000000000) = 1/(500000000000 / 750478307953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (50762831 / 125000000) (406102649 / 1000000000) (Real.log (750478307953 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (750478307953 / 500000000000) = -Real.log (500000000000 / 750478307953) := by
    rw [show ((750478307953 / 500000000000) : ℝ) = ((500000000000 / 750478307953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (51187 / 1250000) ≤ -Real.log (239969376591 / 250000000000) ∧
    -Real.log (239969376591 / 250000000000) ≤ (40949601 / 1000000000) := by
  have h := checkLog_sound (w := (10030623409 / 489969376591)) (n := 12)
    (lo := (51187 / 1250000)) (hi := (40949601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239969376591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239969376591) = 1/(239969376591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40949601 / 1000000000) (-51187 / 1250000) (Real.log (239969376591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40816161 / 1000000000) ≤ -Real.log (240001399951 / 250000000000) ∧
    -Real.log (240001399951 / 250000000000) ≤ (20408081 / 500000000) := by
  have h := checkLog_sound (w := (9998600049 / 490001399951)) (n := 12)
    (lo := (40816161 / 1000000000)) (hi := (20408081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240001399951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240001399951) = 1/(240001399951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20408081 / 500000000) (-40816161 / 1000000000) (Real.log (240001399951 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell237
