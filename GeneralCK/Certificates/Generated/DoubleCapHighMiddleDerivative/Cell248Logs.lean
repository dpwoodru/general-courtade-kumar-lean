import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell248
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

theorem reflection_log_1_neg : (333538249 / 1000000000) ≤ -Real.log (5120 / 7147) ∧
    -Real.log (5120 / 7147) ≤ (1334153 / 4000000) := by
  have h := checkLog_sound (w := (2027 / 12267)) (n := 12)
    (lo := (333538249 / 1000000000)) (hi := (1334153 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7147 / 5120) = 1/(5120 / 7147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (333538249 / 1000000000) (1334153 / 4000000) (Real.log (7147 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7147 / 5120) = -Real.log (5120 / 7147) := by
    rw [show ((7147 / 5120) : ℝ) = ((5120 / 7147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (100802589 / 200000000) ≤ -Real.log (3093 / 5120) ∧
    -Real.log (3093 / 5120) ≤ (252006473 / 500000000) := by
  have h := checkLog_sound (w := (2027 / 8213)) (n := 12)
    (lo := (100802589 / 200000000)) (hi := (252006473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3093) = 1/(3093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252006473 / 500000000) (-100802589 / 200000000) (Real.log (3093 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83279601 / 250000000) ≤ -Real.log (640 / 893) ∧
    -Real.log (640 / 893) ≤ (66623681 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1533)) (n := 12)
    (lo := (83279601 / 250000000)) (hi := (66623681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893 / 640) = 1/(640 / 893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83279601 / 250000000) (66623681 / 200000000) (Real.log (893 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (893 / 640) = -Real.log (640 / 893) := by
    rw [show ((893 / 640) : ℝ) = ((640 / 893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (503043483 / 1000000000) ≤ -Real.log (387 / 640) ∧
    -Real.log (387 / 640) ≤ (125760871 / 250000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 387) = 1/(387 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-125760871 / 250000000) (-503043483 / 1000000000) (Real.log (387 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124006269 / 500000000) ≤ -Real.log (250000 / 320369) ∧
    -Real.log (250000 / 320369) ≤ (248012539 / 1000000000) := by
  have h := checkLog_sound (w := (70369 / 570369)) (n := 12)
    (lo := (124006269 / 500000000)) (hi := (248012539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320369 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320369 / 250000) = 1/(250000 / 320369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124006269 / 500000000) (248012539 / 1000000000) (Real.log (320369 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (320369 / 250000) = -Real.log (250000 / 320369) := by
    rw [show ((320369 / 250000) : ℝ) = ((250000 / 320369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (330556171 / 1000000000) ≤ -Real.log (179631 / 250000) ∧
    -Real.log (179631 / 250000) ≤ (82639043 / 250000000) := by
  have h := checkLog_sound (w := (70369 / 429631)) (n := 12)
    (lo := (330556171 / 1000000000)) (hi := (82639043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179631) = 1/(179631 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82639043 / 250000000) (-330556171 / 1000000000) (Real.log (179631 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62086033 / 250000000) ≤ -Real.log (1000000 / 1281901) ∧
    -Real.log (1000000 / 1281901) ≤ (248344133 / 1000000000) := by
  have h := checkLog_sound (w := (281901 / 2281901)) (n := 12)
    (lo := (62086033 / 250000000)) (hi := (248344133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281901 / 1000000) = 1/(1000000 / 1281901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62086033 / 250000000) (248344133 / 1000000000) (Real.log (1281901 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1281901 / 1000000) = -Real.log (1000000 / 1281901) := by
    rw [show ((1281901 / 1000000) : ℝ) = ((1000000 / 1281901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82786959 / 250000000) ≤ -Real.log (718099 / 1000000) ∧
    -Real.log (718099 / 1000000) ≤ (331147837 / 1000000000) := by
  have h := checkLog_sound (w := (281901 / 1718099)) (n := 12)
    (lo := (82786959 / 250000000)) (hi := (331147837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718099) = 1/(718099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331147837 / 1000000000) (-82786959 / 250000000) (Real.log (718099 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185233147 / 1000000000) ≤ -Real.log (1000000 / 1203499) ∧
    -Real.log (1000000 / 1203499) ≤ (46308287 / 250000000) := by
  have h := checkLog_sound (w := (203499 / 2203499)) (n := 12)
    (lo := (185233147 / 1000000000)) (hi := (46308287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203499 / 1000000) = 1/(1000000 / 1203499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185233147 / 1000000000) (46308287 / 250000000) (Real.log (1203499 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203499 / 1000000) = -Real.log (1000000 / 1203499) := by
    rw [show ((1203499 / 1000000) : ℝ) = ((1000000 / 1203499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113763447 / 500000000) ≤ -Real.log (796501 / 1000000) ∧
    -Real.log (796501 / 1000000) ≤ (45505379 / 200000000) := by
  have h := checkLog_sound (w := (203499 / 1796501)) (n := 12)
    (lo := (113763447 / 500000000)) (hi := (45505379 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796501) = 1/(796501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45505379 / 200000000) (-113763447 / 500000000) (Real.log (796501 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92749917 / 500000000) ≤ -Real.log (50000 / 60191) ∧
    -Real.log (50000 / 60191) ≤ (37099967 / 200000000) := by
  have h := checkLog_sound (w := (10191 / 110191)) (n := 12)
    (lo := (92749917 / 500000000)) (hi := (37099967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60191 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60191 / 50000) = 1/(50000 / 60191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92749917 / 500000000) (37099967 / 200000000) (Real.log (60191 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60191 / 50000) = -Real.log (50000 / 60191) := by
    rw [show ((60191 / 50000) : ℝ) = ((50000 / 60191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56982497 / 250000000) ≤ -Real.log (39809 / 50000) ∧
    -Real.log (39809 / 50000) ≤ (227929989 / 1000000000) := by
  have h := checkLog_sound (w := (10191 / 89809)) (n := 12)
    (lo := (56982497 / 250000000)) (hi := (227929989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39809) = 1/(39809 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227929989 / 1000000000) (-56982497 / 250000000) (Real.log (39809 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (836161887 / 1000000000) ≤ -Real.log (20000000000 / 46149870801) ∧
    -Real.log (20000000000 / 46149870801) ≤ (836161889 / 1000000000) := by
  have h := checkLog_sound (w := (6149870801 / 86149870801)) (n := 12)
    (lo := (143014707 / 1000000000)) (hi := (35753677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46149870801 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46149870801 / 40000000000) = 1/(20000000000 / 46149870801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (836161887 / 1000000000) (836161889 / 1000000000) (Real.log (46149870801 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (46149870801 / 20000000000) = -Real.log (20000000000 / 46149870801) := by
    rw [show ((46149870801 / 20000000000) : ℝ) = ((20000000000 / 46149870801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (837551193 / 1000000000) ≤ -Real.log (31250000000 / 72209424507) ∧
    -Real.log (31250000000 / 72209424507) ≤ (167510239 / 200000000) := by
  have h := checkLog_sound (w := (9709424507 / 134709424507)) (n := 12)
    (lo := (144404013 / 1000000000)) (hi := (72202007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72209424507 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72209424507 / 62500000000) = 1/(31250000000 / 72209424507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (837551193 / 1000000000) (167510239 / 200000000) (Real.log (72209424507 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (72209424507 / 31250000000) = -Real.log (31250000000 / 72209424507) := by
    rw [show ((72209424507 / 31250000000) : ℝ) = ((31250000000 / 72209424507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (578568709 / 1000000000) ≤ -Real.log (250000000000 / 445870979953) ∧
    -Real.log (250000000000 / 445870979953) ≤ (57856871 / 100000000) := by
  have h := checkLog_sound (w := (195870979953 / 695870979953)) (n := 12)
    (lo := (578568709 / 1000000000)) (hi := (57856871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445870979953 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445870979953 / 250000000000) = 1/(250000000000 / 445870979953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (578568709 / 1000000000) (57856871 / 100000000) (Real.log (445870979953 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (445870979953 / 250000000000) = -Real.log (250000000000 / 445870979953) := by
    rw [show ((445870979953 / 250000000000) : ℝ) = ((250000000000 / 445870979953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4527281 / 7812500) ≤ -Real.log (500000000000 / 892565649027) ∧
    -Real.log (500000000000 / 892565649027) ≤ (579491969 / 1000000000) := by
  have h := checkLog_sound (w := (392565649027 / 1392565649027)) (n := 12)
    (lo := (4527281 / 7812500)) (hi := (579491969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892565649027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892565649027 / 500000000000) = 1/(500000000000 / 892565649027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (4527281 / 7812500) (579491969 / 1000000000) (Real.log (892565649027 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (892565649027 / 500000000000) = -Real.log (500000000000 / 892565649027) := by
    rw [show ((892565649027 / 500000000000) : ℝ) = ((500000000000 / 892565649027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (412760041 / 1000000000) ≤ -Real.log (31250000000 / 47218200291) ∧
    -Real.log (31250000000 / 47218200291) ≤ (206380021 / 500000000) := by
  have h := checkLog_sound (w := (15968200291 / 78468200291)) (n := 12)
    (lo := (412760041 / 1000000000)) (hi := (206380021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47218200291 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47218200291 / 31250000000) = 1/(31250000000 / 47218200291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (412760041 / 1000000000) (206380021 / 500000000) (Real.log (47218200291 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (47218200291 / 31250000000) = -Real.log (31250000000 / 47218200291) := by
    rw [show ((47218200291 / 31250000000) : ℝ) = ((31250000000 / 47218200291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (206714911 / 500000000) ≤ -Real.log (250000000000 / 377998693763) ∧
    -Real.log (250000000000 / 377998693763) ≤ (413429823 / 1000000000) := by
  have h := checkLog_sound (w := (127998693763 / 627998693763)) (n := 12)
    (lo := (206714911 / 500000000)) (hi := (413429823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377998693763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377998693763 / 250000000000) = 1/(250000000000 / 377998693763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (206714911 / 500000000) (413429823 / 1000000000) (Real.log (377998693763 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (377998693763 / 250000000000) = -Real.log (250000000000 / 377998693763) := by
    rw [show ((377998693763 / 250000000000) : ℝ) = ((250000000000 / 377998693763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42430153 / 1000000000) ≤ -Real.log (2396143519 / 2500000000) ∧
    -Real.log (2396143519 / 2500000000) ≤ (21215077 / 500000000) := by
  have h := checkLog_sound (w := (103856481 / 4896143519)) (n := 12)
    (lo := (42430153 / 1000000000)) (hi := (21215077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2396143519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2396143519) = 1/(2396143519 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21215077 / 500000000) (-42430153 / 1000000000) (Real.log (2396143519 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21146873 / 500000000) ≤ -Real.log (958588156999 / 1000000000000) ∧
    -Real.log (958588156999 / 1000000000000) ≤ (42293747 / 1000000000) := by
  have h := checkLog_sound (w := (41411843001 / 1958588156999)) (n := 12)
    (lo := (21146873 / 500000000)) (hi := (42293747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958588156999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958588156999) = 1/(958588156999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42293747 / 1000000000) (-21146873 / 500000000) (Real.log (958588156999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell248
