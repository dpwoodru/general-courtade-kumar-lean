import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8256_neg : (502301331 / 1000000000) ≤ -Real.log (10000000000 / 16525198939) ∧
    -Real.log (10000000000 / 16525198939) ≤ (125575333 / 250000000) := by
  have h := checkLog_sound (w := (6525198939 / 26525198939)) (n := 12)
    (lo := (502301331 / 1000000000)) (hi := (125575333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16525198939 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16525198939 / 10000000000) = 1/(10000000000 / 16525198939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8256 : Bounds (502301331 / 1000000000) (125575333 / 250000000) (Real.log (16525198939 / 10000000000)) := by
  have h := reflection_log_8256_neg
  have he : Real.log (16525198939 / 10000000000) = -Real.log (10000000000 / 16525198939) := by
    rw [show ((16525198939 / 10000000000) : ℝ) = ((10000000000 / 16525198939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8257_neg : (220339623 / 1000000000) ≤ -Real.log (2000 / 2493) ∧
    -Real.log (2000 / 2493) ≤ (27542453 / 125000000) := by
  have h := checkLog_sound (w := (493 / 4493)) (n := 12)
    (lo := (220339623 / 1000000000)) (hi := (27542453 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2000) = 1/(2000 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8257 : Bounds (220339623 / 1000000000) (27542453 / 125000000) (Real.log (2493 / 2000)) := by
  have h := reflection_log_8257_neg
  have he : Real.log (2493 / 2000) = -Real.log (2000 / 2493) := by
    rw [show ((2493 / 2000) : ℝ) = ((2000 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8258_neg : (14151313 / 50000000) ≤ -Real.log (1507 / 2000) ∧
    -Real.log (1507 / 2000) ≤ (283026261 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 3507)) (n := 12)
    (lo := (14151313 / 50000000)) (hi := (283026261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1507) = 1/(1507 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8258 : Bounds (-283026261 / 1000000000) (-14151313 / 50000000) (Real.log (1507 / 2000)) := by
  have h := reflection_log_8258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8259_neg : (246469 / 1000000000) ≤ -Real.log (2000000 / 2000493) ∧
    -Real.log (2000000 / 2000493) ≤ (24647 / 100000000) := by
  have h := checkLog_sound (w := (493 / 4000493)) (n := 12)
    (lo := (246469 / 1000000000)) (hi := (24647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000493 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000493 / 2000000) = 1/(2000000 / 2000493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8259 : Bounds (246469 / 1000000000) (24647 / 100000000) (Real.log (2000493 / 2000000)) := by
  have h := reflection_log_8259_neg
  have he : Real.log (2000493 / 2000000) = -Real.log (2000000 / 2000493) := by
    rw [show ((2000493 / 2000000) : ℝ) = ((2000000 / 2000493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8260_neg : (24653 / 100000000) ≤ -Real.log (1999507 / 2000000) ∧
    -Real.log (1999507 / 2000000) ≤ (246531 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 3999507)) (n := 12)
    (lo := (24653 / 100000000)) (hi := (246531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999507) = 1/(1999507 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8260 : Bounds (-246531 / 1000000000) (-24653 / 100000000) (Real.log (1999507 / 2000000)) := by
  have h := reflection_log_8260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8261_neg : (117111699 / 1000000000) ≤ -Real.log (200000 / 224849) ∧
    -Real.log (200000 / 224849) ≤ (1171117 / 10000000) := by
  have h := checkLog_sound (w := (24849 / 424849)) (n := 12)
    (lo := (117111699 / 1000000000)) (hi := (1171117 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224849 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224849 / 200000) = 1/(200000 / 224849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8261 : Bounds (117111699 / 1000000000) (1171117 / 10000000) (Real.log (224849 / 200000)) := by
  have h := reflection_log_8261_neg
  have he : Real.log (224849 / 200000) = -Real.log (200000 / 224849) := by
    rw [show ((224849 / 200000) : ℝ) = ((200000 / 224849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8262_neg : (132668907 / 1000000000) ≤ -Real.log (175151 / 200000) ∧
    -Real.log (175151 / 200000) ≤ (33167227 / 250000000) := by
  have h := checkLog_sound (w := (24849 / 375151)) (n := 12)
    (lo := (132668907 / 1000000000)) (hi := (33167227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 175151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 175151) = 1/(175151 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8262 : Bounds (-33167227 / 250000000) (-132668907 / 1000000000) (Real.log (175151 / 200000)) := by
  have h := reflection_log_8262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8263_neg : (117558121 / 1000000000) ≤ -Real.log (1000000 / 1124747) ∧
    -Real.log (1000000 / 1124747) ≤ (58779061 / 500000000) := by
  have h := checkLog_sound (w := (124747 / 2124747)) (n := 12)
    (lo := (117558121 / 1000000000)) (hi := (58779061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124747 / 1000000) = 1/(1000000 / 1124747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8263 : Bounds (117558121 / 1000000000) (58779061 / 500000000) (Real.log (1124747 / 1000000)) := by
  have h := reflection_log_8263_neg
  have he : Real.log (1124747 / 1000000) = -Real.log (1000000 / 1124747) := by
    rw [show ((1124747 / 1000000) : ℝ) = ((1000000 / 1124747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8264_neg : (133242291 / 1000000000) ≤ -Real.log (875253 / 1000000) ∧
    -Real.log (875253 / 1000000) ≤ (33310573 / 250000000) := by
  have h := checkLog_sound (w := (124747 / 1875253)) (n := 12)
    (lo := (133242291 / 1000000000)) (hi := (33310573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875253) = 1/(875253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8264 : Bounds (-33310573 / 250000000) (-133242291 / 1000000000) (Real.log (875253 / 1000000)) := by
  have h := reflection_log_8264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8265_neg : (1568417 / 100000000) ≤ -Real.log (984438185991 / 1000000000000) ∧
    -Real.log (984438185991 / 1000000000000) ≤ (15684171 / 1000000000) := by
  have h := checkLog_sound (w := (15561814009 / 1984438185991)) (n := 12)
    (lo := (1568417 / 100000000)) (hi := (15684171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984438185991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984438185991) = 1/(984438185991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8265 : Bounds (-15684171 / 1000000000) (-1568417 / 100000000) (Real.log (984438185991 / 1000000000000)) := by
  have h := reflection_log_8265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8266_neg : (1944651 / 125000000) ≤ -Real.log (39382527199 / 40000000000) ∧
    -Real.log (39382527199 / 40000000000) ≤ (15557209 / 1000000000) := by
  have h := checkLog_sound (w := (617472801 / 79382527199)) (n := 12)
    (lo := (1944651 / 125000000)) (hi := (15557209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39382527199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39382527199) = 1/(39382527199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8266 : Bounds (-15557209 / 1000000000) (-1944651 / 125000000) (Real.log (39382527199 / 40000000000)) := by
  have h := reflection_log_8266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8267_neg : (124890303 / 500000000) ≤ -Real.log (500000000000 / 641871870557) ∧
    -Real.log (500000000000 / 641871870557) ≤ (249780607 / 1000000000) := by
  have h := checkLog_sound (w := (141871870557 / 1141871870557)) (n := 12)
    (lo := (124890303 / 500000000)) (hi := (249780607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641871870557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641871870557 / 500000000000) = 1/(500000000000 / 641871870557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8267 : Bounds (124890303 / 500000000) (249780607 / 1000000000) (Real.log (641871870557 / 500000000000)) := by
  have h := reflection_log_8267_neg
  have he : Real.log (641871870557 / 500000000000) = -Real.log (500000000000 / 641871870557) := by
    rw [show ((641871870557 / 500000000000) : ℝ) = ((500000000000 / 641871870557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8268_neg : (250800413 / 1000000000) ≤ -Real.log (500000000000 / 642526789397) ∧
    -Real.log (500000000000 / 642526789397) ≤ (125400207 / 500000000) := by
  have h := checkLog_sound (w := (142526789397 / 1142526789397)) (n := 12)
    (lo := (250800413 / 1000000000)) (hi := (125400207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642526789397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642526789397 / 500000000000) = 1/(500000000000 / 642526789397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8268 : Bounds (250800413 / 1000000000) (125400207 / 500000000) (Real.log (642526789397 / 500000000000)) := by
  have h := reflection_log_8268_neg
  have he : Real.log (642526789397 / 500000000000) = -Real.log (500000000000 / 642526789397) := by
    rw [show ((642526789397 / 500000000000) : ℝ) = ((500000000000 / 642526789397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8269_neg : (502301331 / 1000000000) ≤ -Real.log (500000000000 / 826259946949) ∧
    -Real.log (500000000000 / 826259946949) ≤ (125575333 / 250000000) := by
  have h := checkLog_sound (w := (326259946949 / 1326259946949)) (n := 12)
    (lo := (502301331 / 1000000000)) (hi := (125575333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826259946949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826259946949 / 500000000000) = 1/(500000000000 / 826259946949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8269 : Bounds (502301331 / 1000000000) (125575333 / 250000000) (Real.log (826259946949 / 500000000000)) := by
  have h := reflection_log_8269_neg
  have he : Real.log (826259946949 / 500000000000) = -Real.log (500000000000 / 826259946949) := by
    rw [show ((826259946949 / 500000000000) : ℝ) = ((500000000000 / 826259946949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8270_neg : (125841471 / 250000000) ≤ -Real.log (62500000000 / 103392501659) ∧
    -Real.log (62500000000 / 103392501659) ≤ (100673177 / 200000000) := by
  have h := checkLog_sound (w := (40892501659 / 165892501659)) (n := 12)
    (lo := (125841471 / 250000000)) (hi := (100673177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103392501659 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103392501659 / 62500000000) = 1/(62500000000 / 103392501659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8270 : Bounds (125841471 / 250000000) (100673177 / 200000000) (Real.log (103392501659 / 62500000000)) := by
  have h := reflection_log_8270_neg
  have he : Real.log (103392501659 / 62500000000) = -Real.log (62500000000 / 103392501659) := by
    rw [show ((103392501659 / 62500000000) : ℝ) = ((62500000000 / 103392501659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8271_neg : (110370333 / 500000000) ≤ -Real.log (1000 / 1247) ∧
    -Real.log (1000 / 1247) ≤ (220740667 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 2247)) (n := 12)
    (lo := (110370333 / 500000000)) (hi := (220740667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 1000) = 1/(1000 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8271 : Bounds (110370333 / 500000000) (220740667 / 1000000000) (Real.log (1247 / 1000)) := by
  have h := reflection_log_8271_neg
  have he : Real.log (1247 / 1000) = -Real.log (1000 / 1247) := by
    rw [show ((1247 / 1000) : ℝ) = ((1000 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8272_neg : (283690051 / 1000000000) ≤ -Real.log (753 / 1000) ∧
    -Real.log (753 / 1000) ≤ (70922513 / 250000000) := by
  have h := checkLog_sound (w := (247 / 1753)) (n := 12)
    (lo := (283690051 / 1000000000)) (hi := (70922513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 753) = 1/(753 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8272 : Bounds (-70922513 / 250000000) (-283690051 / 1000000000) (Real.log (753 / 1000)) := by
  have h := reflection_log_8272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8273_neg : (246969 / 1000000000) ≤ -Real.log (1000000 / 1000247) ∧
    -Real.log (1000000 / 1000247) ≤ (24697 / 100000000) := by
  have h := checkLog_sound (w := (247 / 2000247)) (n := 12)
    (lo := (246969 / 1000000000)) (hi := (24697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000247 / 1000000) = 1/(1000000 / 1000247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8273 : Bounds (246969 / 1000000000) (24697 / 100000000) (Real.log (1000247 / 1000000)) := by
  have h := reflection_log_8273_neg
  have he : Real.log (1000247 / 1000000) = -Real.log (1000000 / 1000247) := by
    rw [show ((1000247 / 1000000) : ℝ) = ((1000000 / 1000247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8274_neg : (24703 / 100000000) ≤ -Real.log (999753 / 1000000) ∧
    -Real.log (999753 / 1000000) ≤ (247031 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1999753)) (n := 12)
    (lo := (24703 / 100000000)) (hi := (247031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999753) = 1/(999753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8274 : Bounds (-247031 / 1000000000) (-24703 / 100000000) (Real.log (999753 / 1000000)) := by
  have h := reflection_log_8274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8275_neg : (2933529 / 25000000) ≤ -Real.log (1000000 / 1124503) ∧
    -Real.log (1000000 / 1124503) ≤ (117341161 / 1000000000) := by
  have h := checkLog_sound (w := (124503 / 2124503)) (n := 12)
    (lo := (2933529 / 25000000)) (hi := (117341161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124503 / 1000000) = 1/(1000000 / 1124503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8275 : Bounds (2933529 / 25000000) (117341161 / 1000000000) (Real.log (1124503 / 1000000)) := by
  have h := reflection_log_8275_neg
  have he : Real.log (1124503 / 1000000) = -Real.log (1000000 / 1124503) := by
    rw [show ((1124503 / 1000000) : ℝ) = ((1000000 / 1124503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8276_neg : (132963553 / 1000000000) ≤ -Real.log (875497 / 1000000) ∧
    -Real.log (875497 / 1000000) ≤ (66481777 / 500000000) := by
  have h := checkLog_sound (w := (124503 / 1875497)) (n := 12)
    (lo := (132963553 / 1000000000)) (hi := (66481777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875497) = 1/(875497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8276 : Bounds (-66481777 / 500000000) (-132963553 / 1000000000) (Real.log (875497 / 1000000)) := by
  have h := reflection_log_8276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8277_neg : (7361773 / 62500000) ≤ -Real.log (500000 / 562503) ∧
    -Real.log (500000 / 562503) ≤ (117788369 / 1000000000) := by
  have h := checkLog_sound (w := (62503 / 1062503)) (n := 12)
    (lo := (7361773 / 62500000)) (hi := (117788369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562503 / 500000) = 1/(500000 / 562503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8277 : Bounds (7361773 / 62500000) (117788369 / 1000000000) (Real.log (562503 / 500000)) := by
  have h := reflection_log_8277_neg
  have he : Real.log (562503 / 500000) = -Real.log (500000 / 562503) := by
    rw [show ((562503 / 500000) : ℝ) = ((500000 / 562503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8278_neg : (133538249 / 1000000000) ≤ -Real.log (437497 / 500000) ∧
    -Real.log (437497 / 500000) ≤ (534153 / 4000000) := by
  have h := checkLog_sound (w := (62503 / 937497)) (n := 12)
    (lo := (133538249 / 1000000000)) (hi := (534153 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437497) = 1/(437497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8278 : Bounds (-534153 / 4000000) (-133538249 / 1000000000) (Real.log (437497 / 500000)) := by
  have h := reflection_log_8278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8279_neg : (393747 / 25000000) ≤ -Real.log (246093374991 / 250000000000) ∧
    -Real.log (246093374991 / 250000000000) ≤ (15749881 / 1000000000) := by
  have h := checkLog_sound (w := (3906625009 / 496093374991)) (n := 12)
    (lo := (393747 / 25000000)) (hi := (15749881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246093374991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246093374991) = 1/(246093374991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8279 : Bounds (-15749881 / 1000000000) (-393747 / 25000000) (Real.log (246093374991 / 250000000000)) := by
  have h := reflection_log_8279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8280_neg : (15622393 / 1000000000) ≤ -Real.log (984499002991 / 1000000000000) ∧
    -Real.log (984499002991 / 1000000000000) ≤ (7811197 / 500000000) := by
  have h := checkLog_sound (w := (15500997009 / 1984499002991)) (n := 12)
    (lo := (15622393 / 1000000000)) (hi := (7811197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984499002991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984499002991) = 1/(984499002991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8280 : Bounds (-7811197 / 500000000) (-15622393 / 1000000000) (Real.log (984499002991 / 1000000000000)) := by
  have h := reflection_log_8280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8281_neg : (125152357 / 500000000) ≤ -Real.log (500000000000 / 642208368503) ∧
    -Real.log (500000000000 / 642208368503) ≤ (50060943 / 200000000) := by
  have h := checkLog_sound (w := (142208368503 / 1142208368503)) (n := 12)
    (lo := (125152357 / 500000000)) (hi := (50060943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642208368503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642208368503 / 500000000000) = 1/(500000000000 / 642208368503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8281 : Bounds (125152357 / 500000000) (50060943 / 200000000) (Real.log (642208368503 / 500000000000)) := by
  have h := reflection_log_8281_neg
  have he : Real.log (642208368503 / 500000000000) = -Real.log (500000000000 / 642208368503) := by
    rw [show ((642208368503 / 500000000000) : ℝ) = ((500000000000 / 642208368503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8282_neg : (125663309 / 500000000) ≤ -Real.log (250000000000 / 321432489823) ∧
    -Real.log (250000000000 / 321432489823) ≤ (251326619 / 1000000000) := by
  have h := checkLog_sound (w := (71432489823 / 571432489823)) (n := 12)
    (lo := (125663309 / 500000000)) (hi := (251326619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321432489823 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321432489823 / 250000000000) = 1/(250000000000 / 321432489823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8282 : Bounds (125663309 / 500000000) (251326619 / 1000000000) (Real.log (321432489823 / 250000000000)) := by
  have h := reflection_log_8282_neg
  have he : Real.log (321432489823 / 250000000000) = -Real.log (250000000000 / 321432489823) := by
    rw [show ((321432489823 / 250000000000) : ℝ) = ((250000000000 / 321432489823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8283_neg : (125841471 / 250000000) ≤ -Real.log (500000000000 / 827140013271) ∧
    -Real.log (500000000000 / 827140013271) ≤ (100673177 / 200000000) := by
  have h := checkLog_sound (w := (327140013271 / 1327140013271)) (n := 12)
    (lo := (125841471 / 250000000)) (hi := (100673177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827140013271 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827140013271 / 500000000000) = 1/(500000000000 / 827140013271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8283 : Bounds (125841471 / 250000000) (100673177 / 200000000) (Real.log (827140013271 / 500000000000)) := by
  have h := reflection_log_8283_neg
  have he : Real.log (827140013271 / 500000000000) = -Real.log (500000000000 / 827140013271) := by
    rw [show ((827140013271 / 500000000000) : ℝ) = ((500000000000 / 827140013271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8284_neg : (504430717 / 1000000000) ≤ -Real.log (25000000000 / 41401062417) ∧
    -Real.log (25000000000 / 41401062417) ≤ (252215359 / 500000000) := by
  have h := checkLog_sound (w := (16401062417 / 66401062417)) (n := 12)
    (lo := (504430717 / 1000000000)) (hi := (252215359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41401062417 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41401062417 / 25000000000) = 1/(25000000000 / 41401062417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8284 : Bounds (504430717 / 1000000000) (252215359 / 500000000) (Real.log (41401062417 / 25000000000)) := by
  have h := reflection_log_8284_neg
  have he : Real.log (41401062417 / 25000000000) = -Real.log (25000000000 / 41401062417) := by
    rw [show ((41401062417 / 25000000000) : ℝ) = ((25000000000 / 41401062417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8285_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8285 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_8285_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8286_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8286 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_8286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8287_neg : (247469 / 1000000000) ≤ -Real.log (400000 / 400099) ∧
    -Real.log (400000 / 400099) ≤ (24747 / 100000000) := by
  have h := checkLog_sound (w := (99 / 800099)) (n := 12)
    (lo := (247469 / 1000000000)) (hi := (24747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400099 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400099 / 400000) = 1/(400000 / 400099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8287 : Bounds (247469 / 1000000000) (24747 / 100000000) (Real.log (400099 / 400000)) := by
  have h := reflection_log_8287_neg
  have he : Real.log (400099 / 400000) = -Real.log (400000 / 400099) := by
    rw [show ((400099 / 400000) : ℝ) = ((400000 / 400099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8288_neg : (24753 / 100000000) ≤ -Real.log (399901 / 400000) ∧
    -Real.log (399901 / 400000) ≤ (247531 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 799901)) (n := 12)
    (lo := (24753 / 100000000)) (hi := (247531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399901) = 1/(399901 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8288 : Bounds (-247531 / 1000000000) (-24753 / 100000000) (Real.log (399901 / 400000)) := by
  have h := reflection_log_8288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8289_neg : (14696321 / 125000000) ≤ -Real.log (1000000 / 1124761) ∧
    -Real.log (1000000 / 1124761) ≤ (117570569 / 1000000000) := by
  have h := checkLog_sound (w := (124761 / 2124761)) (n := 12)
    (lo := (14696321 / 125000000)) (hi := (117570569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1124761 / 1000000) = 1/(1000000 / 1124761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8289 : Bounds (14696321 / 125000000) (117570569 / 1000000000) (Real.log (1124761 / 1000000)) := by
  have h := reflection_log_8289_neg
  have he : Real.log (1124761 / 1000000) = -Real.log (1000000 / 1124761) := by
    rw [show ((1124761 / 1000000) : ℝ) = ((1000000 / 1124761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8290_neg : (133258287 / 1000000000) ≤ -Real.log (875239 / 1000000) ∧
    -Real.log (875239 / 1000000) ≤ (8328643 / 62500000) := by
  have h := checkLog_sound (w := (124761 / 1875239)) (n := 12)
    (lo := (133258287 / 1000000000)) (hi := (8328643 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 875239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 875239) = 1/(875239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8290 : Bounds (-8328643 / 62500000) (-133258287 / 1000000000) (Real.log (875239 / 1000000)) := by
  have h := reflection_log_8290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8291_neg : (118018563 / 1000000000) ≤ -Real.log (200000 / 225053) ∧
    -Real.log (200000 / 225053) ≤ (29504641 / 250000000) := by
  have h := checkLog_sound (w := (25053 / 425053)) (n := 12)
    (lo := (118018563 / 1000000000)) (hi := (29504641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225053 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225053 / 200000) = 1/(200000 / 225053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8291 : Bounds (118018563 / 1000000000) (29504641 / 250000000) (Real.log (225053 / 200000)) := by
  have h := reflection_log_8291_neg
  have he : Real.log (225053 / 200000) = -Real.log (200000 / 225053) := by
    rw [show ((225053 / 200000) : ℝ) = ((200000 / 225053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8292_neg : (26766859 / 200000000) ≤ -Real.log (174947 / 200000) ∧
    -Real.log (174947 / 200000) ≤ (16729287 / 125000000) := by
  have h := checkLog_sound (w := (25053 / 374947)) (n := 12)
    (lo := (26766859 / 200000000)) (hi := (16729287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174947) = 1/(174947 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8292 : Bounds (-16729287 / 125000000) (-26766859 / 200000000) (Real.log (174947 / 200000)) := by
  have h := reflection_log_8292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8293_neg : (3953933 / 250000000) ≤ -Real.log (39372347191 / 40000000000) ∧
    -Real.log (39372347191 / 40000000000) ≤ (15815733 / 1000000000) := by
  have h := checkLog_sound (w := (627652809 / 79372347191)) (n := 12)
    (lo := (3953933 / 250000000)) (hi := (15815733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39372347191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39372347191) = 1/(39372347191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8293 : Bounds (-15815733 / 1000000000) (-3953933 / 250000000) (Real.log (39372347191 / 40000000000)) := by
  have h := reflection_log_8293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8294_neg : (7843859 / 500000000) ≤ -Real.log (984434692879 / 1000000000000) ∧
    -Real.log (984434692879 / 1000000000000) ≤ (15687719 / 1000000000) := by
  have h := checkLog_sound (w := (15565307121 / 1984434692879)) (n := 12)
    (lo := (7843859 / 500000000)) (hi := (15687719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984434692879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984434692879) = 1/(984434692879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8294 : Bounds (-15687719 / 1000000000) (-7843859 / 500000000) (Real.log (984434692879 / 1000000000000)) := by
  have h := reflection_log_8294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8295_neg : (50165771 / 200000000) ≤ -Real.log (500000000000 / 642545064833) ∧
    -Real.log (500000000000 / 642545064833) ≤ (31353607 / 125000000) := by
  have h := checkLog_sound (w := (142545064833 / 1142545064833)) (n := 12)
    (lo := (50165771 / 200000000)) (hi := (31353607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642545064833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642545064833 / 500000000000) = 1/(500000000000 / 642545064833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8295 : Bounds (50165771 / 200000000) (31353607 / 125000000) (Real.log (642545064833 / 500000000000)) := by
  have h := reflection_log_8295_neg
  have he : Real.log (642545064833 / 500000000000) = -Real.log (500000000000 / 642545064833) := by
    rw [show ((642545064833 / 500000000000) : ℝ) = ((500000000000 / 642545064833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8296_neg : (251852859 / 1000000000) ≤ -Real.log (125000000000 / 160800842541) ∧
    -Real.log (125000000000 / 160800842541) ≤ (12592643 / 50000000) := by
  have h := checkLog_sound (w := (35800842541 / 285800842541)) (n := 12)
    (lo := (251852859 / 1000000000)) (hi := (12592643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160800842541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160800842541 / 125000000000) = 1/(125000000000 / 160800842541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8296 : Bounds (251852859 / 1000000000) (12592643 / 50000000) (Real.log (160800842541 / 125000000000)) := by
  have h := reflection_log_8296_neg
  have he : Real.log (160800842541 / 125000000000) = -Real.log (125000000000 / 160800842541) := by
    rw [show ((160800842541 / 125000000000) : ℝ) = ((125000000000 / 160800842541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8297_neg : (504430717 / 1000000000) ≤ -Real.log (500000000000 / 828021248339) ∧
    -Real.log (500000000000 / 828021248339) ≤ (252215359 / 500000000) := by
  have h := checkLog_sound (w := (328021248339 / 1328021248339)) (n := 12)
    (lo := (504430717 / 1000000000)) (hi := (252215359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828021248339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828021248339 / 500000000000) = 1/(500000000000 / 828021248339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8297 : Bounds (504430717 / 1000000000) (252215359 / 500000000) (Real.log (828021248339 / 500000000000)) := by
  have h := reflection_log_8297_neg
  have he : Real.log (828021248339 / 500000000000) = -Real.log (500000000000 / 828021248339) := by
    rw [show ((828021248339 / 500000000000) : ℝ) = ((500000000000 / 828021248339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8298_neg : (505495831 / 1000000000) ≤ -Real.log (250000000000 / 414451827243) ∧
    -Real.log (250000000000 / 414451827243) ≤ (63186979 / 125000000) := by
  have h := checkLog_sound (w := (164451827243 / 664451827243)) (n := 12)
    (lo := (505495831 / 1000000000)) (hi := (63186979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414451827243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414451827243 / 250000000000) = 1/(250000000000 / 414451827243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8298 : Bounds (505495831 / 1000000000) (63186979 / 125000000) (Real.log (414451827243 / 250000000000)) := by
  have h := reflection_log_8298_neg
  have he : Real.log (414451827243 / 250000000000) = -Real.log (250000000000 / 414451827243) := by
    rw [show ((414451827243 / 250000000000) : ℝ) = ((250000000000 / 414451827243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8299_neg : (221542269 / 1000000000) ≤ -Real.log (125 / 156) ∧
    -Real.log (125 / 156) ≤ (22154227 / 100000000) := by
  have h := checkLog_sound (w := (31 / 281)) (n := 12)
    (lo := (221542269 / 1000000000)) (hi := (22154227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156 / 125) = 1/(125 / 156) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8299 : Bounds (221542269 / 1000000000) (22154227 / 100000000) (Real.log (156 / 125)) := by
  have h := reflection_log_8299_neg
  have he : Real.log (156 / 125) = -Real.log (125 / 156) := by
    rw [show ((156 / 125) : ℝ) = ((125 / 156) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8300_neg : (57003791 / 200000000) ≤ -Real.log (94 / 125) ∧
    -Real.log (94 / 125) ≤ (71254739 / 250000000) := by
  have h := checkLog_sound (w := (31 / 219)) (n := 12)
    (lo := (57003791 / 200000000)) (hi := (71254739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 94) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 94) = 1/(94 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8300 : Bounds (-71254739 / 250000000) (-57003791 / 200000000) (Real.log (94 / 125)) := by
  have h := reflection_log_8300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8301_neg : (247969 / 1000000000) ≤ -Real.log (125000 / 125031) ∧
    -Real.log (125000 / 125031) ≤ (24797 / 100000000) := by
  have h := checkLog_sound (w := (31 / 250031)) (n := 12)
    (lo := (247969 / 1000000000)) (hi := (24797 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125031 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125031 / 125000) = 1/(125000 / 125031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8301 : Bounds (247969 / 1000000000) (24797 / 100000000) (Real.log (125031 / 125000)) := by
  have h := reflection_log_8301_neg
  have he : Real.log (125031 / 125000) = -Real.log (125000 / 125031) := by
    rw [show ((125031 / 125000) : ℝ) = ((125000 / 125031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8302_neg : (24803 / 100000000) ≤ -Real.log (124969 / 125000) ∧
    -Real.log (124969 / 125000) ≤ (248031 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 249969)) (n := 12)
    (lo := (24803 / 100000000)) (hi := (248031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124969) = 1/(124969 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8302 : Bounds (-248031 / 1000000000) (-24803 / 100000000) (Real.log (124969 / 125000)) := by
  have h := reflection_log_8302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8303_neg : (29449981 / 250000000) ≤ -Real.log (1000000 / 1125019) ∧
    -Real.log (1000000 / 1125019) ≤ (4711997 / 40000000) := by
  have h := checkLog_sound (w := (125019 / 2125019)) (n := 12)
    (lo := (29449981 / 250000000)) (hi := (4711997 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1125019 / 1000000) = 1/(1000000 / 1125019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8303 : Bounds (29449981 / 250000000) (4711997 / 40000000) (Real.log (1125019 / 1000000)) := by
  have h := reflection_log_8303_neg
  have he : Real.log (1125019 / 1000000) = -Real.log (1000000 / 1125019) := by
    rw [show ((1125019 / 1000000) : ℝ) = ((1000000 / 1125019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8304_neg : (133553107 / 1000000000) ≤ -Real.log (874981 / 1000000) ∧
    -Real.log (874981 / 1000000) ≤ (33388277 / 250000000) := by
  have h := checkLog_sound (w := (125019 / 1874981)) (n := 12)
    (lo := (133553107 / 1000000000)) (hi := (33388277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 874981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 874981) = 1/(874981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8304 : Bounds (-33388277 / 250000000) (-133553107 / 1000000000) (Real.log (874981 / 1000000)) := by
  have h := reflection_log_8304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8305_neg : (461909 / 3906250) ≤ -Real.log (250000 / 281381) ∧
    -Real.log (250000 / 281381) ≤ (23649741 / 200000000) := by
  have h := checkLog_sound (w := (31381 / 531381)) (n := 12)
    (lo := (461909 / 3906250)) (hi := (23649741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281381 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281381 / 250000) = 1/(250000 / 281381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8305 : Bounds (461909 / 3906250) (23649741 / 200000000) (Real.log (281381 / 250000)) := by
  have h := reflection_log_8305_neg
  have he : Real.log (281381 / 250000) = -Real.log (250000 / 281381) := by
    rw [show ((281381 / 250000) : ℝ) = ((250000 / 281381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8306_neg : (134130429 / 1000000000) ≤ -Real.log (218619 / 250000) ∧
    -Real.log (218619 / 250000) ≤ (13413043 / 100000000) := by
  have h := checkLog_sound (w := (31381 / 468619)) (n := 12)
    (lo := (134130429 / 1000000000)) (hi := (13413043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 218619) = 1/(218619 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8306 : Bounds (-13413043 / 100000000) (-134130429 / 1000000000) (Real.log (218619 / 250000)) := by
  have h := reflection_log_8306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8307_neg : (3970431 / 250000000) ≤ -Real.log (61515232839 / 62500000000) ∧
    -Real.log (61515232839 / 62500000000) ≤ (635269 / 40000000) := by
  have h := checkLog_sound (w := (984767161 / 124015232839)) (n := 12)
    (lo := (3970431 / 250000000)) (hi := (635269 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61515232839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61515232839) = 1/(61515232839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8307 : Bounds (-635269 / 40000000) (-3970431 / 250000000) (Real.log (61515232839 / 62500000000)) := by
  have h := reflection_log_8307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8308_neg : (7876591 / 500000000) ≤ -Real.log (984370249639 / 1000000000000) ∧
    -Real.log (984370249639 / 1000000000000) ≤ (15753183 / 1000000000) := by
  have h := checkLog_sound (w := (15629750361 / 1984370249639)) (n := 12)
    (lo := (7876591 / 500000000)) (hi := (15753183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984370249639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984370249639) = 1/(984370249639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8308 : Bounds (-15753183 / 1000000000) (-7876591 / 500000000) (Real.log (984370249639 / 1000000000000)) := by
  have h := reflection_log_8308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8309_neg : (251353031 / 1000000000) ≤ -Real.log (250000000000 / 321440979861) ∧
    -Real.log (250000000000 / 321440979861) ≤ (31419129 / 125000000) := by
  have h := checkLog_sound (w := (71440979861 / 571440979861)) (n := 12)
    (lo := (251353031 / 1000000000)) (hi := (31419129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321440979861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321440979861 / 250000000000) = 1/(250000000000 / 321440979861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8309 : Bounds (251353031 / 1000000000) (31419129 / 125000000) (Real.log (321440979861 / 250000000000)) := by
  have h := reflection_log_8309_neg
  have he : Real.log (321440979861 / 250000000000) = -Real.log (250000000000 / 321440979861) := by
    rw [show ((321440979861 / 250000000000) : ℝ) = ((250000000000 / 321440979861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8310_neg : (126189567 / 500000000) ≤ -Real.log (500000000000 / 643541961129) ∧
    -Real.log (500000000000 / 643541961129) ≤ (50475827 / 200000000) := by
  have h := checkLog_sound (w := (143541961129 / 1143541961129)) (n := 12)
    (lo := (126189567 / 500000000)) (hi := (50475827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643541961129 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643541961129 / 500000000000) = 1/(500000000000 / 643541961129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8310 : Bounds (126189567 / 500000000) (50475827 / 200000000) (Real.log (643541961129 / 500000000000)) := by
  have h := reflection_log_8310_neg
  have he : Real.log (643541961129 / 500000000000) = -Real.log (500000000000 / 643541961129) := by
    rw [show ((643541961129 / 500000000000) : ℝ) = ((500000000000 / 643541961129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8311_neg : (505495831 / 1000000000) ≤ -Real.log (100000000000 / 165780730897) ∧
    -Real.log (100000000000 / 165780730897) ≤ (63186979 / 125000000) := by
  have h := checkLog_sound (w := (65780730897 / 265780730897)) (n := 12)
    (lo := (505495831 / 1000000000)) (hi := (63186979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165780730897 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165780730897 / 100000000000) = 1/(100000000000 / 165780730897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8311 : Bounds (505495831 / 1000000000) (63186979 / 125000000) (Real.log (165780730897 / 100000000000)) := by
  have h := reflection_log_8311_neg
  have he : Real.log (165780730897 / 100000000000) = -Real.log (100000000000 / 165780730897) := by
    rw [show ((165780730897 / 100000000000) : ℝ) = ((100000000000 / 165780730897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8312_neg : (63320153 / 125000000) ≤ -Real.log (500000000000 / 829787234043) ∧
    -Real.log (500000000000 / 829787234043) ≤ (20262449 / 40000000) := by
  have h := checkLog_sound (w := (329787234043 / 1329787234043)) (n := 12)
    (lo := (63320153 / 125000000)) (hi := (20262449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829787234043 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829787234043 / 500000000000) = 1/(500000000000 / 829787234043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8312 : Bounds (63320153 / 125000000) (20262449 / 40000000) (Real.log (829787234043 / 500000000000)) := by
  have h := reflection_log_8312_neg
  have he : Real.log (829787234043 / 500000000000) = -Real.log (500000000000 / 829787234043) := by
    rw [show ((829787234043 / 500000000000) : ℝ) = ((500000000000 / 829787234043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8313_neg : (22194283 / 100000000) ≤ -Real.log (2000 / 2497) ∧
    -Real.log (2000 / 2497) ≤ (221942831 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 4497)) (n := 12)
    (lo := (22194283 / 100000000)) (hi := (221942831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 2000) = 1/(2000 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8313 : Bounds (22194283 / 100000000) (221942831 / 1000000000) (Real.log (2497 / 2000)) := by
  have h := reflection_log_8313_neg
  have he : Real.log (2497 / 2000) = -Real.log (2000 / 2497) := by
    rw [show ((2497 / 2000) : ℝ) = ((2000 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8314_neg : (285684069 / 1000000000) ≤ -Real.log (1503 / 2000) ∧
    -Real.log (1503 / 2000) ≤ (28568407 / 100000000) := by
  have h := checkLog_sound (w := (497 / 3503)) (n := 12)
    (lo := (285684069 / 1000000000)) (hi := (28568407 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1503) = 1/(1503 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8314 : Bounds (-28568407 / 100000000) (-285684069 / 1000000000) (Real.log (1503 / 2000)) := by
  have h := reflection_log_8314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8315_neg : (248469 / 1000000000) ≤ -Real.log (2000000 / 2000497) ∧
    -Real.log (2000000 / 2000497) ≤ (24847 / 100000000) := by
  have h := checkLog_sound (w := (497 / 4000497)) (n := 12)
    (lo := (248469 / 1000000000)) (hi := (24847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000497 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000497 / 2000000) = 1/(2000000 / 2000497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8315 : Bounds (248469 / 1000000000) (24847 / 100000000) (Real.log (2000497 / 2000000)) := by
  have h := reflection_log_8315_neg
  have he : Real.log (2000497 / 2000000) = -Real.log (2000000 / 2000497) := by
    rw [show ((2000497 / 2000000) : ℝ) = ((2000000 / 2000497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8316_neg : (24853 / 100000000) ≤ -Real.log (1999503 / 2000000) ∧
    -Real.log (1999503 / 2000000) ≤ (248531 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 3999503)) (n := 12)
    (lo := (24853 / 100000000)) (hi := (248531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999503) = 1/(1999503 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8316 : Bounds (-248531 / 1000000000) (-24853 / 100000000) (Real.log (1999503 / 2000000)) := by
  have h := reflection_log_8316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8317_neg : (29507529 / 250000000) ≤ -Real.log (500000 / 562639) ∧
    -Real.log (500000 / 562639) ≤ (118030117 / 1000000000) := by
  have h := checkLog_sound (w := (62639 / 1062639)) (n := 12)
    (lo := (29507529 / 250000000)) (hi := (118030117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(562639 / 500000) = 1/(500000 / 562639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8317 : Bounds (29507529 / 250000000) (118030117 / 1000000000) (Real.log (562639 / 500000)) := by
  have h := reflection_log_8317_neg
  have he : Real.log (562639 / 500000) = -Real.log (500000 / 562639) := by
    rw [show ((562639 / 500000) : ℝ) = ((500000 / 562639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8318_neg : (133849157 / 1000000000) ≤ -Real.log (437361 / 500000) ∧
    -Real.log (437361 / 500000) ≤ (66924579 / 500000000) := by
  have h := checkLog_sound (w := (62639 / 937361)) (n := 12)
    (lo := (133849157 / 1000000000)) (hi := (66924579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 437361) = 1/(437361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8318 : Bounds (-66924579 / 500000000) (-133849157 / 1000000000) (Real.log (437361 / 500000)) := by
  have h := reflection_log_8318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8319_neg : (118478793 / 1000000000) ≤ -Real.log (1000000 / 1125783) ∧
    -Real.log (1000000 / 1125783) ≤ (59239397 / 500000000) := by
  have h := checkLog_sound (w := (125783 / 2125783)) (n := 12)
    (lo := (118478793 / 1000000000)) (hi := (59239397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1125783 / 1000000) = 1/(1000000 / 1125783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8319 : Bounds (118478793 / 1000000000) (59239397 / 500000000) (Real.log (1125783 / 1000000)) := by
  have h := reflection_log_8319_neg
  have he : Real.log (1125783 / 1000000) = -Real.log (1000000 / 1125783) := by
    rw [show ((1125783 / 1000000) : ℝ) = ((1000000 / 1125783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
