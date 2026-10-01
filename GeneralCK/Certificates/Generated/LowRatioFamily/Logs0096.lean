import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6144_neg : (35495301 / 200000000) ≤ -Real.log (5000 / 5971) ∧
    -Real.log (5000 / 5971) ≤ (88738253 / 500000000) := by
  have h := checkLog_sound (w := (971 / 10971)) (n := 12)
    (lo := (35495301 / 200000000)) (hi := (88738253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5971 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5971 / 5000) = 1/(5000 / 5971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6144 : Bounds (35495301 / 200000000) (88738253 / 500000000) (Real.log (5971 / 5000)) := by
  have h := reflection_log_6144_neg
  have he : Real.log (5971 / 5000) = -Real.log (5000 / 5971) := by
    rw [show ((5971 / 5000) : ℝ) = ((5000 / 5971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6145_neg : (107959853 / 500000000) ≤ -Real.log (4029 / 5000) ∧
    -Real.log (4029 / 5000) ≤ (215919707 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 9029)) (n := 12)
    (lo := (107959853 / 500000000)) (hi := (215919707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4029) = 1/(4029 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6145 : Bounds (-215919707 / 1000000000) (-107959853 / 500000000) (Real.log (4029 / 5000)) := by
  have h := reflection_log_6145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6146_neg : (194181 / 1000000000) ≤ -Real.log (5000000 / 5000971) ∧
    -Real.log (5000000 / 5000971) ≤ (97091 / 500000000) := by
  have h := checkLog_sound (w := (971 / 10000971)) (n := 12)
    (lo := (194181 / 1000000000)) (hi := (97091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000971 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000971 / 5000000) = 1/(5000000 / 5000971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6146 : Bounds (194181 / 1000000000) (97091 / 500000000) (Real.log (5000971 / 5000000)) := by
  have h := reflection_log_6146_neg
  have he : Real.log (5000971 / 5000000) = -Real.log (5000000 / 5000971) := by
    rw [show ((5000971 / 5000000) : ℝ) = ((5000000 / 5000971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6147_neg : (97109 / 500000000) ≤ -Real.log (4999029 / 5000000) ∧
    -Real.log (4999029 / 5000000) ≤ (194219 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 9999029)) (n := 12)
    (lo := (97109 / 500000000)) (hi := (194219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999029) = 1/(4999029 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6147 : Bounds (-194219 / 1000000000) (-97109 / 500000000) (Real.log (4999029 / 5000000)) := by
  have h := reflection_log_6147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6148_neg : (93144199 / 1000000000) ≤ -Real.log (50000 / 54881) ∧
    -Real.log (50000 / 54881) ≤ (465721 / 5000000) := by
  have h := checkLog_sound (w := (4881 / 104881)) (n := 12)
    (lo := (93144199 / 1000000000)) (hi := (465721 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54881 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54881 / 50000) = 1/(50000 / 54881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6148 : Bounds (93144199 / 1000000000) (465721 / 5000000) (Real.log (54881 / 50000)) := by
  have h := reflection_log_6148_neg
  have he : Real.log (54881 / 50000) = -Real.log (50000 / 54881) := by
    rw [show ((54881 / 50000) : ℝ) = ((50000 / 54881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6149_neg : (102719561 / 1000000000) ≤ -Real.log (45119 / 50000) ∧
    -Real.log (45119 / 50000) ≤ (51359781 / 500000000) := by
  have h := checkLog_sound (w := (4881 / 95119)) (n := 12)
    (lo := (102719561 / 1000000000)) (hi := (51359781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45119) = 1/(45119 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6149 : Bounds (-51359781 / 500000000) (-102719561 / 1000000000) (Real.log (45119 / 50000)) := by
  have h := reflection_log_6149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6150_neg : (11670923 / 125000000) ≤ -Real.log (200000 / 219573) ∧
    -Real.log (200000 / 219573) ≤ (18673477 / 200000000) := by
  have h := checkLog_sound (w := (19573 / 419573)) (n := 12)
    (lo := (11670923 / 125000000)) (hi := (18673477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219573 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219573 / 200000) = 1/(200000 / 219573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6150 : Bounds (11670923 / 125000000) (18673477 / 200000000) (Real.log (219573 / 200000)) := by
  have h := reflection_log_6150_neg
  have he : Real.log (219573 / 200000) = -Real.log (200000 / 219573) := by
    rw [show ((219573 / 200000) : ℝ) = ((200000 / 219573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6151_neg : (51495551 / 500000000) ≤ -Real.log (180427 / 200000) ∧
    -Real.log (180427 / 200000) ≤ (102991103 / 1000000000) := by
  have h := checkLog_sound (w := (19573 / 380427)) (n := 12)
    (lo := (51495551 / 500000000)) (hi := (102991103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180427) = 1/(180427 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6151 : Bounds (-102991103 / 1000000000) (-51495551 / 500000000) (Real.log (180427 / 200000)) := by
  have h := reflection_log_6151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6152_neg : (4811859 / 500000000) ≤ -Real.log (39616897671 / 40000000000) ∧
    -Real.log (39616897671 / 40000000000) ≤ (9623719 / 1000000000) := by
  have h := checkLog_sound (w := (383102329 / 79616897671)) (n := 12)
    (lo := (4811859 / 500000000)) (hi := (9623719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39616897671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39616897671) = 1/(39616897671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6152 : Bounds (-9623719 / 1000000000) (-4811859 / 500000000) (Real.log (39616897671 / 40000000000)) := by
  have h := reflection_log_6152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6153_neg : (4787681 / 500000000) ≤ -Real.log (2476175839 / 2500000000) ∧
    -Real.log (2476175839 / 2500000000) ≤ (9575363 / 1000000000) := by
  have h := checkLog_sound (w := (23824161 / 4976175839)) (n := 12)
    (lo := (4787681 / 500000000)) (hi := (9575363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2476175839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2476175839) = 1/(2476175839 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6153 : Bounds (-9575363 / 1000000000) (-4787681 / 500000000) (Real.log (2476175839 / 2500000000)) := by
  have h := reflection_log_6153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6154_neg : (195863761 / 1000000000) ≤ -Real.log (125000000000 / 152045147277) ∧
    -Real.log (125000000000 / 152045147277) ≤ (97931881 / 500000000) := by
  have h := checkLog_sound (w := (27045147277 / 277045147277)) (n := 12)
    (lo := (195863761 / 1000000000)) (hi := (97931881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152045147277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152045147277 / 125000000000) = 1/(125000000000 / 152045147277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6154 : Bounds (195863761 / 1000000000) (97931881 / 500000000) (Real.log (152045147277 / 125000000000)) := by
  have h := reflection_log_6154_neg
  have he : Real.log (152045147277 / 125000000000) = -Real.log (125000000000 / 152045147277) := by
    rw [show ((152045147277 / 125000000000) : ℝ) = ((125000000000 / 152045147277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6155_neg : (196358487 / 1000000000) ≤ -Real.log (250000000000 / 304240773277) ∧
    -Real.log (250000000000 / 304240773277) ≤ (24544811 / 125000000) := by
  have h := checkLog_sound (w := (54240773277 / 554240773277)) (n := 12)
    (lo := (196358487 / 1000000000)) (hi := (24544811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304240773277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304240773277 / 250000000000) = 1/(250000000000 / 304240773277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6155 : Bounds (196358487 / 1000000000) (24544811 / 125000000) (Real.log (304240773277 / 250000000000)) := by
  have h := reflection_log_6155_neg
  have he : Real.log (304240773277 / 250000000000) = -Real.log (250000000000 / 304240773277) := by
    rw [show ((304240773277 / 250000000000) : ℝ) = ((250000000000 / 304240773277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6156_neg : (393188377 / 1000000000) ≤ -Real.log (250000000000 / 370424370269) ∧
    -Real.log (250000000000 / 370424370269) ≤ (196594189 / 500000000) := by
  have h := checkLog_sound (w := (120424370269 / 620424370269)) (n := 12)
    (lo := (393188377 / 1000000000)) (hi := (196594189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370424370269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370424370269 / 250000000000) = 1/(250000000000 / 370424370269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6156 : Bounds (393188377 / 1000000000) (196594189 / 500000000) (Real.log (370424370269 / 250000000000)) := by
  have h := reflection_log_6156_neg
  have he : Real.log (370424370269 / 250000000000) = -Real.log (250000000000 / 370424370269) := by
    rw [show ((370424370269 / 250000000000) : ℝ) = ((250000000000 / 370424370269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6157_neg : (393396211 / 1000000000) ≤ -Real.log (500000000000 / 741002730207) ∧
    -Real.log (500000000000 / 741002730207) ≤ (98349053 / 250000000) := by
  have h := checkLog_sound (w := (241002730207 / 1241002730207)) (n := 12)
    (lo := (393396211 / 1000000000)) (hi := (98349053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741002730207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741002730207 / 500000000000) = 1/(500000000000 / 741002730207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6157 : Bounds (393396211 / 1000000000) (98349053 / 250000000) (Real.log (741002730207 / 500000000000)) := by
  have h := reflection_log_6157_neg
  have he : Real.log (741002730207 / 500000000000) = -Real.log (500000000000 / 741002730207) := by
    rw [show ((741002730207 / 500000000000) : ℝ) = ((500000000000 / 741002730207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6158_neg : (177560239 / 1000000000) ≤ -Real.log (10000 / 11943) ∧
    -Real.log (10000 / 11943) ≤ (2219503 / 12500000) := by
  have h := checkLog_sound (w := (1943 / 21943)) (n := 12)
    (lo := (177560239 / 1000000000)) (hi := (2219503 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11943 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11943 / 10000) = 1/(10000 / 11943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6158 : Bounds (177560239 / 1000000000) (2219503 / 12500000) (Real.log (11943 / 10000)) := by
  have h := reflection_log_6158_neg
  have he : Real.log (11943 / 10000) = -Real.log (10000 / 11943) := by
    rw [show ((11943 / 10000) : ℝ) = ((10000 / 11943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6159_neg : (108021907 / 500000000) ≤ -Real.log (8057 / 10000) ∧
    -Real.log (8057 / 10000) ≤ (43208763 / 200000000) := by
  have h := checkLog_sound (w := (1943 / 18057)) (n := 12)
    (lo := (108021907 / 500000000)) (hi := (43208763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8057) = 1/(8057 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6159 : Bounds (-43208763 / 200000000) (-108021907 / 500000000) (Real.log (8057 / 10000)) := by
  have h := reflection_log_6159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6160_neg : (194281 / 1000000000) ≤ -Real.log (10000000 / 10001943) ∧
    -Real.log (10000000 / 10001943) ≤ (97141 / 500000000) := by
  have h := checkLog_sound (w := (1943 / 20001943)) (n := 12)
    (lo := (194281 / 1000000000)) (hi := (97141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001943 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001943 / 10000000) = 1/(10000000 / 10001943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6160 : Bounds (194281 / 1000000000) (97141 / 500000000) (Real.log (10001943 / 10000000)) := by
  have h := reflection_log_6160_neg
  have he : Real.log (10001943 / 10000000) = -Real.log (10000000 / 10001943) := by
    rw [show ((10001943 / 10000000) : ℝ) = ((10000000 / 10001943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6161_neg : (97159 / 500000000) ≤ -Real.log (9998057 / 10000000) ∧
    -Real.log (9998057 / 10000000) ≤ (194319 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 19998057)) (n := 12)
    (lo := (97159 / 500000000)) (hi := (194319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998057) = 1/(9998057 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6161 : Bounds (-194319 / 1000000000) (-97159 / 500000000) (Real.log (9998057 / 10000000)) := by
  have h := reflection_log_6161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6162_neg : (46595331 / 500000000) ≤ -Real.log (1000000 / 1097671) ∧
    -Real.log (1000000 / 1097671) ≤ (93190663 / 1000000000) := by
  have h := checkLog_sound (w := (97671 / 2097671)) (n := 12)
    (lo := (46595331 / 500000000)) (hi := (93190663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097671 / 1000000) = 1/(1000000 / 1097671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6162 : Bounds (46595331 / 500000000) (93190663 / 1000000000) (Real.log (1097671 / 1000000)) := by
  have h := reflection_log_6162_neg
  have he : Real.log (1097671 / 1000000) = -Real.log (1000000 / 1097671) := by
    rw [show ((1097671 / 1000000) : ℝ) = ((1000000 / 1097671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6163_neg : (1284701 / 12500000) ≤ -Real.log (902329 / 1000000) ∧
    -Real.log (902329 / 1000000) ≤ (102776081 / 1000000000) := by
  have h := checkLog_sound (w := (97671 / 1902329)) (n := 12)
    (lo := (1284701 / 12500000)) (hi := (102776081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902329) = 1/(902329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6163 : Bounds (-102776081 / 1000000000) (-1284701 / 12500000) (Real.log (902329 / 1000000)) := by
  have h := reflection_log_6163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6164_neg : (93413837 / 1000000000) ≤ -Real.log (250000 / 274479) ∧
    -Real.log (250000 / 274479) ≤ (46706919 / 500000000) := by
  have h := checkLog_sound (w := (24479 / 524479)) (n := 12)
    (lo := (93413837 / 1000000000)) (hi := (46706919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274479 / 250000) = 1/(250000 / 274479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6164 : Bounds (93413837 / 1000000000) (46706919 / 500000000) (Real.log (274479 / 250000)) := by
  have h := reflection_log_6164_neg
  have he : Real.log (274479 / 250000) = -Real.log (250000 / 274479) := by
    rw [show ((274479 / 250000) : ℝ) = ((250000 / 274479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6165_neg : (25761909 / 250000000) ≤ -Real.log (225521 / 250000) ∧
    -Real.log (225521 / 250000) ≤ (103047637 / 1000000000) := by
  have h := checkLog_sound (w := (24479 / 475521)) (n := 12)
    (lo := (25761909 / 250000000)) (hi := (103047637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225521) = 1/(225521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6165 : Bounds (-103047637 / 1000000000) (-25761909 / 250000000) (Real.log (225521 / 250000)) := by
  have h := reflection_log_6165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6166_neg : (9633799 / 1000000000) ≤ -Real.log (61900778559 / 62500000000) ∧
    -Real.log (61900778559 / 62500000000) ≤ (48169 / 5000000) := by
  have h := checkLog_sound (w := (599221441 / 124400778559)) (n := 12)
    (lo := (9633799 / 1000000000)) (hi := (48169 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61900778559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61900778559) = 1/(61900778559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6166 : Bounds (-48169 / 5000000) (-9633799 / 1000000000) (Real.log (61900778559 / 62500000000)) := by
  have h := reflection_log_6166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6167_neg : (9585417 / 1000000000) ≤ -Real.log (990460375759 / 1000000000000) ∧
    -Real.log (990460375759 / 1000000000000) ≤ (4792709 / 500000000) := by
  have h := checkLog_sound (w := (9539624241 / 1990460375759)) (n := 12)
    (lo := (9585417 / 1000000000)) (hi := (4792709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990460375759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990460375759) = 1/(990460375759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6167 : Bounds (-4792709 / 500000000) (-9585417 / 1000000000) (Real.log (990460375759 / 1000000000000)) := by
  have h := reflection_log_6167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6168_neg : (97983371 / 500000000) ≤ -Real.log (500000000000 / 608243223923) ∧
    -Real.log (500000000000 / 608243223923) ≤ (195966743 / 1000000000) := by
  have h := checkLog_sound (w := (108243223923 / 1108243223923)) (n := 12)
    (lo := (97983371 / 500000000)) (hi := (195966743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608243223923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608243223923 / 500000000000) = 1/(500000000000 / 608243223923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6168 : Bounds (97983371 / 500000000) (195966743 / 1000000000) (Real.log (608243223923 / 500000000000)) := by
  have h := reflection_log_6168_neg
  have he : Real.log (608243223923 / 500000000000) = -Real.log (500000000000 / 608243223923) := by
    rw [show ((608243223923 / 500000000000) : ℝ) = ((500000000000 / 608243223923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6169_neg : (98230737 / 500000000) ≤ -Real.log (100000000000 / 121708843079) ∧
    -Real.log (100000000000 / 121708843079) ≤ (7858459 / 40000000) := by
  have h := checkLog_sound (w := (21708843079 / 221708843079)) (n := 12)
    (lo := (98230737 / 500000000)) (hi := (7858459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121708843079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121708843079 / 100000000000) = 1/(100000000000 / 121708843079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6169 : Bounds (98230737 / 500000000) (7858459 / 40000000) (Real.log (121708843079 / 100000000000)) := by
  have h := reflection_log_6169_neg
  have he : Real.log (121708843079 / 100000000000) = -Real.log (100000000000 / 121708843079) := by
    rw [show ((121708843079 / 100000000000) : ℝ) = ((100000000000 / 121708843079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6170_neg : (393396211 / 1000000000) ≤ -Real.log (250000000000 / 370501365103) ∧
    -Real.log (250000000000 / 370501365103) ≤ (98349053 / 250000000) := by
  have h := checkLog_sound (w := (120501365103 / 620501365103)) (n := 12)
    (lo := (393396211 / 1000000000)) (hi := (98349053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370501365103 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370501365103 / 250000000000) = 1/(250000000000 / 370501365103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6170 : Bounds (393396211 / 1000000000) (98349053 / 250000000) (Real.log (370501365103 / 250000000000)) := by
  have h := reflection_log_6170_neg
  have he : Real.log (370501365103 / 250000000000) = -Real.log (250000000000 / 370501365103) := by
    rw [show ((370501365103 / 250000000000) : ℝ) = ((250000000000 / 370501365103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6171_neg : (393604053 / 1000000000) ≤ -Real.log (500000000000 / 741156758099) ∧
    -Real.log (500000000000 / 741156758099) ≤ (196802027 / 500000000) := by
  have h := checkLog_sound (w := (241156758099 / 1241156758099)) (n := 12)
    (lo := (393604053 / 1000000000)) (hi := (196802027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741156758099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741156758099 / 500000000000) = 1/(500000000000 / 741156758099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6171 : Bounds (393604053 / 1000000000) (196802027 / 500000000) (Real.log (741156758099 / 500000000000)) := by
  have h := reflection_log_6171_neg
  have he : Real.log (741156758099 / 500000000000) = -Real.log (500000000000 / 741156758099) := by
    rw [show ((741156758099 / 500000000000) : ℝ) = ((500000000000 / 741156758099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6172_neg : (177643967 / 1000000000) ≤ -Real.log (1250 / 1493) ∧
    -Real.log (1250 / 1493) ≤ (2775687 / 15625000) := by
  have h := checkLog_sound (w := (243 / 2743)) (n := 12)
    (lo := (177643967 / 1000000000)) (hi := (2775687 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1250) = 1/(1250 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6172 : Bounds (177643967 / 1000000000) (2775687 / 15625000) (Real.log (1493 / 1250)) := by
  have h := reflection_log_6172_neg
  have he : Real.log (1493 / 1250) = -Real.log (1250 / 1493) := by
    rw [show ((1493 / 1250) : ℝ) = ((1250 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6173_neg : (216167937 / 1000000000) ≤ -Real.log (1007 / 1250) ∧
    -Real.log (1007 / 1250) ≤ (108083969 / 500000000) := by
  have h := checkLog_sound (w := (243 / 2257)) (n := 12)
    (lo := (216167937 / 1000000000)) (hi := (108083969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1007) = 1/(1007 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6173 : Bounds (-108083969 / 500000000) (-216167937 / 1000000000) (Real.log (1007 / 1250)) := by
  have h := reflection_log_6173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6174_neg : (194381 / 1000000000) ≤ -Real.log (1250000 / 1250243) ∧
    -Real.log (1250000 / 1250243) ≤ (97191 / 500000000) := by
  have h := checkLog_sound (w := (243 / 2500243)) (n := 12)
    (lo := (194381 / 1000000000)) (hi := (97191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250243 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250243 / 1250000) = 1/(1250000 / 1250243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6174 : Bounds (194381 / 1000000000) (97191 / 500000000) (Real.log (1250243 / 1250000)) := by
  have h := reflection_log_6174_neg
  have he : Real.log (1250243 / 1250000) = -Real.log (1250000 / 1250243) := by
    rw [show ((1250243 / 1250000) : ℝ) = ((1250000 / 1250243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6175_neg : (97209 / 500000000) ≤ -Real.log (1249757 / 1250000) ∧
    -Real.log (1249757 / 1250000) ≤ (194419 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2499757)) (n := 12)
    (lo := (97209 / 500000000)) (hi := (194419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249757) = 1/(1249757 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6175 : Bounds (-194419 / 1000000000) (-97209 / 500000000) (Real.log (1249757 / 1250000)) := by
  have h := reflection_log_6175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6176_neg : (93237123 / 1000000000) ≤ -Real.log (500000 / 548861) ∧
    -Real.log (500000 / 548861) ≤ (23309281 / 250000000) := by
  have h := checkLog_sound (w := (48861 / 1048861)) (n := 12)
    (lo := (93237123 / 1000000000)) (hi := (23309281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548861 / 500000) = 1/(500000 / 548861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6176 : Bounds (93237123 / 1000000000) (23309281 / 250000000) (Real.log (548861 / 500000)) := by
  have h := reflection_log_6176_neg
  have he : Real.log (548861 / 500000) = -Real.log (500000 / 548861) := by
    rw [show ((548861 / 500000) : ℝ) = ((500000 / 548861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6177_neg : (51416301 / 500000000) ≤ -Real.log (451139 / 500000) ∧
    -Real.log (451139 / 500000) ≤ (102832603 / 1000000000) := by
  have h := checkLog_sound (w := (48861 / 951139)) (n := 12)
    (lo := (51416301 / 500000000)) (hi := (102832603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451139) = 1/(451139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6177 : Bounds (-102832603 / 1000000000) (-51416301 / 500000000) (Real.log (451139 / 500000)) := by
  have h := reflection_log_6177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6178_neg : (93460287 / 1000000000) ≤ -Real.log (1000000 / 1097967) ∧
    -Real.log (1000000 / 1097967) ≤ (1460317 / 15625000) := by
  have h := checkLog_sound (w := (97967 / 2097967)) (n := 12)
    (lo := (93460287 / 1000000000)) (hi := (1460317 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097967 / 1000000) = 1/(1000000 / 1097967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6178 : Bounds (93460287 / 1000000000) (1460317 / 15625000) (Real.log (1097967 / 1000000)) := by
  have h := reflection_log_6178_neg
  have he : Real.log (1097967 / 1000000) = -Real.log (1000000 / 1097967) := by
    rw [show ((1097967 / 1000000) : ℝ) = ((1000000 / 1097967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6179_neg : (51552087 / 500000000) ≤ -Real.log (902033 / 1000000) ∧
    -Real.log (902033 / 1000000) ≤ (4124167 / 40000000) := by
  have h := checkLog_sound (w := (97967 / 1902033)) (n := 12)
    (lo := (51552087 / 500000000)) (hi := (4124167 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902033) = 1/(902033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6179 : Bounds (-4124167 / 40000000) (-51552087 / 500000000) (Real.log (902033 / 1000000)) := by
  have h := reflection_log_6179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6180_neg : (4821943 / 500000000) ≤ -Real.log (990402466911 / 1000000000000) ∧
    -Real.log (990402466911 / 1000000000000) ≤ (9643887 / 1000000000) := by
  have h := checkLog_sound (w := (9597533089 / 1990402466911)) (n := 12)
    (lo := (4821943 / 500000000)) (hi := (9643887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990402466911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990402466911) = 1/(990402466911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6180 : Bounds (-9643887 / 1000000000) (-4821943 / 500000000) (Real.log (990402466911 / 1000000000000)) := by
  have h := reflection_log_6180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6181_neg : (4797739 / 500000000) ≤ -Real.log (247612602679 / 250000000000) ∧
    -Real.log (247612602679 / 250000000000) ≤ (9595479 / 1000000000) := by
  have h := checkLog_sound (w := (2387397321 / 497612602679)) (n := 12)
    (lo := (4797739 / 500000000)) (hi := (9595479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247612602679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247612602679) = 1/(247612602679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6181 : Bounds (-9595479 / 1000000000) (-4797739 / 500000000) (Real.log (247612602679 / 250000000000)) := by
  have h := reflection_log_6181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6182_neg : (7842789 / 40000000) ≤ -Real.log (500000000000 / 608305865819) ∧
    -Real.log (500000000000 / 608305865819) ≤ (98034863 / 500000000) := by
  have h := checkLog_sound (w := (108305865819 / 1108305865819)) (n := 12)
    (lo := (7842789 / 40000000)) (hi := (98034863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608305865819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608305865819 / 500000000000) = 1/(500000000000 / 608305865819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6182 : Bounds (7842789 / 40000000) (98034863 / 500000000) (Real.log (608305865819 / 500000000000)) := by
  have h := reflection_log_6182_neg
  have he : Real.log (608305865819 / 500000000000) = -Real.log (500000000000 / 608305865819) := by
    rw [show ((608305865819 / 500000000000) : ℝ) = ((500000000000 / 608305865819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6183_neg : (98282231 / 500000000) ≤ -Real.log (500000000000 / 608606891323) ∧
    -Real.log (500000000000 / 608606891323) ≤ (196564463 / 1000000000) := by
  have h := checkLog_sound (w := (108606891323 / 1108606891323)) (n := 12)
    (lo := (98282231 / 500000000)) (hi := (196564463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608606891323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608606891323 / 500000000000) = 1/(500000000000 / 608606891323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6183 : Bounds (98282231 / 500000000) (196564463 / 1000000000) (Real.log (608606891323 / 500000000000)) := by
  have h := reflection_log_6183_neg
  have he : Real.log (608606891323 / 500000000000) = -Real.log (500000000000 / 608606891323) := by
    rw [show ((608606891323 / 500000000000) : ℝ) = ((500000000000 / 608606891323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6184_neg : (393604053 / 1000000000) ≤ -Real.log (250000000000 / 370578379049) ∧
    -Real.log (250000000000 / 370578379049) ≤ (196802027 / 500000000) := by
  have h := checkLog_sound (w := (120578379049 / 620578379049)) (n := 12)
    (lo := (393604053 / 1000000000)) (hi := (196802027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370578379049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370578379049 / 250000000000) = 1/(250000000000 / 370578379049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6184 : Bounds (393604053 / 1000000000) (196802027 / 500000000) (Real.log (370578379049 / 250000000000)) := by
  have h := reflection_log_6184_neg
  have he : Real.log (370578379049 / 250000000000) = -Real.log (250000000000 / 370578379049) := by
    rw [show ((370578379049 / 250000000000) : ℝ) = ((250000000000 / 370578379049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6185_neg : (6153311 / 15625000) ≤ -Real.log (500000000000 / 741310824231) ∧
    -Real.log (500000000000 / 741310824231) ≤ (78762381 / 200000000) := by
  have h := checkLog_sound (w := (241310824231 / 1241310824231)) (n := 12)
    (lo := (6153311 / 15625000)) (hi := (78762381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741310824231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741310824231 / 500000000000) = 1/(500000000000 / 741310824231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6185 : Bounds (6153311 / 15625000) (78762381 / 200000000) (Real.log (741310824231 / 500000000000)) := by
  have h := reflection_log_6185_neg
  have he : Real.log (741310824231 / 500000000000) = -Real.log (500000000000 / 741310824231) := by
    rw [show ((741310824231 / 500000000000) : ℝ) = ((500000000000 / 741310824231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6186_neg : (177727687 / 1000000000) ≤ -Real.log (2000 / 2389) ∧
    -Real.log (2000 / 2389) ≤ (22215961 / 125000000) := by
  have h := checkLog_sound (w := (389 / 4389)) (n := 12)
    (lo := (177727687 / 1000000000)) (hi := (22215961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 2000) = 1/(2000 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6186 : Bounds (177727687 / 1000000000) (22215961 / 125000000) (Real.log (2389 / 2000)) := by
  have h := reflection_log_6186_neg
  have he : Real.log (2389 / 2000) = -Real.log (2000 / 2389) := by
    rw [show ((2389 / 2000) : ℝ) = ((2000 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6187_neg : (54073019 / 250000000) ≤ -Real.log (1611 / 2000) ∧
    -Real.log (1611 / 2000) ≤ (216292077 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 3611)) (n := 12)
    (lo := (54073019 / 250000000)) (hi := (216292077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1611) = 1/(1611 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6187 : Bounds (-216292077 / 1000000000) (-54073019 / 250000000) (Real.log (1611 / 2000)) := by
  have h := reflection_log_6187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6188_neg : (194481 / 1000000000) ≤ -Real.log (2000000 / 2000389) ∧
    -Real.log (2000000 / 2000389) ≤ (97241 / 500000000) := by
  have h := checkLog_sound (w := (389 / 4000389)) (n := 12)
    (lo := (194481 / 1000000000)) (hi := (97241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000389 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000389 / 2000000) = 1/(2000000 / 2000389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6188 : Bounds (194481 / 1000000000) (97241 / 500000000) (Real.log (2000389 / 2000000)) := by
  have h := reflection_log_6188_neg
  have he : Real.log (2000389 / 2000000) = -Real.log (2000000 / 2000389) := by
    rw [show ((2000389 / 2000000) : ℝ) = ((2000000 / 2000389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6189_neg : (97259 / 500000000) ≤ -Real.log (1999611 / 2000000) ∧
    -Real.log (1999611 / 2000000) ≤ (194519 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 3999611)) (n := 12)
    (lo := (97259 / 500000000)) (hi := (194519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999611) = 1/(1999611 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6189 : Bounds (-194519 / 1000000000) (-97259 / 500000000) (Real.log (1999611 / 2000000)) := by
  have h := reflection_log_6189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6190_neg : (46641791 / 500000000) ≤ -Real.log (1000000 / 1097773) ∧
    -Real.log (1000000 / 1097773) ≤ (93283583 / 1000000000) := by
  have h := checkLog_sound (w := (97773 / 2097773)) (n := 12)
    (lo := (46641791 / 500000000)) (hi := (93283583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097773 / 1000000) = 1/(1000000 / 1097773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6190 : Bounds (46641791 / 500000000) (93283583 / 1000000000) (Real.log (1097773 / 1000000)) := by
  have h := reflection_log_6190_neg
  have he : Real.log (1097773 / 1000000) = -Real.log (1000000 / 1097773) := by
    rw [show ((1097773 / 1000000) : ℝ) = ((1000000 / 1097773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6191_neg : (102889127 / 1000000000) ≤ -Real.log (902227 / 1000000) ∧
    -Real.log (902227 / 1000000) ≤ (12861141 / 125000000) := by
  have h := checkLog_sound (w := (97773 / 1902227)) (n := 12)
    (lo := (102889127 / 1000000000)) (hi := (12861141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902227) = 1/(902227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6191 : Bounds (-12861141 / 125000000) (-102889127 / 1000000000) (Real.log (902227 / 1000000)) := by
  have h := reflection_log_6191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6192_neg : (5844171 / 62500000) ≤ -Real.log (500000 / 549009) ∧
    -Real.log (500000 / 549009) ≤ (93506737 / 1000000000) := by
  have h := checkLog_sound (w := (49009 / 1049009)) (n := 12)
    (lo := (5844171 / 62500000)) (hi := (93506737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549009 / 500000) = 1/(500000 / 549009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6192 : Bounds (5844171 / 62500000) (93506737 / 1000000000) (Real.log (549009 / 500000)) := by
  have h := reflection_log_6192_neg
  have he : Real.log (549009 / 500000) = -Real.log (500000 / 549009) := by
    rw [show ((549009 / 500000) : ℝ) = ((500000 / 549009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6193_neg : (51580357 / 500000000) ≤ -Real.log (450991 / 500000) ∧
    -Real.log (450991 / 500000) ≤ (20632143 / 200000000) := by
  have h := checkLog_sound (w := (49009 / 950991)) (n := 12)
    (lo := (51580357 / 500000000)) (hi := (20632143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450991) = 1/(450991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6193 : Bounds (-20632143 / 200000000) (-51580357 / 500000000) (Real.log (450991 / 500000)) := by
  have h := reflection_log_6193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6194_neg : (4826989 / 500000000) ≤ -Real.log (247598117919 / 250000000000) ∧
    -Real.log (247598117919 / 250000000000) ≤ (9653979 / 1000000000) := by
  have h := checkLog_sound (w := (2401882081 / 497598117919)) (n := 12)
    (lo := (4826989 / 500000000)) (hi := (9653979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247598117919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247598117919) = 1/(247598117919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6194 : Bounds (-9653979 / 1000000000) (-4826989 / 500000000) (Real.log (247598117919 / 250000000000)) := by
  have h := reflection_log_6194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6195_neg : (1921109 / 200000000) ≤ -Real.log (990440440471 / 1000000000000) ∧
    -Real.log (990440440471 / 1000000000000) ≤ (4802773 / 500000000) := by
  have h := checkLog_sound (w := (9559559529 / 1990440440471)) (n := 12)
    (lo := (1921109 / 200000000)) (hi := (4802773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990440440471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990440440471) = 1/(990440440471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6195 : Bounds (-4802773 / 500000000) (-1921109 / 200000000) (Real.log (990440440471 / 1000000000000)) := by
  have h := reflection_log_6195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6196_neg : (196172709 / 1000000000) ≤ -Real.log (500000000000 / 608368514797) ∧
    -Real.log (500000000000 / 608368514797) ≤ (19617271 / 100000000) := by
  have h := checkLog_sound (w := (108368514797 / 1108368514797)) (n := 12)
    (lo := (196172709 / 1000000000)) (hi := (19617271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608368514797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608368514797 / 500000000000) = 1/(500000000000 / 608368514797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6196 : Bounds (196172709 / 1000000000) (19617271 / 100000000) (Real.log (608368514797 / 500000000000)) := by
  have h := reflection_log_6196_neg
  have he : Real.log (608368514797 / 500000000000) = -Real.log (500000000000 / 608368514797) := by
    rw [show ((608368514797 / 500000000000) : ℝ) = ((500000000000 / 608368514797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6197_neg : (196667451 / 1000000000) ≤ -Real.log (250000000000 / 304334787169) ∧
    -Real.log (250000000000 / 304334787169) ≤ (49166863 / 250000000) := by
  have h := checkLog_sound (w := (54334787169 / 554334787169)) (n := 12)
    (lo := (196667451 / 1000000000)) (hi := (49166863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304334787169 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304334787169 / 250000000000) = 1/(250000000000 / 304334787169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6197 : Bounds (196667451 / 1000000000) (49166863 / 250000000) (Real.log (304334787169 / 250000000000)) := by
  have h := reflection_log_6197_neg
  have he : Real.log (304334787169 / 250000000000) = -Real.log (250000000000 / 304334787169) := by
    rw [show ((304334787169 / 250000000000) : ℝ) = ((250000000000 / 304334787169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6198_neg : (6153311 / 15625000) ≤ -Real.log (50000000000 / 74131082423) ∧
    -Real.log (50000000000 / 74131082423) ≤ (78762381 / 200000000) := by
  have h := checkLog_sound (w := (24131082423 / 124131082423)) (n := 12)
    (lo := (6153311 / 15625000)) (hi := (78762381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74131082423 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74131082423 / 50000000000) = 1/(50000000000 / 74131082423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6198 : Bounds (6153311 / 15625000) (78762381 / 200000000) (Real.log (74131082423 / 50000000000)) := by
  have h := reflection_log_6198_neg
  have he : Real.log (74131082423 / 50000000000) = -Real.log (50000000000 / 74131082423) := by
    rw [show ((74131082423 / 50000000000) : ℝ) = ((50000000000 / 74131082423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6199_neg : (98504941 / 250000000) ≤ -Real.log (62500000000 / 92683116077) ∧
    -Real.log (62500000000 / 92683116077) ≤ (78803953 / 200000000) := by
  have h := checkLog_sound (w := (30183116077 / 155183116077)) (n := 12)
    (lo := (98504941 / 250000000)) (hi := (78803953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92683116077 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92683116077 / 62500000000) = 1/(62500000000 / 92683116077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6199 : Bounds (98504941 / 250000000) (78803953 / 200000000) (Real.log (92683116077 / 62500000000)) := by
  have h := reflection_log_6199_neg
  have he : Real.log (92683116077 / 62500000000) = -Real.log (62500000000 / 92683116077) := by
    rw [show ((92683116077 / 62500000000) : ℝ) = ((62500000000 / 92683116077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6200_neg : (177811401 / 1000000000) ≤ -Real.log (5000 / 5973) ∧
    -Real.log (5000 / 5973) ≤ (88905701 / 500000000) := by
  have h := checkLog_sound (w := (973 / 10973)) (n := 12)
    (lo := (177811401 / 1000000000)) (hi := (88905701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5973 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5973 / 5000) = 1/(5000 / 5973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6200 : Bounds (177811401 / 1000000000) (88905701 / 500000000) (Real.log (5973 / 5000)) := by
  have h := reflection_log_6200_neg
  have he : Real.log (5973 / 5000) = -Real.log (5000 / 5973) := by
    rw [show ((5973 / 5000) : ℝ) = ((5000 / 5973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6201_neg : (21641623 / 100000000) ≤ -Real.log (4027 / 5000) ∧
    -Real.log (4027 / 5000) ≤ (216416231 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 9027)) (n := 12)
    (lo := (21641623 / 100000000)) (hi := (216416231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4027) = 1/(4027 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6201 : Bounds (-216416231 / 1000000000) (-21641623 / 100000000) (Real.log (4027 / 5000)) := by
  have h := reflection_log_6201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6202_neg : (194581 / 1000000000) ≤ -Real.log (5000000 / 5000973) ∧
    -Real.log (5000000 / 5000973) ≤ (97291 / 500000000) := by
  have h := checkLog_sound (w := (973 / 10000973)) (n := 12)
    (lo := (194581 / 1000000000)) (hi := (97291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000973 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000973 / 5000000) = 1/(5000000 / 5000973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6202 : Bounds (194581 / 1000000000) (97291 / 500000000) (Real.log (5000973 / 5000000)) := by
  have h := reflection_log_6202_neg
  have he : Real.log (5000973 / 5000000) = -Real.log (5000000 / 5000973) := by
    rw [show ((5000973 / 5000000) : ℝ) = ((5000000 / 5000973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6203_neg : (97309 / 500000000) ≤ -Real.log (4999027 / 5000000) ∧
    -Real.log (4999027 / 5000000) ≤ (194619 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 9999027)) (n := 12)
    (lo := (97309 / 500000000)) (hi := (194619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999027) = 1/(4999027 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6203 : Bounds (-194619 / 1000000000) (-97309 / 500000000) (Real.log (4999027 / 5000000)) := by
  have h := reflection_log_6203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6204_neg : (46665019 / 500000000) ≤ -Real.log (31250 / 34307) ∧
    -Real.log (31250 / 34307) ≤ (93330039 / 1000000000) := by
  have h := checkLog_sound (w := (3057 / 65557)) (n := 12)
    (lo := (46665019 / 500000000)) (hi := (93330039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34307 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34307 / 31250) = 1/(31250 / 34307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6204 : Bounds (46665019 / 500000000) (93330039 / 1000000000) (Real.log (34307 / 31250)) := by
  have h := reflection_log_6204_neg
  have he : Real.log (34307 / 31250) = -Real.log (31250 / 34307) := by
    rw [show ((34307 / 31250) : ℝ) = ((31250 / 34307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6205_neg : (12868207 / 125000000) ≤ -Real.log (28193 / 31250) ∧
    -Real.log (28193 / 31250) ≤ (102945657 / 1000000000) := by
  have h := checkLog_sound (w := (3057 / 59443)) (n := 12)
    (lo := (12868207 / 125000000)) (hi := (102945657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28193) = 1/(28193 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6205 : Bounds (-102945657 / 1000000000) (-12868207 / 125000000) (Real.log (28193 / 31250)) := by
  have h := reflection_log_6205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6206_neg : (46776591 / 500000000) ≤ -Real.log (1000000 / 1098069) ∧
    -Real.log (1000000 / 1098069) ≤ (93553183 / 1000000000) := by
  have h := checkLog_sound (w := (98069 / 2098069)) (n := 12)
    (lo := (46776591 / 500000000)) (hi := (93553183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098069 / 1000000) = 1/(1000000 / 1098069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6206 : Bounds (46776591 / 500000000) (93553183 / 1000000000) (Real.log (1098069 / 1000000)) := by
  have h := reflection_log_6206_neg
  have he : Real.log (1098069 / 1000000) = -Real.log (1000000 / 1098069) := by
    rw [show ((1098069 / 1000000) : ℝ) = ((1000000 / 1098069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6207_neg : (51608629 / 500000000) ≤ -Real.log (901931 / 1000000) ∧
    -Real.log (901931 / 1000000) ≤ (103217259 / 1000000000) := by
  have h := checkLog_sound (w := (98069 / 1901931)) (n := 12)
    (lo := (51608629 / 500000000)) (hi := (103217259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901931) = 1/(901931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6207 : Bounds (-103217259 / 1000000000) (-51608629 / 500000000) (Real.log (901931 / 1000000)) := by
  have h := reflection_log_6207_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
