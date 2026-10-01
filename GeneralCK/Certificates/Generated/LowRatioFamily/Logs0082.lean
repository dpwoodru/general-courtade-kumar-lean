import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5248_neg : (21512857 / 125000000) ≤ -Real.log (5000 / 5939) ∧
    -Real.log (5000 / 5939) ≤ (172102857 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 10939)) (n := 12)
    (lo := (21512857 / 125000000)) (hi := (172102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5939 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5939 / 5000) = 1/(5000 / 5939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5248 : Bounds (21512857 / 125000000) (172102857 / 1000000000) (Real.log (5939 / 5000)) := by
  have h := reflection_log_5248_neg
  have he : Real.log (5939 / 5000) = -Real.log (5000 / 5939) := by
    rw [show ((5939 / 5000) : ℝ) = ((5000 / 5939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5249_neg : (208008663 / 1000000000) ≤ -Real.log (4061 / 5000) ∧
    -Real.log (4061 / 5000) ≤ (26001083 / 125000000) := by
  have h := checkLog_sound (w := (939 / 9061)) (n := 12)
    (lo := (208008663 / 1000000000)) (hi := (26001083 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4061) = 1/(4061 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5249 : Bounds (-26001083 / 125000000) (-208008663 / 1000000000) (Real.log (4061 / 5000)) := by
  have h := reflection_log_5249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5250_neg : (93891 / 500000000) ≤ -Real.log (5000000 / 5000939) ∧
    -Real.log (5000000 / 5000939) ≤ (187783 / 1000000000) := by
  have h := checkLog_sound (w := (939 / 10000939)) (n := 12)
    (lo := (93891 / 500000000)) (hi := (187783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000939 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000939 / 5000000) = 1/(5000000 / 5000939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5250 : Bounds (93891 / 500000000) (187783 / 1000000000) (Real.log (5000939 / 5000000)) := by
  have h := reflection_log_5250_neg
  have he : Real.log (5000939 / 5000000) = -Real.log (5000000 / 5000939) := by
    rw [show ((5000939 / 5000000) : ℝ) = ((5000000 / 5000939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5251_neg : (187817 / 1000000000) ≤ -Real.log (4999061 / 5000000) ∧
    -Real.log (4999061 / 5000000) ≤ (93909 / 500000000) := by
  have h := checkLog_sound (w := (939 / 9999061)) (n := 12)
    (lo := (187817 / 1000000000)) (hi := (93909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999061) = 1/(4999061 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5251 : Bounds (-93909 / 500000000) (-187817 / 1000000000) (Real.log (4999061 / 5000000)) := by
  have h := reflection_log_5251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5252_neg : (90168803 / 1000000000) ≤ -Real.log (1000000 / 1094359) ∧
    -Real.log (1000000 / 1094359) ≤ (22542201 / 250000000) := by
  have h := checkLog_sound (w := (94359 / 2094359)) (n := 12)
    (lo := (90168803 / 1000000000)) (hi := (22542201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094359 / 1000000) = 1/(1000000 / 1094359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5252 : Bounds (90168803 / 1000000000) (22542201 / 250000000) (Real.log (1094359 / 1000000)) := by
  have h := reflection_log_5252_neg
  have he : Real.log (1094359 / 1000000) = -Real.log (1000000 / 1094359) := by
    rw [show ((1094359 / 1000000) : ℝ) = ((1000000 / 1094359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5253_neg : (49556149 / 500000000) ≤ -Real.log (905641 / 1000000) ∧
    -Real.log (905641 / 1000000) ≤ (99112299 / 1000000000) := by
  have h := checkLog_sound (w := (94359 / 1905641)) (n := 12)
    (lo := (49556149 / 500000000)) (hi := (99112299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905641) = 1/(905641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5253 : Bounds (-99112299 / 1000000000) (-49556149 / 500000000) (Real.log (905641 / 1000000)) := by
  have h := reflection_log_5253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5254_neg : (45193129 / 500000000) ≤ -Real.log (1000000 / 1094597) ∧
    -Real.log (1000000 / 1094597) ≤ (90386259 / 1000000000) := by
  have h := checkLog_sound (w := (94597 / 2094597)) (n := 12)
    (lo := (45193129 / 500000000)) (hi := (90386259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094597 / 1000000) = 1/(1000000 / 1094597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5254 : Bounds (45193129 / 500000000) (90386259 / 1000000000) (Real.log (1094597 / 1000000)) := by
  have h := reflection_log_5254_neg
  have he : Real.log (1094597 / 1000000) = -Real.log (1000000 / 1094597) := by
    rw [show ((1094597 / 1000000) : ℝ) = ((1000000 / 1094597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5255_neg : (9937513 / 100000000) ≤ -Real.log (905403 / 1000000) ∧
    -Real.log (905403 / 1000000) ≤ (99375131 / 1000000000) := by
  have h := checkLog_sound (w := (94597 / 1905403)) (n := 12)
    (lo := (9937513 / 100000000)) (hi := (99375131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905403) = 1/(905403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5255 : Bounds (-99375131 / 1000000000) (-9937513 / 100000000) (Real.log (905403 / 1000000)) := by
  have h := reflection_log_5255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5256_neg : (8988871 / 1000000000) ≤ -Real.log (991051407591 / 1000000000000) ∧
    -Real.log (991051407591 / 1000000000000) ≤ (1123609 / 125000000) := by
  have h := checkLog_sound (w := (8948592409 / 1991051407591)) (n := 12)
    (lo := (8988871 / 1000000000)) (hi := (1123609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991051407591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991051407591) = 1/(991051407591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5256 : Bounds (-1123609 / 125000000) (-8988871 / 1000000000) (Real.log (991051407591 / 1000000000000)) := by
  have h := reflection_log_5256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5257_neg : (4471747 / 500000000) ≤ -Real.log (991096379119 / 1000000000000) ∧
    -Real.log (991096379119 / 1000000000000) ≤ (1788699 / 200000000) := by
  have h := checkLog_sound (w := (8903620881 / 1991096379119)) (n := 12)
    (lo := (4471747 / 500000000)) (hi := (1788699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991096379119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991096379119) = 1/(991096379119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5257 : Bounds (-1788699 / 200000000) (-4471747 / 500000000) (Real.log (991096379119 / 1000000000000)) := by
  have h := reflection_log_5257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5258_neg : (94640551 / 500000000) ≤ -Real.log (250000000000 / 302095145869) ∧
    -Real.log (250000000000 / 302095145869) ≤ (189281103 / 1000000000) := by
  have h := checkLog_sound (w := (52095145869 / 552095145869)) (n := 12)
    (lo := (94640551 / 500000000)) (hi := (189281103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302095145869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302095145869 / 250000000000) = 1/(250000000000 / 302095145869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5258 : Bounds (94640551 / 500000000) (189281103 / 1000000000) (Real.log (302095145869 / 250000000000)) := by
  have h := reflection_log_5258_neg
  have he : Real.log (302095145869 / 250000000000) = -Real.log (250000000000 / 302095145869) := by
    rw [show ((302095145869 / 250000000000) : ℝ) = ((250000000000 / 302095145869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5259_neg : (189761389 / 1000000000) ≤ -Real.log (62500000000 / 75560068279) ∧
    -Real.log (62500000000 / 75560068279) ≤ (18976139 / 100000000) := by
  have h := checkLog_sound (w := (13060068279 / 138060068279)) (n := 12)
    (lo := (189761389 / 1000000000)) (hi := (18976139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75560068279 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75560068279 / 62500000000) = 1/(62500000000 / 75560068279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5259 : Bounds (189761389 / 1000000000) (18976139 / 100000000) (Real.log (75560068279 / 62500000000)) := by
  have h := reflection_log_5259_neg
  have he : Real.log (75560068279 / 62500000000) = -Real.log (62500000000 / 75560068279) := by
    rw [show ((75560068279 / 62500000000) : ℝ) = ((62500000000 / 75560068279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5260_neg : (94976053 / 250000000) ≤ -Real.log (500000000000 / 731072263941) ∧
    -Real.log (500000000000 / 731072263941) ≤ (379904213 / 1000000000) := by
  have h := checkLog_sound (w := (231072263941 / 1231072263941)) (n := 12)
    (lo := (94976053 / 250000000)) (hi := (379904213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731072263941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731072263941 / 500000000000) = 1/(500000000000 / 731072263941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5260 : Bounds (94976053 / 250000000) (379904213 / 1000000000) (Real.log (731072263941 / 500000000000)) := by
  have h := reflection_log_5260_neg
  have he : Real.log (731072263941 / 500000000000) = -Real.log (500000000000 / 731072263941) := by
    rw [show ((731072263941 / 500000000000) : ℝ) = ((500000000000 / 731072263941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5261_neg : (2375697 / 6250000) ≤ -Real.log (250000000000 / 365611918247) ∧
    -Real.log (250000000000 / 365611918247) ≤ (380111521 / 1000000000) := by
  have h := checkLog_sound (w := (115611918247 / 615611918247)) (n := 12)
    (lo := (2375697 / 6250000)) (hi := (380111521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365611918247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365611918247 / 250000000000) = 1/(250000000000 / 365611918247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5261 : Bounds (2375697 / 6250000) (380111521 / 1000000000) (Real.log (365611918247 / 250000000000)) := by
  have h := reflection_log_5261_neg
  have he : Real.log (365611918247 / 250000000000) = -Real.log (250000000000 / 365611918247) := by
    rw [show ((365611918247 / 250000000000) : ℝ) = ((250000000000 / 365611918247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5262_neg : (86093521 / 500000000) ≤ -Real.log (10000 / 11879) ∧
    -Real.log (10000 / 11879) ≤ (172187043 / 1000000000) := by
  have h := checkLog_sound (w := (1879 / 21879)) (n := 12)
    (lo := (86093521 / 500000000)) (hi := (172187043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11879 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11879 / 10000) = 1/(10000 / 11879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5262 : Bounds (86093521 / 500000000) (172187043 / 1000000000) (Real.log (11879 / 10000)) := by
  have h := reflection_log_5262_neg
  have he : Real.log (11879 / 10000) = -Real.log (10000 / 11879) := by
    rw [show ((11879 / 10000) : ℝ) = ((10000 / 11879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5263_neg : (208131793 / 1000000000) ≤ -Real.log (8121 / 10000) ∧
    -Real.log (8121 / 10000) ≤ (104065897 / 500000000) := by
  have h := checkLog_sound (w := (1879 / 18121)) (n := 12)
    (lo := (208131793 / 1000000000)) (hi := (104065897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8121) = 1/(8121 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5263 : Bounds (-104065897 / 500000000) (-208131793 / 1000000000) (Real.log (8121 / 10000)) := by
  have h := reflection_log_5263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5264_neg : (93941 / 500000000) ≤ -Real.log (10000000 / 10001879) ∧
    -Real.log (10000000 / 10001879) ≤ (187883 / 1000000000) := by
  have h := checkLog_sound (w := (1879 / 20001879)) (n := 12)
    (lo := (93941 / 500000000)) (hi := (187883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001879 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001879 / 10000000) = 1/(10000000 / 10001879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5264 : Bounds (93941 / 500000000) (187883 / 1000000000) (Real.log (10001879 / 10000000)) := by
  have h := reflection_log_5264_neg
  have he : Real.log (10001879 / 10000000) = -Real.log (10000000 / 10001879) := by
    rw [show ((10001879 / 10000000) : ℝ) = ((10000000 / 10001879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5265_neg : (187917 / 1000000000) ≤ -Real.log (9998121 / 10000000) ∧
    -Real.log (9998121 / 10000000) ≤ (93959 / 500000000) := by
  have h := checkLog_sound (w := (1879 / 19998121)) (n := 12)
    (lo := (187917 / 1000000000)) (hi := (93959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998121) = 1/(9998121 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5265 : Bounds (-93959 / 500000000) (-187917 / 1000000000) (Real.log (9998121 / 10000000)) := by
  have h := reflection_log_5265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5266_neg : (18043081 / 200000000) ≤ -Real.log (100000 / 109441) ∧
    -Real.log (100000 / 109441) ≤ (45107703 / 500000000) := by
  have h := checkLog_sound (w := (9441 / 209441)) (n := 12)
    (lo := (18043081 / 200000000)) (hi := (45107703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109441 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109441 / 100000) = 1/(100000 / 109441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5266 : Bounds (18043081 / 200000000) (45107703 / 500000000) (Real.log (109441 / 100000)) := by
  have h := reflection_log_5266_neg
  have he : Real.log (109441 / 100000) = -Real.log (100000 / 109441) := by
    rw [show ((109441 / 100000) : ℝ) = ((100000 / 109441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5267_neg : (99168613 / 1000000000) ≤ -Real.log (90559 / 100000) ∧
    -Real.log (90559 / 100000) ≤ (49584307 / 500000000) := by
  have h := checkLog_sound (w := (9441 / 190559)) (n := 12)
    (lo := (99168613 / 1000000000)) (hi := (49584307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90559) = 1/(90559 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5267 : Bounds (-49584307 / 500000000) (-99168613 / 1000000000) (Real.log (90559 / 100000)) := by
  have h := reflection_log_5267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5268_neg : (1808657 / 20000000) ≤ -Real.log (125000 / 136831) ∧
    -Real.log (125000 / 136831) ≤ (90432851 / 1000000000) := by
  have h := checkLog_sound (w := (11831 / 261831)) (n := 12)
    (lo := (1808657 / 20000000)) (hi := (90432851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136831 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136831 / 125000) = 1/(125000 / 136831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5268 : Bounds (1808657 / 20000000) (90432851 / 1000000000) (Real.log (136831 / 125000)) := by
  have h := reflection_log_5268_neg
  have he : Real.log (136831 / 125000) = -Real.log (125000 / 136831) := by
    rw [show ((136831 / 125000) : ℝ) = ((125000 / 136831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5269_neg : (4971573 / 50000000) ≤ -Real.log (113169 / 125000) ∧
    -Real.log (113169 / 125000) ≤ (99431461 / 1000000000) := by
  have h := checkLog_sound (w := (11831 / 238169)) (n := 12)
    (lo := (4971573 / 50000000)) (hi := (99431461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113169) = 1/(113169 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5269 : Bounds (-99431461 / 1000000000) (-4971573 / 50000000) (Real.log (113169 / 125000)) := by
  have h := reflection_log_5269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5270_neg : (899861 / 100000000) ≤ -Real.log (15485027439 / 15625000000) ∧
    -Real.log (15485027439 / 15625000000) ≤ (8998611 / 1000000000) := by
  have h := checkLog_sound (w := (139972561 / 31110027439)) (n := 12)
    (lo := (899861 / 100000000)) (hi := (8998611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15485027439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15485027439) = 1/(15485027439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5270 : Bounds (-8998611 / 1000000000) (-899861 / 100000000) (Real.log (15485027439 / 15625000000)) := by
  have h := reflection_log_5270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5271_neg : (1119151 / 125000000) ≤ -Real.log (9910867519 / 10000000000) ∧
    -Real.log (9910867519 / 10000000000) ≤ (8953209 / 1000000000) := by
  have h := checkLog_sound (w := (89132481 / 19910867519)) (n := 12)
    (lo := (1119151 / 125000000)) (hi := (8953209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9910867519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9910867519) = 1/(9910867519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5271 : Bounds (-8953209 / 1000000000) (-1119151 / 125000000) (Real.log (9910867519 / 10000000000)) := by
  have h := reflection_log_5271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5272_neg : (189384019 / 1000000000) ≤ -Real.log (250000000000 / 302126238143) ∧
    -Real.log (250000000000 / 302126238143) ≤ (9469201 / 50000000) := by
  have h := checkLog_sound (w := (52126238143 / 552126238143)) (n := 12)
    (lo := (189384019 / 1000000000)) (hi := (9469201 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302126238143 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302126238143 / 250000000000) = 1/(250000000000 / 302126238143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5272 : Bounds (189384019 / 1000000000) (9469201 / 50000000) (Real.log (302126238143 / 250000000000)) := by
  have h := reflection_log_5272_neg
  have he : Real.log (302126238143 / 250000000000) = -Real.log (250000000000 / 302126238143) := by
    rw [show ((302126238143 / 250000000000) : ℝ) = ((250000000000 / 302126238143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5273_neg : (189864311 / 1000000000) ≤ -Real.log (250000000000 / 302271381739) ∧
    -Real.log (250000000000 / 302271381739) ≤ (23733039 / 125000000) := by
  have h := checkLog_sound (w := (52271381739 / 552271381739)) (n := 12)
    (lo := (189864311 / 1000000000)) (hi := (23733039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302271381739 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302271381739 / 250000000000) = 1/(250000000000 / 302271381739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5273 : Bounds (189864311 / 1000000000) (23733039 / 125000000) (Real.log (302271381739 / 250000000000)) := by
  have h := reflection_log_5273_neg
  have he : Real.log (302271381739 / 250000000000) = -Real.log (250000000000 / 302271381739) := by
    rw [show ((302271381739 / 250000000000) : ℝ) = ((250000000000 / 302271381739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5274_neg : (2375697 / 6250000) ≤ -Real.log (500000000000 / 731223836493) ∧
    -Real.log (500000000000 / 731223836493) ≤ (380111521 / 1000000000) := by
  have h := checkLog_sound (w := (231223836493 / 1231223836493)) (n := 12)
    (lo := (2375697 / 6250000)) (hi := (380111521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731223836493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731223836493 / 500000000000) = 1/(500000000000 / 731223836493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5274 : Bounds (2375697 / 6250000) (380111521 / 1000000000) (Real.log (731223836493 / 500000000000)) := by
  have h := reflection_log_5274_neg
  have he : Real.log (731223836493 / 500000000000) = -Real.log (500000000000 / 731223836493) := by
    rw [show ((731223836493 / 500000000000) : ℝ) = ((500000000000 / 731223836493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5275_neg : (95079709 / 250000000) ≤ -Real.log (250000000000 / 365687723187) ∧
    -Real.log (250000000000 / 365687723187) ≤ (380318837 / 1000000000) := by
  have h := checkLog_sound (w := (115687723187 / 615687723187)) (n := 12)
    (lo := (95079709 / 250000000)) (hi := (380318837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365687723187 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365687723187 / 250000000000) = 1/(250000000000 / 365687723187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5275 : Bounds (95079709 / 250000000) (380318837 / 1000000000) (Real.log (365687723187 / 250000000000)) := by
  have h := reflection_log_5275_neg
  have he : Real.log (365687723187 / 250000000000) = -Real.log (250000000000 / 365687723187) := by
    rw [show ((365687723187 / 250000000000) : ℝ) = ((250000000000 / 365687723187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5276_neg : (8613561 / 50000000) ≤ -Real.log (250 / 297) ∧
    -Real.log (250 / 297) ≤ (172271221 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 547)) (n := 12)
    (lo := (8613561 / 50000000)) (hi := (172271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 250) = 1/(250 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5276 : Bounds (8613561 / 50000000) (172271221 / 1000000000) (Real.log (297 / 250)) := by
  have h := reflection_log_5276_neg
  have he : Real.log (297 / 250) = -Real.log (250 / 297) := by
    rw [show ((297 / 250) : ℝ) = ((250 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5277_neg : (104127469 / 500000000) ≤ -Real.log (203 / 250) ∧
    -Real.log (203 / 250) ≤ (208254939 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 453)) (n := 12)
    (lo := (104127469 / 500000000)) (hi := (208254939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 203) = 1/(203 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5277 : Bounds (-208254939 / 1000000000) (-104127469 / 500000000) (Real.log (203 / 250)) := by
  have h := reflection_log_5277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5278_neg : (93991 / 500000000) ≤ -Real.log (250000 / 250047) ∧
    -Real.log (250000 / 250047) ≤ (187983 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 500047)) (n := 12)
    (lo := (93991 / 500000000)) (hi := (187983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250047 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250047 / 250000) = 1/(250000 / 250047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5278 : Bounds (93991 / 500000000) (187983 / 1000000000) (Real.log (250047 / 250000)) := by
  have h := reflection_log_5278_neg
  have he : Real.log (250047 / 250000) = -Real.log (250000 / 250047) := by
    rw [show ((250047 / 250000) : ℝ) = ((250000 / 250047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5279_neg : (188017 / 1000000000) ≤ -Real.log (249953 / 250000) ∧
    -Real.log (249953 / 250000) ≤ (94009 / 500000000) := by
  have h := checkLog_sound (w := (47 / 499953)) (n := 12)
    (lo := (188017 / 1000000000)) (hi := (94009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249953) = 1/(249953 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5279 : Bounds (-94009 / 500000000) (-188017 / 1000000000) (Real.log (249953 / 250000)) := by
  have h := reflection_log_5279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5280_neg : (22565501 / 250000000) ≤ -Real.log (1000000 / 1094461) ∧
    -Real.log (1000000 / 1094461) ≤ (18052401 / 200000000) := by
  have h := checkLog_sound (w := (94461 / 2094461)) (n := 12)
    (lo := (22565501 / 250000000)) (hi := (18052401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094461 / 1000000) = 1/(1000000 / 1094461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5280 : Bounds (22565501 / 250000000) (18052401 / 200000000) (Real.log (1094461 / 1000000)) := by
  have h := reflection_log_5280_neg
  have he : Real.log (1094461 / 1000000) = -Real.log (1000000 / 1094461) := by
    rw [show ((1094461 / 1000000) : ℝ) = ((1000000 / 1094461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5281_neg : (24806233 / 250000000) ≤ -Real.log (905539 / 1000000) ∧
    -Real.log (905539 / 1000000) ≤ (99224933 / 1000000000) := by
  have h := checkLog_sound (w := (94461 / 1905539)) (n := 12)
    (lo := (24806233 / 250000000)) (hi := (99224933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905539) = 1/(905539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5281 : Bounds (-99224933 / 1000000000) (-24806233 / 250000000) (Real.log (905539 / 1000000)) := by
  have h := reflection_log_5281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5282_neg : (90479439 / 1000000000) ≤ -Real.log (1000000 / 1094699) ∧
    -Real.log (1000000 / 1094699) ≤ (1130993 / 12500000) := by
  have h := checkLog_sound (w := (94699 / 2094699)) (n := 12)
    (lo := (90479439 / 1000000000)) (hi := (1130993 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094699 / 1000000) = 1/(1000000 / 1094699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5282 : Bounds (90479439 / 1000000000) (1130993 / 12500000) (Real.log (1094699 / 1000000)) := by
  have h := reflection_log_5282_neg
  have he : Real.log (1094699 / 1000000) = -Real.log (1000000 / 1094699) := by
    rw [show ((1094699 / 1000000) : ℝ) = ((1000000 / 1094699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5283_neg : (99487793 / 1000000000) ≤ -Real.log (905301 / 1000000) ∧
    -Real.log (905301 / 1000000) ≤ (49743897 / 500000000) := by
  have h := checkLog_sound (w := (94699 / 1905301)) (n := 12)
    (lo := (99487793 / 1000000000)) (hi := (49743897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905301) = 1/(905301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5283 : Bounds (-49743897 / 500000000) (-99487793 / 1000000000) (Real.log (905301 / 1000000)) := by
  have h := reflection_log_5283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5284_neg : (4504177 / 500000000) ≤ -Real.log (991032099399 / 1000000000000) ∧
    -Real.log (991032099399 / 1000000000000) ≤ (1801671 / 200000000) := by
  have h := checkLog_sound (w := (8967900601 / 1991032099399)) (n := 12)
    (lo := (4504177 / 500000000)) (hi := (1801671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991032099399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991032099399) = 1/(991032099399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5284 : Bounds (-1801671 / 200000000) (-4504177 / 500000000) (Real.log (991032099399 / 1000000000000)) := by
  have h := reflection_log_5284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5285_neg : (8962927 / 1000000000) ≤ -Real.log (991077119479 / 1000000000000) ∧
    -Real.log (991077119479 / 1000000000000) ≤ (560183 / 62500000) := by
  have h := checkLog_sound (w := (8922880521 / 1991077119479)) (n := 12)
    (lo := (8962927 / 1000000000)) (hi := (560183 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991077119479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991077119479) = 1/(991077119479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5285 : Bounds (-560183 / 62500000) (-8962927 / 1000000000) (Real.log (991077119479 / 1000000000000)) := by
  have h := reflection_log_5285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5286_neg : (189486937 / 1000000000) ≤ -Real.log (250000000000 / 302157333919) ∧
    -Real.log (250000000000 / 302157333919) ≤ (94743469 / 500000000) := by
  have h := checkLog_sound (w := (52157333919 / 552157333919)) (n := 12)
    (lo := (189486937 / 1000000000)) (hi := (94743469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302157333919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302157333919 / 250000000000) = 1/(250000000000 / 302157333919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5286 : Bounds (189486937 / 1000000000) (94743469 / 500000000) (Real.log (302157333919 / 250000000000)) := by
  have h := reflection_log_5286_neg
  have he : Real.log (302157333919 / 250000000000) = -Real.log (250000000000 / 302157333919) := by
    rw [show ((302157333919 / 250000000000) : ℝ) = ((250000000000 / 302157333919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5287_neg : (189967233 / 1000000000) ≤ -Real.log (250000000000 / 302302493867) ∧
    -Real.log (250000000000 / 302302493867) ≤ (94983617 / 500000000) := by
  have h := checkLog_sound (w := (52302493867 / 552302493867)) (n := 12)
    (lo := (189967233 / 1000000000)) (hi := (94983617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302302493867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302302493867 / 250000000000) = 1/(250000000000 / 302302493867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5287 : Bounds (189967233 / 1000000000) (94983617 / 500000000) (Real.log (302302493867 / 250000000000)) := by
  have h := reflection_log_5287_neg
  have he : Real.log (302302493867 / 250000000000) = -Real.log (250000000000 / 302302493867) := by
    rw [show ((302302493867 / 250000000000) : ℝ) = ((250000000000 / 302302493867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5288_neg : (95079709 / 250000000) ≤ -Real.log (500000000000 / 731375446373) ∧
    -Real.log (500000000000 / 731375446373) ≤ (380318837 / 1000000000) := by
  have h := checkLog_sound (w := (231375446373 / 1231375446373)) (n := 12)
    (lo := (95079709 / 250000000)) (hi := (380318837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731375446373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731375446373 / 500000000000) = 1/(500000000000 / 731375446373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5288 : Bounds (95079709 / 250000000) (380318837 / 1000000000) (Real.log (731375446373 / 500000000000)) := by
  have h := reflection_log_5288_neg
  have he : Real.log (731375446373 / 500000000000) = -Real.log (500000000000 / 731375446373) := by
    rw [show ((731375446373 / 500000000000) : ℝ) = ((500000000000 / 731375446373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5289_neg : (380526159 / 1000000000) ≤ -Real.log (500000000000 / 731527093597) ∧
    -Real.log (500000000000 / 731527093597) ≤ (4756577 / 12500000) := by
  have h := checkLog_sound (w := (231527093597 / 1231527093597)) (n := 12)
    (lo := (380526159 / 1000000000)) (hi := (4756577 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731527093597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731527093597 / 500000000000) = 1/(500000000000 / 731527093597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5289 : Bounds (380526159 / 1000000000) (4756577 / 12500000) (Real.log (731527093597 / 500000000000)) := by
  have h := reflection_log_5289_neg
  have he : Real.log (731527093597 / 500000000000) = -Real.log (500000000000 / 731527093597) := by
    rw [show ((731527093597 / 500000000000) : ℝ) = ((500000000000 / 731527093597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5290_neg : (2693053 / 15625000) ≤ -Real.log (10000 / 11881) ∧
    -Real.log (10000 / 11881) ≤ (172355393 / 1000000000) := by
  have h := checkLog_sound (w := (1881 / 21881)) (n := 12)
    (lo := (2693053 / 15625000)) (hi := (172355393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11881 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11881 / 10000) = 1/(10000 / 11881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5290 : Bounds (2693053 / 15625000) (172355393 / 1000000000) (Real.log (11881 / 10000)) := by
  have h := reflection_log_5290_neg
  have he : Real.log (11881 / 10000) = -Real.log (10000 / 11881) := by
    rw [show ((11881 / 10000) : ℝ) = ((10000 / 11881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5291_neg : (208378099 / 1000000000) ≤ -Real.log (8119 / 10000) ∧
    -Real.log (8119 / 10000) ≤ (2083781 / 10000000) := by
  have h := checkLog_sound (w := (1881 / 18119)) (n := 12)
    (lo := (208378099 / 1000000000)) (hi := (2083781 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8119) = 1/(8119 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5291 : Bounds (-2083781 / 10000000) (-208378099 / 1000000000) (Real.log (8119 / 10000)) := by
  have h := reflection_log_5291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5292_neg : (94041 / 500000000) ≤ -Real.log (10000000 / 10001881) ∧
    -Real.log (10000000 / 10001881) ≤ (188083 / 1000000000) := by
  have h := checkLog_sound (w := (1881 / 20001881)) (n := 12)
    (lo := (94041 / 500000000)) (hi := (188083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001881 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001881 / 10000000) = 1/(10000000 / 10001881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5292 : Bounds (94041 / 500000000) (188083 / 1000000000) (Real.log (10001881 / 10000000)) := by
  have h := reflection_log_5292_neg
  have he : Real.log (10001881 / 10000000) = -Real.log (10000000 / 10001881) := by
    rw [show ((10001881 / 10000000) : ℝ) = ((10000000 / 10001881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5293_neg : (188117 / 1000000000) ≤ -Real.log (9998119 / 10000000) ∧
    -Real.log (9998119 / 10000000) ≤ (94059 / 500000000) := by
  have h := checkLog_sound (w := (1881 / 19998119)) (n := 12)
    (lo := (188117 / 1000000000)) (hi := (94059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998119) = 1/(9998119 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5293 : Bounds (-94059 / 500000000) (-188117 / 1000000000) (Real.log (9998119 / 10000000)) := by
  have h := reflection_log_5293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5294_neg : (90308601 / 1000000000) ≤ -Real.log (62500 / 68407) ∧
    -Real.log (62500 / 68407) ≤ (45154301 / 500000000) := by
  have h := checkLog_sound (w := (5907 / 130907)) (n := 12)
    (lo := (90308601 / 1000000000)) (hi := (45154301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68407 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68407 / 62500) = 1/(62500 / 68407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5294 : Bounds (90308601 / 1000000000) (45154301 / 500000000) (Real.log (68407 / 62500)) := by
  have h := reflection_log_5294_neg
  have he : Real.log (68407 / 62500) = -Real.log (62500 / 68407) := by
    rw [show ((68407 / 62500) : ℝ) = ((62500 / 68407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5295_neg : (49640627 / 500000000) ≤ -Real.log (56593 / 62500) ∧
    -Real.log (56593 / 62500) ≤ (19856251 / 200000000) := by
  have h := checkLog_sound (w := (5907 / 119093)) (n := 12)
    (lo := (49640627 / 500000000)) (hi := (19856251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56593) = 1/(56593 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5295 : Bounds (-19856251 / 200000000) (-49640627 / 500000000) (Real.log (56593 / 62500)) := by
  have h := reflection_log_5295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5296_neg : (45263013 / 500000000) ≤ -Real.log (4000 / 4379) ∧
    -Real.log (4000 / 4379) ≤ (90526027 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 8379)) (n := 12)
    (lo := (45263013 / 500000000)) (hi := (90526027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4379 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4379 / 4000) = 1/(4000 / 4379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5296 : Bounds (45263013 / 500000000) (90526027 / 1000000000) (Real.log (4379 / 4000)) := by
  have h := reflection_log_5296_neg
  have he : Real.log (4379 / 4000) = -Real.log (4000 / 4379) := by
    rw [show ((4379 / 4000) : ℝ) = ((4000 / 4379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5297_neg : (9954413 / 100000000) ≤ -Real.log (3621 / 4000) ∧
    -Real.log (3621 / 4000) ≤ (99544131 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 7621)) (n := 12)
    (lo := (9954413 / 100000000)) (hi := (99544131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3621) = 1/(3621 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5297 : Bounds (-99544131 / 1000000000) (-9954413 / 100000000) (Real.log (3621 / 4000)) := by
  have h := reflection_log_5297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5298_neg : (9018103 / 1000000000) ≤ -Real.log (15856359 / 16000000) ∧
    -Real.log (15856359 / 16000000) ≤ (1127263 / 125000000) := by
  have h := checkLog_sound (w := (143641 / 31856359)) (n := 12)
    (lo := (9018103 / 1000000000)) (hi := (1127263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15856359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15856359) = 1/(15856359 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5298 : Bounds (-1127263 / 125000000) (-9018103 / 1000000000) (Real.log (15856359 / 16000000)) := by
  have h := reflection_log_5298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5299_neg : (2243163 / 250000000) ≤ -Real.log (3871357351 / 3906250000) ∧
    -Real.log (3871357351 / 3906250000) ≤ (8972653 / 1000000000) := by
  have h := checkLog_sound (w := (34892649 / 7777607351)) (n := 12)
    (lo := (2243163 / 250000000)) (hi := (8972653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3871357351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3871357351) = 1/(3871357351 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5299 : Bounds (-8972653 / 1000000000) (-2243163 / 250000000) (Real.log (3871357351 / 3906250000)) := by
  have h := reflection_log_5299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5300_neg : (37917971 / 200000000) ≤ -Real.log (125000000000 / 151094216599) ∧
    -Real.log (125000000000 / 151094216599) ≤ (5924683 / 31250000) := by
  have h := checkLog_sound (w := (26094216599 / 276094216599)) (n := 12)
    (lo := (37917971 / 200000000)) (hi := (5924683 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151094216599 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151094216599 / 125000000000) = 1/(125000000000 / 151094216599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5300 : Bounds (37917971 / 200000000) (5924683 / 31250000) (Real.log (151094216599 / 125000000000)) := by
  have h := reflection_log_5300_neg
  have he : Real.log (151094216599 / 125000000000) = -Real.log (125000000000 / 151094216599) := by
    rw [show ((151094216599 / 125000000000) : ℝ) = ((125000000000 / 151094216599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5301_neg : (190070157 / 1000000000) ≤ -Real.log (500000000000 / 604667219001) ∧
    -Real.log (500000000000 / 604667219001) ≤ (95035079 / 500000000) := by
  have h := checkLog_sound (w := (104667219001 / 1104667219001)) (n := 12)
    (lo := (190070157 / 1000000000)) (hi := (95035079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604667219001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604667219001 / 500000000000) = 1/(500000000000 / 604667219001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5301 : Bounds (190070157 / 1000000000) (95035079 / 500000000) (Real.log (604667219001 / 500000000000)) := by
  have h := reflection_log_5301_neg
  have he : Real.log (604667219001 / 500000000000) = -Real.log (500000000000 / 604667219001) := by
    rw [show ((604667219001 / 500000000000) : ℝ) = ((500000000000 / 604667219001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5302_neg : (380526159 / 1000000000) ≤ -Real.log (125000000000 / 182881773399) ∧
    -Real.log (125000000000 / 182881773399) ≤ (4756577 / 12500000) := by
  have h := checkLog_sound (w := (57881773399 / 307881773399)) (n := 12)
    (lo := (380526159 / 1000000000)) (hi := (4756577 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182881773399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182881773399 / 125000000000) = 1/(125000000000 / 182881773399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5302 : Bounds (380526159 / 1000000000) (4756577 / 12500000) (Real.log (182881773399 / 125000000000)) := by
  have h := reflection_log_5302_neg
  have he : Real.log (182881773399 / 125000000000) = -Real.log (125000000000 / 182881773399) := by
    rw [show ((182881773399 / 125000000000) : ℝ) = ((125000000000 / 182881773399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5303_neg : (380733491 / 1000000000) ≤ -Real.log (20000000000 / 29267151127) ∧
    -Real.log (20000000000 / 29267151127) ≤ (95183373 / 250000000) := by
  have h := checkLog_sound (w := (9267151127 / 49267151127)) (n := 12)
    (lo := (380733491 / 1000000000)) (hi := (95183373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29267151127 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29267151127 / 20000000000) = 1/(20000000000 / 29267151127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5303 : Bounds (380733491 / 1000000000) (95183373 / 250000000) (Real.log (29267151127 / 20000000000)) := by
  have h := reflection_log_5303_neg
  have he : Real.log (29267151127 / 20000000000) = -Real.log (20000000000 / 29267151127) := by
    rw [show ((29267151127 / 20000000000) : ℝ) = ((20000000000 / 29267151127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5304_neg : (43109889 / 250000000) ≤ -Real.log (5000 / 5941) ∧
    -Real.log (5000 / 5941) ≤ (172439557 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 10941)) (n := 12)
    (lo := (43109889 / 250000000)) (hi := (172439557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5941 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5941 / 5000) = 1/(5000 / 5941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5304 : Bounds (43109889 / 250000000) (172439557 / 1000000000) (Real.log (5941 / 5000)) := by
  have h := reflection_log_5304_neg
  have he : Real.log (5941 / 5000) = -Real.log (5000 / 5941) := by
    rw [show ((5941 / 5000) : ℝ) = ((5000 / 5941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5305_neg : (104250637 / 500000000) ≤ -Real.log (4059 / 5000) ∧
    -Real.log (4059 / 5000) ≤ (8340051 / 40000000) := by
  have h := checkLog_sound (w := (941 / 9059)) (n := 12)
    (lo := (104250637 / 500000000)) (hi := (8340051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4059) = 1/(4059 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5305 : Bounds (-8340051 / 40000000) (-104250637 / 500000000) (Real.log (4059 / 5000)) := by
  have h := reflection_log_5305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5306_neg : (94091 / 500000000) ≤ -Real.log (5000000 / 5000941) ∧
    -Real.log (5000000 / 5000941) ≤ (188183 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 10000941)) (n := 12)
    (lo := (94091 / 500000000)) (hi := (188183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000941 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000941 / 5000000) = 1/(5000000 / 5000941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5306 : Bounds (94091 / 500000000) (188183 / 1000000000) (Real.log (5000941 / 5000000)) := by
  have h := reflection_log_5306_neg
  have he : Real.log (5000941 / 5000000) = -Real.log (5000000 / 5000941) := by
    rw [show ((5000941 / 5000000) : ℝ) = ((5000000 / 5000941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5307_neg : (188217 / 1000000000) ≤ -Real.log (4999059 / 5000000) ∧
    -Real.log (4999059 / 5000000) ≤ (94109 / 500000000) := by
  have h := checkLog_sound (w := (941 / 9999059)) (n := 12)
    (lo := (188217 / 1000000000)) (hi := (94109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999059) = 1/(4999059 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5307 : Bounds (-94109 / 500000000) (-188217 / 1000000000) (Real.log (4999059 / 5000000)) := by
  have h := reflection_log_5307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5308_neg : (90354283 / 1000000000) ≤ -Real.log (500000 / 547281) ∧
    -Real.log (500000 / 547281) ≤ (22588571 / 250000000) := by
  have h := checkLog_sound (w := (47281 / 1047281)) (n := 12)
    (lo := (90354283 / 1000000000)) (hi := (22588571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547281 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547281 / 500000) = 1/(500000 / 547281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5308 : Bounds (90354283 / 1000000000) (22588571 / 250000000) (Real.log (547281 / 500000)) := by
  have h := reflection_log_5308_neg
  have he : Real.log (547281 / 500000) = -Real.log (500000 / 547281) := by
    rw [show ((547281 / 500000) : ℝ) = ((500000 / 547281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5309_neg : (49668237 / 500000000) ≤ -Real.log (452719 / 500000) ∧
    -Real.log (452719 / 500000) ≤ (3973459 / 40000000) := by
  have h := checkLog_sound (w := (47281 / 952719)) (n := 12)
    (lo := (49668237 / 500000000)) (hi := (3973459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452719) = 1/(452719 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5309 : Bounds (-3973459 / 40000000) (-49668237 / 500000000) (Real.log (452719 / 500000)) := by
  have h := reflection_log_5309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5310_neg : (90572611 / 1000000000) ≤ -Real.log (1000000 / 1094801) ∧
    -Real.log (1000000 / 1094801) ≤ (22643153 / 250000000) := by
  have h := checkLog_sound (w := (94801 / 2094801)) (n := 12)
    (lo := (90572611 / 1000000000)) (hi := (22643153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094801 / 1000000) = 1/(1000000 / 1094801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5310 : Bounds (90572611 / 1000000000) (22643153 / 250000000) (Real.log (1094801 / 1000000)) := by
  have h := reflection_log_5310_neg
  have he : Real.log (1094801 / 1000000) = -Real.log (1000000 / 1094801) := by
    rw [show ((1094801 / 1000000) : ℝ) = ((1000000 / 1094801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5311_neg : (99600469 / 1000000000) ≤ -Real.log (905199 / 1000000) ∧
    -Real.log (905199 / 1000000) ≤ (9960047 / 100000000) := by
  have h := checkLog_sound (w := (94801 / 1905199)) (n := 12)
    (lo := (99600469 / 1000000000)) (hi := (9960047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905199) = 1/(905199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5311 : Bounds (-9960047 / 100000000) (-99600469 / 1000000000) (Real.log (905199 / 1000000)) := by
  have h := reflection_log_5311_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
