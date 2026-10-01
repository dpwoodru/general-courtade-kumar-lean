import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell249
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

theorem reflection_log_1_neg : (333957917 / 1000000000) ≤ -Real.log (512 / 715) ∧
    -Real.log (512 / 715) ≤ (166978959 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1227)) (n := 12)
    (lo := (333957917 / 1000000000)) (hi := (166978959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715 / 512) = 1/(512 / 715) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (333957917 / 1000000000) (166978959 / 500000000) (Real.log (715 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (715 / 512) = -Real.log (512 / 715) := by
    rw [show ((715 / 512) : ℝ) = ((512 / 715) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126245837 / 250000000) ≤ -Real.log (309 / 512) ∧
    -Real.log (309 / 512) ≤ (504983349 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 821)) (n := 12)
    (lo := (126245837 / 250000000)) (hi := (504983349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 309) = 1/(309 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-504983349 / 1000000000) (-126245837 / 250000000) (Real.log (309 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (333538249 / 1000000000) ≤ -Real.log (5120 / 7147) ∧
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


theorem reflection_log_3 : Bounds (333538249 / 1000000000) (1334153 / 4000000) (Real.log (7147 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7147 / 5120) = -Real.log (5120 / 7147) := by
    rw [show ((7147 / 5120) : ℝ) = ((5120 / 7147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (100802589 / 200000000) ≤ -Real.log (3093 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-252006473 / 500000000) (-100802589 / 200000000) (Real.log (3093 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (31042919 / 125000000) ≤ -Real.log (10000 / 12819) ∧
    -Real.log (10000 / 12819) ≤ (248343353 / 1000000000) := by
  have h := checkLog_sound (w := (2819 / 22819)) (n := 12)
    (lo := (31042919 / 125000000)) (hi := (248343353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10000) = 1/(10000 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (31042919 / 125000000) (248343353 / 1000000000) (Real.log (12819 / 10000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12819 / 10000) = -Real.log (10000 / 12819) := by
    rw [show ((12819 / 10000) : ℝ) = ((10000 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331146443 / 1000000000) ≤ -Real.log (7181 / 10000) ∧
    -Real.log (7181 / 10000) ≤ (82786611 / 250000000) := by
  have h := checkLog_sound (w := (2819 / 17181)) (n := 12)
    (lo := (331146443 / 1000000000)) (hi := (82786611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7181) = 1/(7181 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82786611 / 250000000) (-331146443 / 1000000000) (Real.log (7181 / 10000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (31084257 / 125000000) ≤ -Real.log (250000 / 320581) ∧
    -Real.log (250000 / 320581) ≤ (248674057 / 1000000000) := by
  have h := checkLog_sound (w := (70581 / 570581)) (n := 12)
    (lo := (31084257 / 125000000)) (hi := (248674057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320581 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320581 / 250000) = 1/(250000 / 320581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (31084257 / 125000000) (248674057 / 1000000000) (Real.log (320581 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (320581 / 250000) = -Real.log (250000 / 320581) := by
    rw [show ((320581 / 250000) : ℝ) = ((250000 / 320581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66347413 / 200000000) ≤ -Real.log (179419 / 250000) ∧
    -Real.log (179419 / 250000) ≤ (165868533 / 500000000) := by
  have h := checkLog_sound (w := (70581 / 429419)) (n := 12)
    (lo := (66347413 / 200000000)) (hi := (165868533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179419) = 1/(179419 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165868533 / 500000000) (-66347413 / 200000000) (Real.log (179419 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185499003 / 1000000000) ≤ -Real.log (1000000 / 1203819) ∧
    -Real.log (1000000 / 1203819) ≤ (46374751 / 250000000) := by
  have h := checkLog_sound (w := (203819 / 2203819)) (n := 12)
    (lo := (185499003 / 1000000000)) (hi := (46374751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203819 / 1000000) = 1/(1000000 / 1203819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185499003 / 1000000000) (46374751 / 250000000) (Real.log (1203819 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203819 / 1000000) = -Real.log (1000000 / 1203819) := by
    rw [show ((1203819 / 1000000) : ℝ) = ((1000000 / 1203819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (56982183 / 250000000) ≤ -Real.log (796181 / 1000000) ∧
    -Real.log (796181 / 1000000) ≤ (227928733 / 1000000000) := by
  have h := checkLog_sound (w := (203819 / 1796181)) (n := 12)
    (lo := (56982183 / 250000000)) (hi := (227928733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796181) = 1/(796181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227928733 / 1000000000) (-56982183 / 250000000) (Real.log (796181 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (185765619 / 1000000000) ≤ -Real.log (50000 / 60207) ∧
    -Real.log (50000 / 60207) ≤ (9288281 / 50000000) := by
  have h := checkLog_sound (w := (10207 / 110207)) (n := 12)
    (lo := (185765619 / 1000000000)) (hi := (9288281 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60207 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60207 / 50000) = 1/(50000 / 60207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (185765619 / 1000000000) (9288281 / 50000000) (Real.log (60207 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60207 / 50000) = -Real.log (50000 / 60207) := by
    rw [show ((60207 / 50000) : ℝ) = ((50000 / 60207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (57082997 / 250000000) ≤ -Real.log (39793 / 50000) ∧
    -Real.log (39793 / 50000) ≤ (228331989 / 1000000000) := by
  have h := checkLog_sound (w := (10207 / 89793)) (n := 12)
    (lo := (57082997 / 250000000)) (hi := (228331989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39793) = 1/(39793 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-228331989 / 1000000000) (-57082997 / 250000000) (Real.log (39793 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (837551193 / 1000000000) ≤ -Real.log (500000000000 / 1155350792111) ∧
    -Real.log (500000000000 / 1155350792111) ≤ (167510239 / 200000000) := by
  have h := checkLog_sound (w := (155350792111 / 2155350792111)) (n := 12)
    (lo := (144404013 / 1000000000)) (hi := (72202007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155350792111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1155350792111 / 1000000000000) = 1/(500000000000 / 1155350792111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (837551193 / 1000000000) (167510239 / 200000000) (Real.log (1155350792111 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1155350792111 / 500000000000) = -Real.log (500000000000 / 1155350792111) := by
    rw [show ((1155350792111 / 500000000000) : ℝ) = ((500000000000 / 1155350792111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (167788253 / 200000000) ≤ -Real.log (500000000000 / 1156957928803) ∧
    -Real.log (500000000000 / 1156957928803) ≤ (838941267 / 1000000000) := by
  have h := checkLog_sound (w := (156957928803 / 2156957928803)) (n := 12)
    (lo := (29158817 / 200000000)) (hi := (72897043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156957928803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1156957928803 / 1000000000000) = 1/(500000000000 / 1156957928803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (167788253 / 200000000) (838941267 / 1000000000) (Real.log (1156957928803 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1156957928803 / 500000000000) = -Real.log (500000000000 / 1156957928803) := by
    rw [show ((1156957928803 / 500000000000) : ℝ) = ((500000000000 / 1156957928803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (144872449 / 250000000) ≤ -Real.log (500000000000 / 892563709789) ∧
    -Real.log (500000000000 / 892563709789) ≤ (579489797 / 1000000000) := by
  have h := checkLog_sound (w := (392563709789 / 1392563709789)) (n := 12)
    (lo := (144872449 / 250000000)) (hi := (579489797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892563709789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892563709789 / 500000000000) = 1/(500000000000 / 892563709789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144872449 / 250000000) (579489797 / 1000000000) (Real.log (892563709789 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (892563709789 / 500000000000) = -Real.log (500000000000 / 892563709789) := by
    rw [show ((892563709789 / 500000000000) : ℝ) = ((500000000000 / 892563709789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (580411121 / 1000000000) ≤ -Real.log (250000000000 / 446693215323) ∧
    -Real.log (250000000000 / 446693215323) ≤ (290205561 / 500000000) := by
  have h := checkLog_sound (w := (196693215323 / 696693215323)) (n := 12)
    (lo := (580411121 / 1000000000)) (hi := (290205561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((446693215323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(446693215323 / 250000000000) = 1/(250000000000 / 446693215323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (580411121 / 1000000000) (290205561 / 500000000) (Real.log (446693215323 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (446693215323 / 250000000000) = -Real.log (250000000000 / 446693215323) := by
    rw [show ((446693215323 / 250000000000) : ℝ) = ((250000000000 / 446693215323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (82685547 / 200000000) ≤ -Real.log (500000000000 / 755995809997) ∧
    -Real.log (500000000000 / 755995809997) ≤ (51678467 / 125000000) := by
  have h := checkLog_sound (w := (255995809997 / 1255995809997)) (n := 12)
    (lo := (82685547 / 200000000)) (hi := (51678467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755995809997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755995809997 / 500000000000) = 1/(500000000000 / 755995809997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (82685547 / 200000000) (51678467 / 125000000) (Real.log (755995809997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (755995809997 / 500000000000) = -Real.log (500000000000 / 755995809997) := by
    rw [show ((755995809997 / 500000000000) : ℝ) = ((500000000000 / 755995809997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (414097607 / 1000000000) ≤ -Real.log (6250000000 / 9456279999) ∧
    -Real.log (6250000000 / 9456279999) ≤ (51762201 / 125000000) := by
  have h := checkLog_sound (w := (3206279999 / 15706279999)) (n := 12)
    (lo := (414097607 / 1000000000)) (hi := (51762201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9456279999 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9456279999 / 6250000000) = 1/(6250000000 / 9456279999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (414097607 / 1000000000) (51762201 / 125000000) (Real.log (9456279999 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9456279999 / 6250000000) = -Real.log (6250000000 / 9456279999) := by
    rw [show ((9456279999 / 6250000000) : ℝ) = ((6250000000 / 9456279999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1330199 / 31250000) ≤ -Real.log (2395817151 / 2500000000) ∧
    -Real.log (2395817151 / 2500000000) ≤ (42566369 / 1000000000) := by
  have h := checkLog_sound (w := (104182849 / 4895817151)) (n := 12)
    (lo := (1330199 / 31250000)) (hi := (42566369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395817151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395817151) = 1/(2395817151 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42566369 / 1000000000) (-1330199 / 31250000) (Real.log (2395817151 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1325929 / 31250000) ≤ -Real.log (958457815239 / 1000000000000) ∧
    -Real.log (958457815239 / 1000000000000) ≤ (42429729 / 1000000000) := by
  have h := checkLog_sound (w := (41542184761 / 1958457815239)) (n := 12)
    (lo := (1325929 / 31250000)) (hi := (42429729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958457815239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958457815239) = 1/(958457815239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42429729 / 1000000000) (-1325929 / 31250000) (Real.log (958457815239 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell249
