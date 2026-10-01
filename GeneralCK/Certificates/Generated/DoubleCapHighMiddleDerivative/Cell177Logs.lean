import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell177
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

theorem reflection_log_1_neg : (37910301 / 125000000) ≤ -Real.log (2560 / 3467) ∧
    -Real.log (2560 / 3467) ≤ (303282409 / 1000000000) := by
  have h := checkLog_sound (w := (907 / 6027)) (n := 12)
    (lo := (37910301 / 125000000)) (hi := (303282409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3467 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3467 / 2560) = 1/(2560 / 3467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37910301 / 125000000) (303282409 / 1000000000) (Real.log (3467 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3467 / 2560) = -Real.log (2560 / 3467) := by
    rw [show ((3467 / 2560) : ℝ) = ((2560 / 3467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (437415439 / 1000000000) ≤ -Real.log (1653 / 2560) ∧
    -Real.log (1653 / 2560) ≤ (5467693 / 12500000) := by
  have h := checkLog_sound (w := (907 / 4213)) (n := 12)
    (lo := (437415439 / 1000000000)) (hi := (5467693 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1653) = 1/(1653 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-5467693 / 12500000) (-437415439 / 1000000000) (Real.log (1653 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (302849663 / 1000000000) ≤ -Real.log (5120 / 6931) ∧
    -Real.log (5120 / 6931) ≤ (2366013 / 7812500) := by
  have h := checkLog_sound (w := (1811 / 12051)) (n := 12)
    (lo := (302849663 / 1000000000)) (hi := (2366013 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6931 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6931 / 5120) = 1/(5120 / 6931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (302849663 / 1000000000) (2366013 / 7812500) (Real.log (6931 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6931 / 5120) = -Real.log (5120 / 6931) := by
    rw [show ((6931 / 5120) : ℝ) = ((5120 / 6931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (43650841 / 100000000) ≤ -Real.log (3309 / 5120) ∧
    -Real.log (3309 / 5120) ≤ (436508411 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 8429)) (n := 12)
    (lo := (43650841 / 100000000)) (hi := (436508411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3309) = 1/(3309 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-436508411 / 1000000000) (-43650841 / 100000000) (Real.log (3309 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (56083111 / 250000000) ≤ -Real.log (1000000 / 1251487) ∧
    -Real.log (1000000 / 1251487) ≤ (44866489 / 200000000) := by
  have h := checkLog_sound (w := (251487 / 2251487)) (n := 12)
    (lo := (56083111 / 250000000)) (hi := (44866489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251487 / 1000000) = 1/(1000000 / 1251487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (56083111 / 250000000) (44866489 / 200000000) (Real.log (1251487 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1251487 / 1000000) = -Real.log (1000000 / 1251487) := by
    rw [show ((1251487 / 1000000) : ℝ) = ((1000000 / 1251487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (289666707 / 1000000000) ≤ -Real.log (748513 / 1000000) ∧
    -Real.log (748513 / 1000000) ≤ (72416677 / 250000000) := by
  have h := checkLog_sound (w := (251487 / 1748513)) (n := 12)
    (lo := (289666707 / 1000000000)) (hi := (72416677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748513) = 1/(748513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72416677 / 250000000) (-289666707 / 1000000000) (Real.log (748513 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44934077 / 200000000) ≤ -Real.log (100000 / 125191) ∧
    -Real.log (100000 / 125191) ≤ (112335193 / 500000000) := by
  have h := checkLog_sound (w := (25191 / 225191)) (n := 12)
    (lo := (44934077 / 200000000)) (hi := (112335193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125191 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125191 / 100000) = 1/(100000 / 125191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44934077 / 200000000) (112335193 / 500000000) (Real.log (125191 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (125191 / 100000) = -Real.log (100000 / 125191) := by
    rw [show ((125191 / 100000) : ℝ) = ((100000 / 125191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (290231987 / 1000000000) ≤ -Real.log (74809 / 100000) ∧
    -Real.log (74809 / 100000) ≤ (72557997 / 250000000) := by
  have h := checkLog_sound (w := (25191 / 174809)) (n := 12)
    (lo := (290231987 / 1000000000)) (hi := (72557997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74809) = 1/(74809 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72557997 / 250000000) (-290231987 / 1000000000) (Real.log (74809 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16636069 / 100000000) ≤ -Real.log (1000000 / 1180999) ∧
    -Real.log (1000000 / 1180999) ≤ (166360691 / 1000000000) := by
  have h := checkLog_sound (w := (180999 / 2180999)) (n := 12)
    (lo := (16636069 / 100000000)) (hi := (166360691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180999 / 1000000) = 1/(1000000 / 1180999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16636069 / 100000000) (166360691 / 1000000000) (Real.log (1180999 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180999 / 1000000) = -Real.log (1000000 / 1180999) := by
    rw [show ((1180999 / 1000000) : ℝ) = ((1000000 / 1180999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99834987 / 500000000) ≤ -Real.log (819001 / 1000000) ∧
    -Real.log (819001 / 1000000) ≤ (7986799 / 40000000) := by
  have h := checkLog_sound (w := (180999 / 1819001)) (n := 12)
    (lo := (99834987 / 500000000)) (hi := (7986799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819001) = 1/(819001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7986799 / 40000000) (-99834987 / 500000000) (Real.log (819001 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83313689 / 500000000) ≤ -Real.log (500000 / 590657) ∧
    -Real.log (500000 / 590657) ≤ (166627379 / 1000000000) := by
  have h := checkLog_sound (w := (90657 / 1090657)) (n := 12)
    (lo := (83313689 / 500000000)) (hi := (166627379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590657 / 500000) = 1/(500000 / 590657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83313689 / 500000000) (166627379 / 1000000000) (Real.log (590657 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590657 / 500000) = -Real.log (500000 / 590657) := by
    rw [show ((590657 / 500000) : ℝ) = ((500000 / 590657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200054663 / 1000000000) ≤ -Real.log (409343 / 500000) ∧
    -Real.log (409343 / 500000) ≤ (25006833 / 125000000) := by
  have h := checkLog_sound (w := (90657 / 909343)) (n := 12)
    (lo := (200054663 / 1000000000)) (hi := (25006833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409343) = 1/(409343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25006833 / 125000000) (-200054663 / 1000000000) (Real.log (409343 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (739358073 / 1000000000) ≤ -Real.log (125000000000 / 261823813841) ∧
    -Real.log (125000000000 / 261823813841) ≤ (29574323 / 40000000) := by
  have h := checkLog_sound (w := (11823813841 / 511823813841)) (n := 12)
    (lo := (46210893 / 1000000000)) (hi := (23105447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261823813841 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261823813841 / 250000000000) = 1/(125000000000 / 261823813841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (739358073 / 1000000000) (29574323 / 40000000) (Real.log (261823813841 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (261823813841 / 125000000000) = -Real.log (125000000000 / 261823813841) := by
    rw [show ((261823813841 / 125000000000) : ℝ) = ((125000000000 / 261823813841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (740697847 / 1000000000) ≤ -Real.log (31250000000 / 65543708409) ∧
    -Real.log (31250000000 / 65543708409) ≤ (740697849 / 1000000000) := by
  have h := checkLog_sound (w := (3043708409 / 128043708409)) (n := 12)
    (lo := (47550667 / 1000000000)) (hi := (11887667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65543708409 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65543708409 / 62500000000) = 1/(31250000000 / 65543708409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (740697847 / 1000000000) (740697849 / 1000000000) (Real.log (65543708409 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (65543708409 / 31250000000) = -Real.log (31250000000 / 65543708409) := by
    rw [show ((65543708409 / 31250000000) : ℝ) = ((31250000000 / 65543708409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (513999151 / 1000000000) ≤ -Real.log (50000000000 / 83598214059) ∧
    -Real.log (50000000000 / 83598214059) ≤ (32124947 / 62500000) := by
  have h := checkLog_sound (w := (33598214059 / 133598214059)) (n := 12)
    (lo := (513999151 / 1000000000)) (hi := (32124947 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83598214059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83598214059 / 50000000000) = 1/(50000000000 / 83598214059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (513999151 / 1000000000) (32124947 / 62500000) (Real.log (83598214059 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (83598214059 / 50000000000) = -Real.log (50000000000 / 83598214059) := by
    rw [show ((83598214059 / 50000000000) : ℝ) = ((50000000000 / 83598214059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128725593 / 250000000) ≤ -Real.log (125000000000 / 209184389579) ∧
    -Real.log (125000000000 / 209184389579) ≤ (514902373 / 1000000000) := by
  have h := checkLog_sound (w := (84184389579 / 334184389579)) (n := 12)
    (lo := (128725593 / 250000000)) (hi := (514902373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209184389579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209184389579 / 125000000000) = 1/(125000000000 / 209184389579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (128725593 / 250000000) (514902373 / 1000000000) (Real.log (209184389579 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (209184389579 / 125000000000) = -Real.log (125000000000 / 209184389579) := by
    rw [show ((209184389579 / 125000000000) : ℝ) = ((125000000000 / 209184389579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45753833 / 125000000) ≤ -Real.log (500000000000 / 720999730159) ∧
    -Real.log (500000000000 / 720999730159) ≤ (73206133 / 200000000) := by
  have h := checkLog_sound (w := (220999730159 / 1220999730159)) (n := 12)
    (lo := (45753833 / 125000000)) (hi := (73206133 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720999730159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720999730159 / 500000000000) = 1/(500000000000 / 720999730159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45753833 / 125000000) (73206133 / 200000000) (Real.log (720999730159 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (720999730159 / 500000000000) = -Real.log (500000000000 / 720999730159) := by
    rw [show ((720999730159 / 500000000000) : ℝ) = ((500000000000 / 720999730159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (366682041 / 1000000000) ≤ -Real.log (500000000000 / 721469525557) ∧
    -Real.log (500000000000 / 721469525557) ≤ (183341021 / 500000000) := by
  have h := checkLog_sound (w := (221469525557 / 1221469525557)) (n := 12)
    (lo := (366682041 / 1000000000)) (hi := (183341021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721469525557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721469525557 / 500000000000) = 1/(500000000000 / 721469525557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (366682041 / 1000000000) (183341021 / 500000000) (Real.log (721469525557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (721469525557 / 500000000000) = -Real.log (500000000000 / 721469525557) := by
    rw [show ((721469525557 / 500000000000) : ℝ) = ((500000000000 / 721469525557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8356821 / 250000000) ≤ -Real.log (241781308351 / 250000000000) ∧
    -Real.log (241781308351 / 250000000000) ≤ (6685457 / 200000000) := by
  have h := checkLog_sound (w := (8218691649 / 491781308351)) (n := 12)
    (lo := (8356821 / 250000000)) (hi := (6685457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241781308351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241781308351) = 1/(241781308351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6685457 / 200000000) (-8356821 / 250000000) (Real.log (241781308351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33309283 / 1000000000) ≤ -Real.log (967239361999 / 1000000000000) ∧
    -Real.log (967239361999 / 1000000000000) ≤ (8327321 / 250000000) := by
  have h := checkLog_sound (w := (32760638001 / 1967239361999)) (n := 12)
    (lo := (33309283 / 1000000000)) (hi := (8327321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967239361999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967239361999) = 1/(967239361999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8327321 / 250000000) (-33309283 / 1000000000) (Real.log (967239361999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell177
