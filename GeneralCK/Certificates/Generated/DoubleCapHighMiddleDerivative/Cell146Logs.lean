import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell146
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

theorem reflection_log_1_neg : (7244487 / 25000000) ≤ -Real.log (5120 / 6841) ∧
    -Real.log (5120 / 6841) ≤ (289779481 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 11961)) (n := 12)
    (lo := (7244487 / 25000000)) (hi := (289779481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6841 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6841 / 5120) = 1/(5120 / 6841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7244487 / 25000000) (289779481 / 1000000000) (Real.log (6841 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6841 / 5120) = -Real.log (5120 / 6841) := by
    rw [show ((6841 / 5120) : ℝ) = ((5120 / 6841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (25604573 / 62500000) ≤ -Real.log (3399 / 5120) ∧
    -Real.log (3399 / 5120) ≤ (409673169 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 8519)) (n := 12)
    (lo := (25604573 / 62500000)) (hi := (409673169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3399) = 1/(3399 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-409673169 / 1000000000) (-25604573 / 62500000) (Real.log (3399 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72335213 / 250000000) ≤ -Real.log (2560 / 3419) ∧
    -Real.log (2560 / 3419) ≤ (289340853 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 5979)) (n := 12)
    (lo := (72335213 / 250000000)) (hi := (289340853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3419 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3419 / 2560) = 1/(2560 / 3419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72335213 / 250000000) (289340853 / 1000000000) (Real.log (3419 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3419 / 2560) = -Real.log (2560 / 3419) := by
    rw [show ((3419 / 2560) : ℝ) = ((2560 / 3419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (81758189 / 200000000) ≤ -Real.log (1701 / 2560) ∧
    -Real.log (1701 / 2560) ≤ (204395473 / 500000000) := by
  have h := checkLog_sound (w := (859 / 4261)) (n := 12)
    (lo := (81758189 / 200000000)) (hi := (204395473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1701) = 1/(1701 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-204395473 / 500000000) (-81758189 / 200000000) (Real.log (1701 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21384687 / 100000000) ≤ -Real.log (1000000 / 1238433) ∧
    -Real.log (1000000 / 1238433) ≤ (213846871 / 1000000000) := by
  have h := checkLog_sound (w := (238433 / 2238433)) (n := 12)
    (lo := (21384687 / 100000000)) (hi := (213846871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238433 / 1000000) = 1/(1000000 / 1238433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21384687 / 100000000) (213846871 / 1000000000) (Real.log (1238433 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1238433 / 1000000) = -Real.log (1000000 / 1238433) := by
    rw [show ((1238433 / 1000000) : ℝ) = ((1000000 / 1238433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136188563 / 500000000) ≤ -Real.log (761567 / 1000000) ∧
    -Real.log (761567 / 1000000) ≤ (272377127 / 1000000000) := by
  have h := checkLog_sound (w := (238433 / 1761567)) (n := 12)
    (lo := (136188563 / 500000000)) (hi := (272377127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761567) = 1/(761567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-272377127 / 1000000000) (-136188563 / 500000000) (Real.log (761567 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10709459 / 50000000) ≤ -Real.log (1000000 / 1238857) ∧
    -Real.log (1000000 / 1238857) ≤ (214189181 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 2238857)) (n := 12)
    (lo := (10709459 / 50000000)) (hi := (214189181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238857 / 1000000) = 1/(1000000 / 1238857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10709459 / 50000000) (214189181 / 1000000000) (Real.log (1238857 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1238857 / 1000000) = -Real.log (1000000 / 1238857) := by
    rw [show ((1238857 / 1000000) : ℝ) = ((1000000 / 1238857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68233507 / 250000000) ≤ -Real.log (761143 / 1000000) ∧
    -Real.log (761143 / 1000000) ≤ (272934029 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 1761143)) (n := 12)
    (lo := (68233507 / 250000000)) (hi := (272934029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761143) = 1/(761143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-272934029 / 1000000000) (-68233507 / 250000000) (Real.log (761143 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158111681 / 1000000000) ≤ -Real.log (1000000 / 1171297) ∧
    -Real.log (1000000 / 1171297) ≤ (79055841 / 500000000) := by
  have h := checkLog_sound (w := (171297 / 2171297)) (n := 12)
    (lo := (158111681 / 1000000000)) (hi := (79055841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171297 / 1000000) = 1/(1000000 / 1171297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158111681 / 1000000000) (79055841 / 500000000) (Real.log (1171297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171297 / 1000000) = -Real.log (1000000 / 1171297) := by
    rw [show ((1171297 / 1000000) : ℝ) = ((1000000 / 1171297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187893451 / 1000000000) ≤ -Real.log (828703 / 1000000) ∧
    -Real.log (828703 / 1000000) ≤ (46973363 / 250000000) := by
  have h := checkLog_sound (w := (171297 / 1828703)) (n := 12)
    (lo := (187893451 / 1000000000)) (hi := (46973363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828703) = 1/(828703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46973363 / 250000000) (-187893451 / 1000000000) (Real.log (828703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (158378871 / 1000000000) ≤ -Real.log (100000 / 117161) ∧
    -Real.log (100000 / 117161) ≤ (19797359 / 125000000) := by
  have h := checkLog_sound (w := (17161 / 217161)) (n := 12)
    (lo := (158378871 / 1000000000)) (hi := (19797359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117161 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117161 / 100000) = 1/(100000 / 117161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (158378871 / 1000000000) (19797359 / 125000000) (Real.log (117161 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117161 / 100000) = -Real.log (100000 / 117161) := by
    rw [show ((117161 / 100000) : ℝ) = ((100000 / 117161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9413561 / 50000000) ≤ -Real.log (82839 / 100000) ∧
    -Real.log (82839 / 100000) ≤ (188271221 / 1000000000) := by
  have h := checkLog_sound (w := (17161 / 182839)) (n := 12)
    (lo := (9413561 / 50000000)) (hi := (188271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82839) = 1/(82839 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188271221 / 1000000000) (-9413561 / 50000000) (Real.log (82839 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (174532949 / 250000000) ≤ -Real.log (62500000000 / 125624632569) ∧
    -Real.log (62500000000 / 125624632569) ≤ (349065899 / 500000000) := by
  have h := checkLog_sound (w := (624632569 / 250624632569)) (n := 12)
    (lo := (623077 / 125000000)) (hi := (4984617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125624632569 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125624632569 / 125000000000) = 1/(62500000000 / 125624632569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (174532949 / 250000000) (349065899 / 500000000) (Real.log (125624632569 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (125624632569 / 62500000000) = -Real.log (62500000000 / 125624632569) := by
    rw [show ((125624632569 / 62500000000) : ℝ) = ((62500000000 / 125624632569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (87431581 / 125000000) ≤ -Real.log (500000000000 / 1006325389821) ∧
    -Real.log (500000000000 / 1006325389821) ≤ (13989053 / 20000000) := by
  have h := checkLog_sound (w := (6325389821 / 2006325389821)) (n := 12)
    (lo := (1576367 / 250000000)) (hi := (6305469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006325389821 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006325389821 / 1000000000000) = 1/(500000000000 / 1006325389821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (87431581 / 125000000) (13989053 / 20000000) (Real.log (1006325389821 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1006325389821 / 500000000000) = -Real.log (500000000000 / 1006325389821) := by
    rw [show ((1006325389821 / 500000000000) : ℝ) = ((500000000000 / 1006325389821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (486223997 / 1000000000) ≤ -Real.log (50000000000 / 81308210571) ∧
    -Real.log (50000000000 / 81308210571) ≤ (243111999 / 500000000) := by
  have h := checkLog_sound (w := (31308210571 / 131308210571)) (n := 12)
    (lo := (486223997 / 1000000000)) (hi := (243111999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81308210571 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81308210571 / 50000000000) = 1/(50000000000 / 81308210571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (486223997 / 1000000000) (243111999 / 500000000) (Real.log (81308210571 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (81308210571 / 50000000000) = -Real.log (50000000000 / 81308210571) := by
    rw [show ((81308210571 / 50000000000) : ℝ) = ((50000000000 / 81308210571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60890401 / 125000000) ≤ -Real.log (125000000000 / 203453391807) ∧
    -Real.log (125000000000 / 203453391807) ≤ (487123209 / 1000000000) := by
  have h := checkLog_sound (w := (78453391807 / 328453391807)) (n := 12)
    (lo := (60890401 / 125000000)) (hi := (487123209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203453391807 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203453391807 / 125000000000) = 1/(125000000000 / 203453391807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (60890401 / 125000000) (487123209 / 1000000000) (Real.log (203453391807 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (203453391807 / 125000000000) = -Real.log (125000000000 / 203453391807) := by
    rw [show ((203453391807 / 125000000000) : ℝ) = ((125000000000 / 203453391807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (86501283 / 250000000) ≤ -Real.log (250000000000 / 353352467651) ∧
    -Real.log (250000000000 / 353352467651) ≤ (346005133 / 1000000000) := by
  have h := checkLog_sound (w := (103352467651 / 603352467651)) (n := 12)
    (lo := (86501283 / 250000000)) (hi := (346005133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353352467651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353352467651 / 250000000000) = 1/(250000000000 / 353352467651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (86501283 / 250000000) (346005133 / 1000000000) (Real.log (353352467651 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353352467651 / 250000000000) = -Real.log (250000000000 / 353352467651) := by
    rw [show ((353352467651 / 250000000000) : ℝ) = ((250000000000 / 353352467651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (86662523 / 250000000) ≤ -Real.log (500000000000 / 707160878331) ∧
    -Real.log (500000000000 / 707160878331) ≤ (346650093 / 1000000000) := by
  have h := checkLog_sound (w := (207160878331 / 1207160878331)) (n := 12)
    (lo := (86662523 / 250000000)) (hi := (346650093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707160878331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707160878331 / 500000000000) = 1/(500000000000 / 707160878331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (86662523 / 250000000) (346650093 / 1000000000) (Real.log (707160878331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (707160878331 / 500000000000) = -Real.log (500000000000 / 707160878331) := by
    rw [show ((707160878331 / 500000000000) : ℝ) = ((500000000000 / 707160878331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29892349 / 1000000000) ≤ -Real.log (9705500079 / 10000000000) ∧
    -Real.log (9705500079 / 10000000000) ≤ (597847 / 20000000) := by
  have h := checkLog_sound (w := (294499921 / 19705500079)) (n := 12)
    (lo := (29892349 / 1000000000)) (hi := (597847 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9705500079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9705500079) = 1/(9705500079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-597847 / 20000000) (-29892349 / 1000000000) (Real.log (9705500079 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29781769 / 1000000000) ≤ -Real.log (970657337791 / 1000000000000) ∧
    -Real.log (970657337791 / 1000000000000) ≤ (2978177 / 100000000) := by
  have h := checkLog_sound (w := (29342662209 / 1970657337791)) (n := 12)
    (lo := (29781769 / 1000000000)) (hi := (2978177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970657337791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970657337791) = 1/(970657337791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2978177 / 100000000) (-29781769 / 1000000000) (Real.log (970657337791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell146
