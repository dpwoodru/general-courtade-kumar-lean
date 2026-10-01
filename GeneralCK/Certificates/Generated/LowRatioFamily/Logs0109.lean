import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6976_neg : (96296057 / 1000000000) ≤ -Real.log (200000 / 220217) ∧
    -Real.log (200000 / 220217) ≤ (48148029 / 500000000) := by
  have h := checkLog_sound (w := (20217 / 420217)) (n := 12)
    (lo := (96296057 / 1000000000)) (hi := (48148029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220217 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220217 / 200000) = 1/(200000 / 220217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6976 : Bounds (96296057 / 1000000000) (48148029 / 500000000) (Real.log (220217 / 200000)) := by
  have h := reflection_log_6976_neg
  have he : Real.log (220217 / 200000) = -Real.log (200000 / 220217) := by
    rw [show ((220217 / 200000) : ℝ) = ((200000 / 220217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6977_neg : (53283399 / 500000000) ≤ -Real.log (179783 / 200000) ∧
    -Real.log (179783 / 200000) ≤ (106566799 / 1000000000) := by
  have h := checkLog_sound (w := (20217 / 379783)) (n := 12)
    (lo := (53283399 / 500000000)) (hi := (106566799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179783) = 1/(179783 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6977 : Bounds (-106566799 / 1000000000) (-53283399 / 500000000) (Real.log (179783 / 200000)) := by
  have h := reflection_log_6977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6978_neg : (10270741 / 1000000000) ≤ -Real.log (39591272911 / 40000000000) ∧
    -Real.log (39591272911 / 40000000000) ≤ (5135371 / 500000000) := by
  have h := checkLog_sound (w := (408727089 / 79591272911)) (n := 12)
    (lo := (10270741 / 1000000000)) (hi := (5135371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39591272911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39591272911) = 1/(39591272911 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6978 : Bounds (-5135371 / 500000000) (-10270741 / 1000000000) (Real.log (39591272911 / 40000000000)) := by
  have h := reflection_log_6978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6979_neg : (10178017 / 1000000000) ≤ -Real.log (9898736031 / 10000000000) ∧
    -Real.log (9898736031 / 10000000000) ≤ (5089009 / 500000000) := by
  have h := checkLog_sound (w := (101263969 / 19898736031)) (n := 12)
    (lo := (10178017 / 1000000000)) (hi := (5089009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9898736031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9898736031) = 1/(9898736031 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6979 : Bounds (-5089009 / 500000000) (-10178017 / 1000000000) (Real.log (9898736031 / 10000000000)) := by
  have h := reflection_log_6979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6980_neg : (201943503 / 1000000000) ≤ -Real.log (250000000000 / 305944716857) ∧
    -Real.log (250000000000 / 305944716857) ≤ (12621469 / 62500000) := by
  have h := checkLog_sound (w := (55944716857 / 555944716857)) (n := 12)
    (lo := (201943503 / 1000000000)) (hi := (12621469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305944716857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305944716857 / 250000000000) = 1/(250000000000 / 305944716857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6980 : Bounds (201943503 / 1000000000) (12621469 / 62500000) (Real.log (305944716857 / 250000000000)) := by
  have h := reflection_log_6980_neg
  have he : Real.log (305944716857 / 250000000000) = -Real.log (250000000000 / 305944716857) := by
    rw [show ((305944716857 / 250000000000) : ℝ) = ((250000000000 / 305944716857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6981_neg : (40572571 / 200000000) ≤ -Real.log (500000000000 / 612452234083) ∧
    -Real.log (500000000000 / 612452234083) ≤ (25357857 / 125000000) := by
  have h := checkLog_sound (w := (112452234083 / 1112452234083)) (n := 12)
    (lo := (40572571 / 200000000)) (hi := (25357857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612452234083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612452234083 / 500000000000) = 1/(500000000000 / 612452234083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6981 : Bounds (40572571 / 200000000) (25357857 / 125000000) (Real.log (612452234083 / 500000000000)) := by
  have h := reflection_log_6981_neg
  have he : Real.log (612452234083 / 500000000000) = -Real.log (500000000000 / 612452234083) := by
    rw [show ((612452234083 / 500000000000) : ℝ) = ((500000000000 / 612452234083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6982_neg : (406506883 / 1000000000) ≤ -Real.log (500000000000 / 750781738587) ∧
    -Real.log (500000000000 / 750781738587) ≤ (101626721 / 250000000) := by
  have h := checkLog_sound (w := (250781738587 / 1250781738587)) (n := 12)
    (lo := (406506883 / 1000000000)) (hi := (101626721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750781738587 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750781738587 / 500000000000) = 1/(500000000000 / 750781738587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6982 : Bounds (406506883 / 1000000000) (101626721 / 250000000) (Real.log (750781738587 / 500000000000)) := by
  have h := reflection_log_6982_neg
  have he : Real.log (750781738587 / 500000000000) = -Real.log (500000000000 / 750781738587) := by
    rw [show ((750781738587 / 500000000000) : ℝ) = ((500000000000 / 750781738587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6983_neg : (183154543 / 1000000000) ≤ -Real.log (1000 / 1201) ∧
    -Real.log (1000 / 1201) ≤ (11447159 / 62500000) := by
  have h := checkLog_sound (w := (201 / 2201)) (n := 12)
    (lo := (183154543 / 1000000000)) (hi := (11447159 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201 / 1000) = 1/(1000 / 1201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6983 : Bounds (183154543 / 1000000000) (11447159 / 62500000) (Real.log (1201 / 1000)) := by
  have h := reflection_log_6983_neg
  have he : Real.log (1201 / 1000) = -Real.log (1000 / 1201) := by
    rw [show ((1201 / 1000) : ℝ) = ((1000 / 1201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6984_neg : (224394333 / 1000000000) ≤ -Real.log (799 / 1000) ∧
    -Real.log (799 / 1000) ≤ (112197167 / 500000000) := by
  have h := checkLog_sound (w := (201 / 1799)) (n := 12)
    (lo := (224394333 / 1000000000)) (hi := (112197167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 799) = 1/(799 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6984 : Bounds (-112197167 / 500000000) (-224394333 / 1000000000) (Real.log (799 / 1000)) := by
  have h := reflection_log_6984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6985_neg : (200979 / 1000000000) ≤ -Real.log (1000000 / 1000201) ∧
    -Real.log (1000000 / 1000201) ≤ (10049 / 50000000) := by
  have h := checkLog_sound (w := (201 / 2000201)) (n := 12)
    (lo := (200979 / 1000000000)) (hi := (10049 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000201 / 1000000) = 1/(1000000 / 1000201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6985 : Bounds (200979 / 1000000000) (10049 / 50000000) (Real.log (1000201 / 1000000)) := by
  have h := reflection_log_6985_neg
  have he : Real.log (1000201 / 1000000) = -Real.log (1000000 / 1000201) := by
    rw [show ((1000201 / 1000000) : ℝ) = ((1000000 / 1000201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6986_neg : (10051 / 50000000) ≤ -Real.log (999799 / 1000000) ∧
    -Real.log (999799 / 1000000) ≤ (201021 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 1999799)) (n := 12)
    (lo := (10051 / 50000000)) (hi := (201021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999799) = 1/(999799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6986 : Bounds (-201021 / 1000000000) (-10051 / 50000000) (Real.log (999799 / 1000000)) := by
  have h := reflection_log_6986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6987_neg : (96114401 / 1000000000) ≤ -Real.log (200000 / 220177) ∧
    -Real.log (200000 / 220177) ≤ (48057201 / 500000000) := by
  have h := checkLog_sound (w := (20177 / 420177)) (n := 12)
    (lo := (96114401 / 1000000000)) (hi := (48057201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220177 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220177 / 200000) = 1/(200000 / 220177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6987 : Bounds (96114401 / 1000000000) (48057201 / 500000000) (Real.log (220177 / 200000)) := by
  have h := reflection_log_6987_neg
  have he : Real.log (220177 / 200000) = -Real.log (200000 / 220177) := by
    rw [show ((220177 / 200000) : ℝ) = ((200000 / 220177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6988_neg : (26586083 / 250000000) ≤ -Real.log (179823 / 200000) ∧
    -Real.log (179823 / 200000) ≤ (106344333 / 1000000000) := by
  have h := checkLog_sound (w := (20177 / 379823)) (n := 12)
    (lo := (26586083 / 250000000)) (hi := (106344333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179823) = 1/(179823 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6988 : Bounds (-106344333 / 1000000000) (-26586083 / 250000000) (Real.log (179823 / 200000)) := by
  have h := reflection_log_6988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6989_neg : (6033033 / 62500000) ≤ -Real.log (1000000 / 1101341) ∧
    -Real.log (1000000 / 1101341) ≤ (96528529 / 1000000000) := by
  have h := checkLog_sound (w := (101341 / 2101341)) (n := 12)
    (lo := (6033033 / 62500000)) (hi := (96528529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101341 / 1000000) = 1/(1000000 / 1101341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6989 : Bounds (6033033 / 62500000) (96528529 / 1000000000) (Real.log (1101341 / 1000000)) := by
  have h := reflection_log_6989_neg
  have he : Real.log (1101341 / 1000000) = -Real.log (1000000 / 1101341) := by
    rw [show ((1101341 / 1000000) : ℝ) = ((1000000 / 1101341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6990_neg : (53425813 / 500000000) ≤ -Real.log (898659 / 1000000) ∧
    -Real.log (898659 / 1000000) ≤ (106851627 / 1000000000) := by
  have h := checkLog_sound (w := (101341 / 1898659)) (n := 12)
    (lo := (53425813 / 500000000)) (hi := (106851627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898659) = 1/(898659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6990 : Bounds (-106851627 / 1000000000) (-53425813 / 500000000) (Real.log (898659 / 1000000)) := by
  have h := reflection_log_6990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6991_neg : (5161549 / 500000000) ≤ -Real.log (989730001719 / 1000000000000) ∧
    -Real.log (989730001719 / 1000000000000) ≤ (10323099 / 1000000000) := by
  have h := checkLog_sound (w := (10269998281 / 1989730001719)) (n := 12)
    (lo := (5161549 / 500000000)) (hi := (10323099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989730001719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989730001719) = 1/(989730001719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6991 : Bounds (-10323099 / 1000000000) (-5161549 / 500000000) (Real.log (989730001719 / 1000000000000)) := by
  have h := reflection_log_6991_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6992_neg : (1022993 / 100000000) ≤ -Real.log (39592888671 / 40000000000) ∧
    -Real.log (39592888671 / 40000000000) ≤ (10229931 / 1000000000) := by
  have h := checkLog_sound (w := (407111329 / 79592888671)) (n := 12)
    (lo := (1022993 / 100000000)) (hi := (10229931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39592888671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39592888671) = 1/(39592888671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6992 : Bounds (-10229931 / 1000000000) (-1022993 / 100000000) (Real.log (39592888671 / 40000000000)) := by
  have h := reflection_log_6992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6993_neg : (101229367 / 500000000) ≤ -Real.log (500000000000 / 612204779143) ∧
    -Real.log (500000000000 / 612204779143) ≤ (40491747 / 200000000) := by
  have h := checkLog_sound (w := (112204779143 / 1112204779143)) (n := 12)
    (lo := (101229367 / 500000000)) (hi := (40491747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612204779143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612204779143 / 500000000000) = 1/(500000000000 / 612204779143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6993 : Bounds (101229367 / 500000000) (40491747 / 200000000) (Real.log (612204779143 / 500000000000)) := by
  have h := reflection_log_6993_neg
  have he : Real.log (612204779143 / 500000000000) = -Real.log (500000000000 / 612204779143) := by
    rw [show ((612204779143 / 500000000000) : ℝ) = ((500000000000 / 612204779143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6994_neg : (40676031 / 200000000) ≤ -Real.log (250000000000 / 306384568563) ∧
    -Real.log (250000000000 / 306384568563) ≤ (50845039 / 250000000) := by
  have h := checkLog_sound (w := (56384568563 / 556384568563)) (n := 12)
    (lo := (40676031 / 200000000)) (hi := (50845039 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306384568563 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306384568563 / 250000000000) = 1/(250000000000 / 306384568563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6994 : Bounds (40676031 / 200000000) (50845039 / 250000000) (Real.log (306384568563 / 250000000000)) := by
  have h := reflection_log_6994_neg
  have he : Real.log (306384568563 / 250000000000) = -Real.log (250000000000 / 306384568563) := by
    rw [show ((306384568563 / 250000000000) : ℝ) = ((250000000000 / 306384568563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6995_neg : (406506883 / 1000000000) ≤ -Real.log (250000000000 / 375390869293) ∧
    -Real.log (250000000000 / 375390869293) ≤ (101626721 / 250000000) := by
  have h := checkLog_sound (w := (125390869293 / 625390869293)) (n := 12)
    (lo := (406506883 / 1000000000)) (hi := (101626721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375390869293 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375390869293 / 250000000000) = 1/(250000000000 / 375390869293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6995 : Bounds (406506883 / 1000000000) (101626721 / 250000000) (Real.log (375390869293 / 250000000000)) := by
  have h := reflection_log_6995_neg
  have he : Real.log (375390869293 / 250000000000) = -Real.log (250000000000 / 375390869293) := by
    rw [show ((375390869293 / 250000000000) : ℝ) = ((250000000000 / 375390869293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6996_neg : (101887219 / 250000000) ≤ -Real.log (50000000000 / 75156445557) ∧
    -Real.log (50000000000 / 75156445557) ≤ (407548877 / 1000000000) := by
  have h := checkLog_sound (w := (25156445557 / 125156445557)) (n := 12)
    (lo := (101887219 / 250000000)) (hi := (407548877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75156445557 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75156445557 / 50000000000) = 1/(50000000000 / 75156445557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6996 : Bounds (101887219 / 250000000) (407548877 / 1000000000) (Real.log (75156445557 / 50000000000)) := by
  have h := reflection_log_6996_neg
  have he : Real.log (75156445557 / 50000000000) = -Real.log (50000000000 / 75156445557) := by
    rw [show ((75156445557 / 50000000000) : ℝ) = ((50000000000 / 75156445557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6997_neg : (22946347 / 125000000) ≤ -Real.log (2000 / 2403) ∧
    -Real.log (2000 / 2403) ≤ (183570777 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 4403)) (n := 12)
    (lo := (22946347 / 125000000)) (hi := (183570777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2403 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2403 / 2000) = 1/(2000 / 2403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6997 : Bounds (22946347 / 125000000) (183570777 / 1000000000) (Real.log (2403 / 2000)) := by
  have h := reflection_log_6997_neg
  have he : Real.log (2403 / 2000) = -Real.log (2000 / 2403) := by
    rw [show ((2403 / 2000) : ℝ) = ((2000 / 2403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6998_neg : (225020311 / 1000000000) ≤ -Real.log (1597 / 2000) ∧
    -Real.log (1597 / 2000) ≤ (28127539 / 125000000) := by
  have h := checkLog_sound (w := (403 / 3597)) (n := 12)
    (lo := (225020311 / 1000000000)) (hi := (28127539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1597) = 1/(1597 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6998 : Bounds (-28127539 / 125000000) (-225020311 / 1000000000) (Real.log (1597 / 2000)) := by
  have h := reflection_log_6998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6999_neg : (201479 / 1000000000) ≤ -Real.log (2000000 / 2000403) ∧
    -Real.log (2000000 / 2000403) ≤ (5037 / 25000000) := by
  have h := checkLog_sound (w := (403 / 4000403)) (n := 12)
    (lo := (201479 / 1000000000)) (hi := (5037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000403 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000403 / 2000000) = 1/(2000000 / 2000403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6999 : Bounds (201479 / 1000000000) (5037 / 25000000) (Real.log (2000403 / 2000000)) := by
  have h := reflection_log_6999_neg
  have he : Real.log (2000403 / 2000000) = -Real.log (2000000 / 2000403) := by
    rw [show ((2000403 / 2000000) : ℝ) = ((2000000 / 2000403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7000_neg : (2519 / 12500000) ≤ -Real.log (1999597 / 2000000) ∧
    -Real.log (1999597 / 2000000) ≤ (201521 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 3999597)) (n := 12)
    (lo := (2519 / 12500000)) (hi := (201521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999597) = 1/(1999597 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7000 : Bounds (-201521 / 1000000000) (-2519 / 12500000) (Real.log (1999597 / 2000000)) := by
  have h := reflection_log_7000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7001_neg : (48173457 / 500000000) ≤ -Real.log (1000000 / 1101141) ∧
    -Real.log (1000000 / 1101141) ≤ (19269383 / 200000000) := by
  have h := checkLog_sound (w := (101141 / 2101141)) (n := 12)
    (lo := (48173457 / 500000000)) (hi := (19269383 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101141 / 1000000) = 1/(1000000 / 1101141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7001 : Bounds (48173457 / 500000000) (19269383 / 200000000) (Real.log (1101141 / 1000000)) := by
  have h := reflection_log_7001_neg
  have he : Real.log (1101141 / 1000000) = -Real.log (1000000 / 1101141) := by
    rw [show ((1101141 / 1000000) : ℝ) = ((1000000 / 1101141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7002_neg : (106629097 / 1000000000) ≤ -Real.log (898859 / 1000000) ∧
    -Real.log (898859 / 1000000) ≤ (53314549 / 500000000) := by
  have h := checkLog_sound (w := (101141 / 1898859)) (n := 12)
    (lo := (106629097 / 1000000000)) (hi := (53314549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898859) = 1/(898859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7002 : Bounds (-53314549 / 500000000) (-106629097 / 1000000000) (Real.log (898859 / 1000000)) := by
  have h := reflection_log_7002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7003_neg : (19352189 / 200000000) ≤ -Real.log (1000000 / 1101597) ∧
    -Real.log (1000000 / 1101597) ≤ (48380473 / 500000000) := by
  have h := checkLog_sound (w := (101597 / 2101597)) (n := 12)
    (lo := (19352189 / 200000000)) (hi := (48380473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101597 / 1000000) = 1/(1000000 / 1101597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7003 : Bounds (19352189 / 200000000) (48380473 / 500000000) (Real.log (1101597 / 1000000)) := by
  have h := reflection_log_7003_neg
  have he : Real.log (1101597 / 1000000) = -Real.log (1000000 / 1101597) := by
    rw [show ((1101597 / 1000000) : ℝ) = ((1000000 / 1101597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7004_neg : (13392067 / 125000000) ≤ -Real.log (898403 / 1000000) ∧
    -Real.log (898403 / 1000000) ≤ (107136537 / 1000000000) := by
  have h := checkLog_sound (w := (101597 / 1898403)) (n := 12)
    (lo := (13392067 / 125000000)) (hi := (107136537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898403) = 1/(898403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7004 : Bounds (-107136537 / 1000000000) (-13392067 / 125000000) (Real.log (898403 / 1000000)) := by
  have h := reflection_log_7004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7005_neg : (10375591 / 1000000000) ≤ -Real.log (989678049591 / 1000000000000) ∧
    -Real.log (989678049591 / 1000000000000) ≤ (1296949 / 125000000) := by
  have h := checkLog_sound (w := (10321950409 / 1989678049591)) (n := 12)
    (lo := (10375591 / 1000000000)) (hi := (1296949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989678049591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989678049591) = 1/(989678049591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7005 : Bounds (-1296949 / 125000000) (-10375591 / 1000000000) (Real.log (989678049591 / 1000000000000)) := by
  have h := reflection_log_7005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7006_neg : (5141091 / 500000000) ≤ -Real.log (989770498119 / 1000000000000) ∧
    -Real.log (989770498119 / 1000000000000) ≤ (10282183 / 1000000000) := by
  have h := checkLog_sound (w := (10229501881 / 1989770498119)) (n := 12)
    (lo := (5141091 / 500000000)) (hi := (10282183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989770498119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989770498119) = 1/(989770498119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7006 : Bounds (-10282183 / 1000000000) (-5141091 / 500000000) (Real.log (989770498119 / 1000000000000)) := by
  have h := reflection_log_7006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7007_neg : (50744003 / 250000000) ≤ -Real.log (250000000000 / 306260770599) ∧
    -Real.log (250000000000 / 306260770599) ≤ (202976013 / 1000000000) := by
  have h := checkLog_sound (w := (56260770599 / 556260770599)) (n := 12)
    (lo := (50744003 / 250000000)) (hi := (202976013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306260770599 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306260770599 / 250000000000) = 1/(250000000000 / 306260770599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7007 : Bounds (50744003 / 250000000) (202976013 / 1000000000) (Real.log (306260770599 / 250000000000)) := by
  have h := reflection_log_7007_neg
  have he : Real.log (306260770599 / 250000000000) = -Real.log (250000000000 / 306260770599) := by
    rw [show ((306260770599 / 250000000000) : ℝ) = ((250000000000 / 306260770599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7008_neg : (203897481 / 1000000000) ≤ -Real.log (125000000000 / 153271555193) ∧
    -Real.log (125000000000 / 153271555193) ≤ (101948741 / 500000000) := by
  have h := checkLog_sound (w := (28271555193 / 278271555193)) (n := 12)
    (lo := (203897481 / 1000000000)) (hi := (101948741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153271555193 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153271555193 / 125000000000) = 1/(125000000000 / 153271555193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7008 : Bounds (203897481 / 1000000000) (101948741 / 500000000) (Real.log (153271555193 / 125000000000)) := by
  have h := reflection_log_7008_neg
  have he : Real.log (153271555193 / 125000000000) = -Real.log (125000000000 / 153271555193) := by
    rw [show ((153271555193 / 125000000000) : ℝ) = ((125000000000 / 153271555193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7009_neg : (101887219 / 250000000) ≤ -Real.log (500000000000 / 751564455569) ∧
    -Real.log (500000000000 / 751564455569) ≤ (407548877 / 1000000000) := by
  have h := checkLog_sound (w := (251564455569 / 1251564455569)) (n := 12)
    (lo := (101887219 / 250000000)) (hi := (407548877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751564455569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751564455569 / 500000000000) = 1/(500000000000 / 751564455569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7009 : Bounds (101887219 / 250000000) (407548877 / 1000000000) (Real.log (751564455569 / 500000000000)) := by
  have h := reflection_log_7009_neg
  have he : Real.log (751564455569 / 500000000000) = -Real.log (500000000000 / 751564455569) := by
    rw [show ((751564455569 / 500000000000) : ℝ) = ((500000000000 / 751564455569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7010_neg : (408591087 / 1000000000) ≤ -Real.log (500000000000 / 752348152787) ∧
    -Real.log (500000000000 / 752348152787) ≤ (25536943 / 62500000) := by
  have h := checkLog_sound (w := (252348152787 / 1252348152787)) (n := 12)
    (lo := (408591087 / 1000000000)) (hi := (25536943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752348152787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752348152787 / 500000000000) = 1/(500000000000 / 752348152787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7010 : Bounds (408591087 / 1000000000) (25536943 / 62500000) (Real.log (752348152787 / 500000000000)) := by
  have h := reflection_log_7010_neg
  have he : Real.log (752348152787 / 500000000000) = -Real.log (500000000000 / 752348152787) := by
    rw [show ((752348152787 / 500000000000) : ℝ) = ((500000000000 / 752348152787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7011_neg : (45996709 / 250000000) ≤ -Real.log (500 / 601) ∧
    -Real.log (500 / 601) ≤ (183986837 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 1101)) (n := 12)
    (lo := (45996709 / 250000000)) (hi := (183986837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601 / 500) = 1/(500 / 601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7011 : Bounds (45996709 / 250000000) (183986837 / 1000000000) (Real.log (601 / 500)) := by
  have h := reflection_log_7011_neg
  have he : Real.log (601 / 500) = -Real.log (500 / 601) := by
    rw [show ((601 / 500) : ℝ) = ((500 / 601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7012_neg : (225646681 / 1000000000) ≤ -Real.log (399 / 500) ∧
    -Real.log (399 / 500) ≤ (112823341 / 500000000) := by
  have h := checkLog_sound (w := (101 / 899)) (n := 12)
    (lo := (225646681 / 1000000000)) (hi := (112823341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 399) = 1/(399 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7012 : Bounds (-112823341 / 500000000) (-225646681 / 1000000000) (Real.log (399 / 500)) := by
  have h := reflection_log_7012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7013_neg : (201979 / 1000000000) ≤ -Real.log (500000 / 500101) ∧
    -Real.log (500000 / 500101) ≤ (10099 / 50000000) := by
  have h := checkLog_sound (w := (101 / 1000101)) (n := 12)
    (lo := (201979 / 1000000000)) (hi := (10099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500101 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500101 / 500000) = 1/(500000 / 500101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7013 : Bounds (201979 / 1000000000) (10099 / 50000000) (Real.log (500101 / 500000)) := by
  have h := reflection_log_7013_neg
  have he : Real.log (500101 / 500000) = -Real.log (500000 / 500101) := by
    rw [show ((500101 / 500000) : ℝ) = ((500000 / 500101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7014_neg : (10101 / 50000000) ≤ -Real.log (499899 / 500000) ∧
    -Real.log (499899 / 500000) ≤ (202021 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 999899)) (n := 12)
    (lo := (10101 / 50000000)) (hi := (202021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499899) = 1/(499899 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7014 : Bounds (-202021 / 1000000000) (-10101 / 50000000) (Real.log (499899 / 500000)) := by
  have h := reflection_log_7014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7015_neg : (48289233 / 500000000) ≤ -Real.log (250000 / 275349) ∧
    -Real.log (250000 / 275349) ≤ (96578467 / 1000000000) := by
  have h := checkLog_sound (w := (25349 / 525349)) (n := 12)
    (lo := (48289233 / 500000000)) (hi := (96578467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275349 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275349 / 250000) = 1/(250000 / 275349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7015 : Bounds (48289233 / 500000000) (96578467 / 1000000000) (Real.log (275349 / 250000)) := by
  have h := reflection_log_7015_neg
  have he : Real.log (275349 / 250000) = -Real.log (250000 / 275349) := by
    rw [show ((275349 / 250000) : ℝ) = ((250000 / 275349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7016_neg : (10691283 / 100000000) ≤ -Real.log (224651 / 250000) ∧
    -Real.log (224651 / 250000) ≤ (106912831 / 1000000000) := by
  have h := checkLog_sound (w := (25349 / 474651)) (n := 12)
    (lo := (10691283 / 100000000)) (hi := (106912831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 224651) = 1/(224651 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7016 : Bounds (-106912831 / 1000000000) (-10691283 / 100000000) (Real.log (224651 / 250000)) := by
  have h := reflection_log_7016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7017_neg : (24248327 / 250000000) ≤ -Real.log (1000000 / 1101853) ∧
    -Real.log (1000000 / 1101853) ≤ (96993309 / 1000000000) := by
  have h := checkLog_sound (w := (101853 / 2101853)) (n := 12)
    (lo := (24248327 / 250000000)) (hi := (96993309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101853 / 1000000) = 1/(1000000 / 1101853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7017 : Bounds (24248327 / 250000000) (96993309 / 1000000000) (Real.log (1101853 / 1000000)) := by
  have h := reflection_log_7017_neg
  have he : Real.log (1101853 / 1000000) = -Real.log (1000000 / 1101853) := by
    rw [show ((1101853 / 1000000) : ℝ) = ((1000000 / 1101853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7018_neg : (53710763 / 500000000) ≤ -Real.log (898147 / 1000000) ∧
    -Real.log (898147 / 1000000) ≤ (107421527 / 1000000000) := by
  have h := checkLog_sound (w := (101853 / 1898147)) (n := 12)
    (lo := (53710763 / 500000000)) (hi := (107421527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898147) = 1/(898147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7018 : Bounds (-107421527 / 1000000000) (-53710763 / 500000000) (Real.log (898147 / 1000000)) := by
  have h := reflection_log_7018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7019_neg : (5214109 / 500000000) ≤ -Real.log (989625966391 / 1000000000000) ∧
    -Real.log (989625966391 / 1000000000000) ≤ (10428219 / 1000000000) := by
  have h := checkLog_sound (w := (10374033609 / 1989625966391)) (n := 12)
    (lo := (5214109 / 500000000)) (hi := (10428219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989625966391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989625966391) = 1/(989625966391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7019 : Bounds (-10428219 / 1000000000) (-5214109 / 500000000) (Real.log (989625966391 / 1000000000000)) := by
  have h := reflection_log_7019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7020_neg : (2583591 / 250000000) ≤ -Real.log (61857428199 / 62500000000) ∧
    -Real.log (61857428199 / 62500000000) ≤ (2066873 / 200000000) := by
  have h := checkLog_sound (w := (642571801 / 124357428199)) (n := 12)
    (lo := (2583591 / 250000000)) (hi := (2066873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61857428199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61857428199) = 1/(61857428199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7020 : Bounds (-2066873 / 200000000) (-2583591 / 250000000) (Real.log (61857428199 / 62500000000)) := by
  have h := reflection_log_7020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7021_neg : (203491297 / 1000000000) ≤ -Real.log (500000000000 / 612837245327) ∧
    -Real.log (500000000000 / 612837245327) ≤ (101745649 / 500000000) := by
  have h := checkLog_sound (w := (112837245327 / 1112837245327)) (n := 12)
    (lo := (203491297 / 1000000000)) (hi := (101745649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612837245327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612837245327 / 500000000000) = 1/(500000000000 / 612837245327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7021 : Bounds (203491297 / 1000000000) (101745649 / 500000000) (Real.log (612837245327 / 500000000000)) := by
  have h := reflection_log_7021_neg
  have he : Real.log (612837245327 / 500000000000) = -Real.log (500000000000 / 612837245327) := by
    rw [show ((612837245327 / 500000000000) : ℝ) = ((500000000000 / 612837245327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7022_neg : (102207417 / 500000000) ≤ -Real.log (62500000000 / 76675435647) ∧
    -Real.log (62500000000 / 76675435647) ≤ (40882967 / 200000000) := by
  have h := checkLog_sound (w := (14175435647 / 139175435647)) (n := 12)
    (lo := (102207417 / 500000000)) (hi := (40882967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76675435647 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76675435647 / 62500000000) = 1/(62500000000 / 76675435647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7022 : Bounds (102207417 / 500000000) (40882967 / 200000000) (Real.log (76675435647 / 62500000000)) := by
  have h := reflection_log_7022_neg
  have he : Real.log (76675435647 / 62500000000) = -Real.log (62500000000 / 76675435647) := by
    rw [show ((76675435647 / 62500000000) : ℝ) = ((62500000000 / 76675435647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7023_neg : (408591087 / 1000000000) ≤ -Real.log (250000000000 / 376174076393) ∧
    -Real.log (250000000000 / 376174076393) ≤ (25536943 / 62500000) := by
  have h := checkLog_sound (w := (126174076393 / 626174076393)) (n := 12)
    (lo := (408591087 / 1000000000)) (hi := (25536943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376174076393 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376174076393 / 250000000000) = 1/(250000000000 / 376174076393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7023 : Bounds (408591087 / 1000000000) (25536943 / 62500000) (Real.log (376174076393 / 250000000000)) := by
  have h := reflection_log_7023_neg
  have he : Real.log (376174076393 / 250000000000) = -Real.log (250000000000 / 376174076393) := by
    rw [show ((376174076393 / 250000000000) : ℝ) = ((250000000000 / 376174076393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7024_neg : (409633517 / 1000000000) ≤ -Real.log (500000000000 / 753132832081) ∧
    -Real.log (500000000000 / 753132832081) ≤ (204816759 / 500000000) := by
  have h := checkLog_sound (w := (253132832081 / 1253132832081)) (n := 12)
    (lo := (409633517 / 1000000000)) (hi := (204816759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753132832081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753132832081 / 500000000000) = 1/(500000000000 / 753132832081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7024 : Bounds (409633517 / 1000000000) (204816759 / 500000000) (Real.log (753132832081 / 500000000000)) := by
  have h := reflection_log_7024_neg
  have he : Real.log (753132832081 / 500000000000) = -Real.log (500000000000 / 753132832081) := by
    rw [show ((753132832081 / 500000000000) : ℝ) = ((500000000000 / 753132832081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7025_neg : (92201361 / 500000000) ≤ -Real.log (400 / 481) ∧
    -Real.log (400 / 481) ≤ (184402723 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 881)) (n := 12)
    (lo := (92201361 / 500000000)) (hi := (184402723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481 / 400) = 1/(400 / 481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7025 : Bounds (92201361 / 500000000) (184402723 / 1000000000) (Real.log (481 / 400)) := by
  have h := reflection_log_7025_neg
  have he : Real.log (481 / 400) = -Real.log (400 / 481) := by
    rw [show ((481 / 400) : ℝ) = ((400 / 481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7026_neg : (56568361 / 250000000) ≤ -Real.log (319 / 400) ∧
    -Real.log (319 / 400) ≤ (45254689 / 200000000) := by
  have h := checkLog_sound (w := (81 / 719)) (n := 12)
    (lo := (56568361 / 250000000)) (hi := (45254689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 319) = 1/(319 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7026 : Bounds (-45254689 / 200000000) (-56568361 / 250000000) (Real.log (319 / 400)) := by
  have h := reflection_log_7026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7027_neg : (202479 / 1000000000) ≤ -Real.log (400000 / 400081) ∧
    -Real.log (400000 / 400081) ≤ (2531 / 12500000) := by
  have h := checkLog_sound (w := (81 / 800081)) (n := 12)
    (lo := (202479 / 1000000000)) (hi := (2531 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400081 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400081 / 400000) = 1/(400000 / 400081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7027 : Bounds (202479 / 1000000000) (2531 / 12500000) (Real.log (400081 / 400000)) := by
  have h := reflection_log_7027_neg
  have he : Real.log (400081 / 400000) = -Real.log (400000 / 400081) := by
    rw [show ((400081 / 400000) : ℝ) = ((400000 / 400081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7028_neg : (5063 / 25000000) ≤ -Real.log (399919 / 400000) ∧
    -Real.log (399919 / 400000) ≤ (202521 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 799919)) (n := 12)
    (lo := (5063 / 25000000)) (hi := (202521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399919) = 1/(399919 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7028 : Bounds (-202521 / 1000000000) (-5063 / 25000000) (Real.log (399919 / 400000)) := by
  have h := reflection_log_7028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7029_neg : (96809963 / 1000000000) ≤ -Real.log (1000000 / 1101651) ∧
    -Real.log (1000000 / 1101651) ≤ (24202491 / 250000000) := by
  have h := checkLog_sound (w := (101651 / 2101651)) (n := 12)
    (lo := (96809963 / 1000000000)) (hi := (24202491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101651 / 1000000) = 1/(1000000 / 1101651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7029 : Bounds (96809963 / 1000000000) (24202491 / 250000000) (Real.log (1101651 / 1000000)) := by
  have h := reflection_log_7029_neg
  have he : Real.log (1101651 / 1000000) = -Real.log (1000000 / 1101651) := by
    rw [show ((1101651 / 1000000) : ℝ) = ((1000000 / 1101651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7030_neg : (26799161 / 250000000) ≤ -Real.log (898349 / 1000000) ∧
    -Real.log (898349 / 1000000) ≤ (21439329 / 200000000) := by
  have h := checkLog_sound (w := (101651 / 1898349)) (n := 12)
    (lo := (26799161 / 250000000)) (hi := (21439329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898349) = 1/(898349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7030 : Bounds (-21439329 / 200000000) (-26799161 / 250000000) (Real.log (898349 / 1000000)) := by
  have h := reflection_log_7030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7031_neg : (6076601 / 62500000) ≤ -Real.log (1000000 / 1102109) ∧
    -Real.log (1000000 / 1102109) ≤ (97225617 / 1000000000) := by
  have h := checkLog_sound (w := (102109 / 2102109)) (n := 12)
    (lo := (6076601 / 62500000)) (hi := (97225617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1102109 / 1000000) = 1/(1000000 / 1102109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7031 : Bounds (6076601 / 62500000) (97225617 / 1000000000) (Real.log (1102109 / 1000000)) := by
  have h := reflection_log_7031_neg
  have he : Real.log (1102109 / 1000000) = -Real.log (1000000 / 1102109) := by
    rw [show ((1102109 / 1000000) : ℝ) = ((1000000 / 1102109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7032_neg : (53853299 / 500000000) ≤ -Real.log (897891 / 1000000) ∧
    -Real.log (897891 / 1000000) ≤ (107706599 / 1000000000) := by
  have h := checkLog_sound (w := (102109 / 1897891)) (n := 12)
    (lo := (53853299 / 500000000)) (hi := (107706599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 897891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 897891) = 1/(897891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7032 : Bounds (-107706599 / 1000000000) (-53853299 / 500000000) (Real.log (897891 / 1000000)) := by
  have h := reflection_log_7032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7033_neg : (10480981 / 1000000000) ≤ -Real.log (989573752119 / 1000000000000) ∧
    -Real.log (989573752119 / 1000000000000) ≤ (5240491 / 500000000) := by
  have h := checkLog_sound (w := (10426247881 / 1989573752119)) (n := 12)
    (lo := (10480981 / 1000000000)) (hi := (5240491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989573752119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989573752119) = 1/(989573752119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7033 : Bounds (-5240491 / 500000000) (-10480981 / 1000000000) (Real.log (989573752119 / 1000000000000)) := by
  have h := reflection_log_7033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7034_neg : (10386681 / 1000000000) ≤ -Real.log (989667074199 / 1000000000000) ∧
    -Real.log (989667074199 / 1000000000000) ≤ (5193341 / 500000000) := by
  have h := checkLog_sound (w := (10332925801 / 1989667074199)) (n := 12)
    (lo := (10386681 / 1000000000)) (hi := (5193341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989667074199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989667074199) = 1/(989667074199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7034 : Bounds (-5193341 / 500000000) (-10386681 / 1000000000) (Real.log (989667074199 / 1000000000000)) := by
  have h := reflection_log_7034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7035_neg : (12750413 / 62500000) ≤ -Real.log (500000000000 / 613153128683) ∧
    -Real.log (500000000000 / 613153128683) ≤ (204006609 / 1000000000) := by
  have h := checkLog_sound (w := (113153128683 / 1113153128683)) (n := 12)
    (lo := (12750413 / 62500000)) (hi := (204006609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613153128683 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613153128683 / 500000000000) = 1/(500000000000 / 613153128683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7035 : Bounds (12750413 / 62500000) (204006609 / 1000000000) (Real.log (613153128683 / 500000000000)) := by
  have h := reflection_log_7035_neg
  have he : Real.log (613153128683 / 500000000000) = -Real.log (500000000000 / 613153128683) := by
    rw [show ((613153128683 / 500000000000) : ℝ) = ((500000000000 / 613153128683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7036_neg : (40986443 / 200000000) ≤ -Real.log (125000000000 / 153430232623) ∧
    -Real.log (125000000000 / 153430232623) ≤ (25616527 / 125000000) := by
  have h := checkLog_sound (w := (28430232623 / 278430232623)) (n := 12)
    (lo := (40986443 / 200000000)) (hi := (25616527 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153430232623 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153430232623 / 125000000000) = 1/(125000000000 / 153430232623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7036 : Bounds (40986443 / 200000000) (25616527 / 125000000) (Real.log (153430232623 / 125000000000)) := by
  have h := reflection_log_7036_neg
  have he : Real.log (153430232623 / 125000000000) = -Real.log (125000000000 / 153430232623) := by
    rw [show ((153430232623 / 125000000000) : ℝ) = ((125000000000 / 153430232623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7037_neg : (409633517 / 1000000000) ≤ -Real.log (6250000000 / 9414160401) ∧
    -Real.log (6250000000 / 9414160401) ≤ (204816759 / 500000000) := by
  have h := checkLog_sound (w := (3164160401 / 15664160401)) (n := 12)
    (lo := (409633517 / 1000000000)) (hi := (204816759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9414160401 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9414160401 / 6250000000) = 1/(6250000000 / 9414160401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7037 : Bounds (409633517 / 1000000000) (204816759 / 500000000) (Real.log (9414160401 / 6250000000)) := by
  have h := reflection_log_7037_neg
  have he : Real.log (9414160401 / 6250000000) = -Real.log (6250000000 / 9414160401) := by
    rw [show ((9414160401 / 6250000000) : ℝ) = ((6250000000 / 9414160401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7038_neg : (410676167 / 1000000000) ≤ -Real.log (250000000000 / 376959247649) ∧
    -Real.log (250000000000 / 376959247649) ≤ (51334521 / 125000000) := by
  have h := checkLog_sound (w := (126959247649 / 626959247649)) (n := 12)
    (lo := (410676167 / 1000000000)) (hi := (51334521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376959247649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376959247649 / 250000000000) = 1/(250000000000 / 376959247649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7038 : Bounds (410676167 / 1000000000) (51334521 / 125000000) (Real.log (376959247649 / 250000000000)) := by
  have h := reflection_log_7038_neg
  have he : Real.log (376959247649 / 250000000000) = -Real.log (250000000000 / 376959247649) := by
    rw [show ((376959247649 / 250000000000) : ℝ) = ((250000000000 / 376959247649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7039_neg : (46204609 / 250000000) ≤ -Real.log (1000 / 1203) ∧
    -Real.log (1000 / 1203) ≤ (184818437 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2203)) (n := 12)
    (lo := (46204609 / 250000000)) (hi := (184818437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203 / 1000) = 1/(1000 / 1203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7039 : Bounds (46204609 / 250000000) (184818437 / 1000000000) (Real.log (1203 / 1000)) := by
  have h := reflection_log_7039_neg
  have he : Real.log (1203 / 1000) = -Real.log (1000 / 1203) := by
    rw [show ((1203 / 1000) : ℝ) = ((1000 / 1203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
