import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13568_neg : (171821279 / 1000000000) ≤ -Real.log (842129665759 / 1000000000000) ∧
    -Real.log (842129665759 / 1000000000000) ≤ (1073883 / 6250000) := by
  have h := checkLog_sound (w := (157870334241 / 1842129665759)) (n := 12)
    (lo := (171821279 / 1000000000)) (hi := (1073883 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 842129665759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 842129665759) = 1/(842129665759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13568 : Bounds (-1073883 / 6250000) (-171821279 / 1000000000) (Real.log (842129665759 / 1000000000000)) := by
  have h := reflection_log_13568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13569_neg : (840946393 / 1000000000) ≤ -Real.log (500000000000 / 1159280104733) ∧
    -Real.log (500000000000 / 1159280104733) ≤ (168189279 / 200000000) := by
  have h := checkLog_sound (w := (159280104733 / 2159280104733)) (n := 12)
    (lo := (147799213 / 1000000000)) (hi := (73899607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159280104733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1159280104733 / 1000000000000) = 1/(500000000000 / 1159280104733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13569 : Bounds (840946393 / 1000000000) (168189279 / 200000000) (Real.log (1159280104733 / 500000000000)) := by
  have h := reflection_log_13569_neg
  have he : Real.log (1159280104733 / 500000000000) = -Real.log (500000000000 / 1159280104733) := by
    rw [show ((1159280104733 / 500000000000) : ℝ) = ((500000000000 / 1159280104733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13570_neg : (847374051 / 1000000000) ≤ -Real.log (500000000000 / 1166755560297) ∧
    -Real.log (500000000000 / 1166755560297) ≤ (847374053 / 1000000000) := by
  have h := checkLog_sound (w := (166755560297 / 2166755560297)) (n := 12)
    (lo := (154226871 / 1000000000)) (hi := (19278359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166755560297 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166755560297 / 1000000000000) = 1/(500000000000 / 1166755560297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13570 : Bounds (847374051 / 1000000000) (847374053 / 1000000000) (Real.log (1166755560297 / 500000000000)) := by
  have h := reflection_log_13570_neg
  have he : Real.log (1166755560297 / 500000000000) = -Real.log (500000000000 / 1166755560297) := by
    rw [show ((1166755560297 / 500000000000) : ℝ) = ((500000000000 / 1166755560297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13571_neg : (22484713 / 12500000) ≤ -Real.log (500000000000 / 3021126760563) ∧
    -Real.log (500000000000 / 3021126760563) ≤ (1798777043 / 1000000000) := by
  have h := checkLog_sound (w := (1021126760563 / 5021126760563)) (n := 12)
    (lo := (10312067 / 25000000)) (hi := (412482681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3021126760563 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3021126760563 / 2000000000000) = 1/(500000000000 / 3021126760563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13571 : Bounds (22484713 / 12500000) (1798777043 / 1000000000) (Real.log (3021126760563 / 500000000000)) := by
  have h := reflection_log_13571_neg
  have he : Real.log (3021126760563 / 500000000000) = -Real.log (500000000000 / 3021126760563) := by
    rw [show ((3021126760563 / 500000000000) : ℝ) = ((500000000000 / 3021126760563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13572_neg : (905571667 / 500000000) ≤ -Real.log (50000000000 / 305871886121) ∧
    -Real.log (50000000000 / 305871886121) ≤ (1811143337 / 1000000000) := by
  have h := checkLog_sound (w := (105871886121 / 505871886121)) (n := 12)
    (lo := (212424487 / 500000000)) (hi := (16993959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305871886121 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(305871886121 / 200000000000) = 1/(50000000000 / 305871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13572 : Bounds (905571667 / 500000000) (1811143337 / 1000000000) (Real.log (305871886121 / 50000000000)) := by
  have h := reflection_log_13572_neg
  have he : Real.log (305871886121 / 50000000000) = -Real.log (50000000000 / 305871886121) := by
    rw [show ((305871886121 / 50000000000) : ℝ) = ((50000000000 / 305871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13573_neg : (271743203 / 500000000) ≤ -Real.log (500 / 861) ∧
    -Real.log (500 / 861) ≤ (543486407 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1361)) (n := 12)
    (lo := (271743203 / 500000000)) (hi := (543486407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 500) = 1/(500 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13573 : Bounds (271743203 / 500000000) (543486407 / 1000000000) (Real.log (861 / 500)) := by
  have h := reflection_log_13573_neg
  have he : Real.log (861 / 500) = -Real.log (500 / 861) := by
    rw [show ((861 / 500) : ℝ) = ((500 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13574_neg : (320033541 / 250000000) ≤ -Real.log (139 / 500) ∧
    -Real.log (139 / 500) ≤ (640067083 / 500000000) := by
  have h := checkLog_sound (w := (111 / 389)) (n := 12)
    (lo := (73373373 / 125000000)) (hi := (117397397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 139) = 1/(139 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13574 : Bounds (-640067083 / 500000000) (-320033541 / 250000000) (Real.log (139 / 500)) := by
  have h := reflection_log_13574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13575_neg : (721739 / 1000000000) ≤ -Real.log (500000 / 500361) ∧
    -Real.log (500000 / 500361) ≤ (36087 / 50000000) := by
  have h := checkLog_sound (w := (361 / 1000361)) (n := 12)
    (lo := (721739 / 1000000000)) (hi := (36087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500361 / 500000) = 1/(500000 / 500361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13575 : Bounds (721739 / 1000000000) (36087 / 50000000) (Real.log (500361 / 500000)) := by
  have h := reflection_log_13575_neg
  have he : Real.log (500361 / 500000) = -Real.log (500000 / 500361) := by
    rw [show ((500361 / 500000) : ℝ) = ((500000 / 500361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13576_neg : (36113 / 50000000) ≤ -Real.log (499639 / 500000) ∧
    -Real.log (499639 / 500000) ≤ (722261 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 999639)) (n := 12)
    (lo := (36113 / 50000000)) (hi := (722261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499639) = 1/(499639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13576 : Bounds (-722261 / 1000000000) (-36113 / 50000000) (Real.log (499639 / 500000)) := by
  have h := reflection_log_13576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13577_neg : (168023573 / 500000000) ≤ -Real.log (200000 / 279881) ∧
    -Real.log (200000 / 279881) ≤ (336047147 / 1000000000) := by
  have h := checkLog_sound (w := (79881 / 479881)) (n := 12)
    (lo := (168023573 / 500000000)) (hi := (336047147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279881 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279881 / 200000) = 1/(200000 / 279881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13577 : Bounds (168023573 / 500000000) (336047147 / 1000000000) (Real.log (279881 / 200000)) := by
  have h := reflection_log_13577_neg
  have he : Real.log (279881 / 200000) = -Real.log (200000 / 279881) := by
    rw [show ((279881 / 200000) : ℝ) = ((200000 / 279881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13578_neg : (31864653 / 62500000) ≤ -Real.log (120119 / 200000) ∧
    -Real.log (120119 / 200000) ≤ (509834449 / 1000000000) := by
  have h := checkLog_sound (w := (79881 / 320119)) (n := 12)
    (lo := (31864653 / 62500000)) (hi := (509834449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120119) = 1/(120119 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13578 : Bounds (-509834449 / 1000000000) (-31864653 / 62500000) (Real.log (120119 / 200000)) := by
  have h := reflection_log_13578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13579_neg : (84495631 / 250000000) ≤ -Real.log (250000 / 350529) ∧
    -Real.log (250000 / 350529) ≤ (13519301 / 40000000) := by
  have h := checkLog_sound (w := (100529 / 600529)) (n := 12)
    (lo := (84495631 / 250000000)) (hi := (13519301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350529 / 250000) = 1/(250000 / 350529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13579 : Bounds (84495631 / 250000000) (13519301 / 40000000) (Real.log (350529 / 250000)) := by
  have h := reflection_log_13579_neg
  have he : Real.log (350529 / 250000) = -Real.log (250000 / 350529) := by
    rw [show ((350529 / 250000) : ℝ) = ((250000 / 350529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13580_neg : (514358523 / 1000000000) ≤ -Real.log (149471 / 250000) ∧
    -Real.log (149471 / 250000) ≤ (128589631 / 250000000) := by
  have h := checkLog_sound (w := (100529 / 399471)) (n := 12)
    (lo := (514358523 / 1000000000)) (hi := (128589631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149471) = 1/(149471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13580 : Bounds (-128589631 / 250000000) (-514358523 / 1000000000) (Real.log (149471 / 250000)) := by
  have h := reflection_log_13580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13581_neg : (176375999 / 1000000000) ≤ -Real.log (52393920159 / 62500000000) ∧
    -Real.log (52393920159 / 62500000000) ≤ (22047 / 125000) := by
  have h := checkLog_sound (w := (10106079841 / 114893920159)) (n := 12)
    (lo := (176375999 / 1000000000)) (hi := (22047 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52393920159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52393920159) = 1/(52393920159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13581 : Bounds (-22047 / 125000) (-176375999 / 1000000000) (Real.log (52393920159 / 62500000000)) := by
  have h := reflection_log_13581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13582_neg : (86893651 / 500000000) ≤ -Real.log (33619025839 / 40000000000) ∧
    -Real.log (33619025839 / 40000000000) ≤ (173787303 / 1000000000) := by
  have h := checkLog_sound (w := (6380974161 / 73619025839)) (n := 12)
    (lo := (86893651 / 500000000)) (hi := (173787303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33619025839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33619025839) = 1/(33619025839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13582 : Bounds (-173787303 / 1000000000) (-86893651 / 500000000) (Real.log (33619025839 / 40000000000)) := by
  have h := reflection_log_13582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13583_neg : (422940797 / 500000000) ≤ -Real.log (500000000000 / 1165015526269) ∧
    -Real.log (500000000000 / 1165015526269) ≤ (211470399 / 250000000) := by
  have h := checkLog_sound (w := (165015526269 / 2165015526269)) (n := 12)
    (lo := (76367207 / 500000000)) (hi := (30546883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165015526269 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165015526269 / 1000000000000) = 1/(500000000000 / 1165015526269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13583 : Bounds (422940797 / 500000000) (211470399 / 250000000) (Real.log (1165015526269 / 500000000000)) := by
  have h := reflection_log_13583_neg
  have he : Real.log (1165015526269 / 500000000000) = -Real.log (500000000000 / 1165015526269) := by
    rw [show ((1165015526269 / 500000000000) : ℝ) = ((500000000000 / 1165015526269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13584_neg : (852341047 / 1000000000) ≤ -Real.log (500000000000 / 1172565246771) ∧
    -Real.log (500000000000 / 1172565246771) ≤ (852341049 / 1000000000) := by
  have h := checkLog_sound (w := (172565246771 / 2172565246771)) (n := 12)
    (lo := (159193867 / 1000000000)) (hi := (39798467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172565246771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1172565246771 / 1000000000000) = 1/(500000000000 / 1172565246771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13584 : Bounds (852341047 / 1000000000) (852341049 / 1000000000) (Real.log (1172565246771 / 500000000000)) := by
  have h := reflection_log_13584_neg
  have he : Real.log (1172565246771 / 500000000000) = -Real.log (500000000000 / 1172565246771) := by
    rw [show ((1172565246771 / 500000000000) : ℝ) = ((500000000000 / 1172565246771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13585_neg : (905571667 / 500000000) ≤ -Real.log (500000000000 / 3058718861209) ∧
    -Real.log (500000000000 / 3058718861209) ≤ (1811143337 / 1000000000) := by
  have h := checkLog_sound (w := (1058718861209 / 5058718861209)) (n := 12)
    (lo := (212424487 / 500000000)) (hi := (16993959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3058718861209 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3058718861209 / 2000000000000) = 1/(500000000000 / 3058718861209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13585 : Bounds (905571667 / 500000000) (1811143337 / 1000000000) (Real.log (3058718861209 / 500000000000)) := by
  have h := reflection_log_13585_neg
  have he : Real.log (3058718861209 / 500000000000) = -Real.log (500000000000 / 3058718861209) := by
    rw [show ((3058718861209 / 500000000000) : ℝ) = ((500000000000 / 3058718861209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13586_neg : (182362057 / 100000000) ≤ -Real.log (500000000000 / 3097122302159) ∧
    -Real.log (500000000000 / 3097122302159) ≤ (1823620573 / 1000000000) := by
  have h := checkLog_sound (w := (1097122302159 / 5097122302159)) (n := 12)
    (lo := (43732621 / 100000000)) (hi := (437326211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3097122302159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3097122302159 / 2000000000000) = 1/(500000000000 / 3097122302159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13586 : Bounds (182362057 / 100000000) (1823620573 / 1000000000) (Real.log (3097122302159 / 500000000000)) := by
  have h := reflection_log_13586_neg
  have he : Real.log (3097122302159 / 500000000000) = -Real.log (500000000000 / 3097122302159) := by
    rw [show ((3097122302159 / 500000000000) : ℝ) = ((500000000000 / 3097122302159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13587_neg : (10904541 / 20000000) ≤ -Real.log (40 / 69) ∧
    -Real.log (40 / 69) ≤ (545227051 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 109)) (n := 12)
    (lo := (10904541 / 20000000)) (hi := (545227051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69 / 40) = 1/(40 / 69) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13587 : Bounds (10904541 / 20000000) (545227051 / 1000000000) (Real.log (69 / 40)) := by
  have h := reflection_log_13587_neg
  have he : Real.log (69 / 40) = -Real.log (40 / 69) := by
    rw [show ((69 / 40) : ℝ) = ((40 / 69) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13588_neg : (64549209 / 50000000) ≤ -Real.log (11 / 40) ∧
    -Real.log (11 / 40) ≤ (645492091 / 500000000) := by
  have h := checkLog_sound (w := (9 / 31)) (n := 12)
    (lo := (597837 / 1000000)) (hi := (597837001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 11) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 11) = 1/(11 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13588 : Bounds (-645492091 / 500000000) (-64549209 / 50000000) (Real.log (11 / 40)) := by
  have h := reflection_log_13588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13589_neg : (724737 / 1000000000) ≤ -Real.log (40000 / 40029) ∧
    -Real.log (40000 / 40029) ≤ (362369 / 500000000) := by
  have h := checkLog_sound (w := (29 / 80029)) (n := 12)
    (lo := (724737 / 1000000000)) (hi := (362369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40029 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40029 / 40000) = 1/(40000 / 40029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13589 : Bounds (724737 / 1000000000) (362369 / 500000000) (Real.log (40029 / 40000)) := by
  have h := reflection_log_13589_neg
  have he : Real.log (40029 / 40000) = -Real.log (40000 / 40029) := by
    rw [show ((40029 / 40000) : ℝ) = ((40000 / 40029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13590_neg : (362631 / 500000000) ≤ -Real.log (39971 / 40000) ∧
    -Real.log (39971 / 40000) ≤ (725263 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 79971)) (n := 12)
    (lo := (362631 / 500000000)) (hi := (725263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39971) = 1/(39971 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13590 : Bounds (-725263 / 1000000000) (-362631 / 500000000) (Real.log (39971 / 40000)) := by
  have h := reflection_log_13590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13591_neg : (67506763 / 200000000) ≤ -Real.log (1000000 / 1401487) ∧
    -Real.log (1000000 / 1401487) ≤ (42191727 / 125000000) := by
  have h := checkLog_sound (w := (401487 / 2401487)) (n := 12)
    (lo := (67506763 / 200000000)) (hi := (42191727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401487 / 1000000) = 1/(1000000 / 1401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13591 : Bounds (67506763 / 200000000) (42191727 / 125000000) (Real.log (1401487 / 1000000)) := by
  have h := reflection_log_13591_neg
  have he : Real.log (1401487 / 1000000) = -Real.log (1000000 / 1401487) := by
    rw [show ((1401487 / 1000000) : ℝ) = ((1000000 / 1401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13592_neg : (513307033 / 1000000000) ≤ -Real.log (598513 / 1000000) ∧
    -Real.log (598513 / 1000000) ≤ (256653517 / 500000000) := by
  have h := checkLog_sound (w := (401487 / 1598513)) (n := 12)
    (lo := (513307033 / 1000000000)) (hi := (256653517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 598513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 598513) = 1/(598513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13592 : Bounds (-256653517 / 500000000) (-513307033 / 1000000000) (Real.log (598513 / 1000000)) := by
  have h := reflection_log_13592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13593_neg : (33947273 / 100000000) ≤ -Real.log (1000000 / 1404207) ∧
    -Real.log (1000000 / 1404207) ≤ (339472731 / 1000000000) := by
  have h := checkLog_sound (w := (404207 / 2404207)) (n := 12)
    (lo := (33947273 / 100000000)) (hi := (339472731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1404207 / 1000000) = 1/(1000000 / 1404207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13593 : Bounds (33947273 / 100000000) (339472731 / 1000000000) (Real.log (1404207 / 1000000)) := by
  have h := reflection_log_13593_neg
  have he : Real.log (1404207 / 1000000) = -Real.log (1000000 / 1404207) := by
    rw [show ((1404207 / 1000000) : ℝ) = ((1000000 / 1404207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13594_neg : (517861987 / 1000000000) ≤ -Real.log (595793 / 1000000) ∧
    -Real.log (595793 / 1000000) ≤ (129465497 / 250000000) := by
  have h := checkLog_sound (w := (404207 / 1595793)) (n := 12)
    (lo := (517861987 / 1000000000)) (hi := (129465497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 595793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 595793) = 1/(595793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13594 : Bounds (-129465497 / 250000000) (-517861987 / 1000000000) (Real.log (595793 / 1000000)) := by
  have h := reflection_log_13594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13595_neg : (178389257 / 1000000000) ≤ -Real.log (836616701151 / 1000000000000) ∧
    -Real.log (836616701151 / 1000000000000) ≤ (89194629 / 500000000) := by
  have h := checkLog_sound (w := (163383298849 / 1836616701151)) (n := 12)
    (lo := (178389257 / 1000000000)) (hi := (89194629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 836616701151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 836616701151) = 1/(836616701151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13595 : Bounds (-89194629 / 500000000) (-178389257 / 1000000000) (Real.log (836616701151 / 1000000000000)) := by
  have h := reflection_log_13595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13596_neg : (175773217 / 1000000000) ≤ -Real.log (838808188831 / 1000000000000) ∧
    -Real.log (838808188831 / 1000000000000) ≤ (87886609 / 500000000) := by
  have h := checkLog_sound (w := (161191811169 / 1838808188831)) (n := 12)
    (lo := (175773217 / 1000000000)) (hi := (87886609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 838808188831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 838808188831) = 1/(838808188831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13596 : Bounds (-87886609 / 500000000) (-175773217 / 1000000000) (Real.log (838808188831 / 1000000000000)) := by
  have h := reflection_log_13596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13597_neg : (53177553 / 62500000) ≤ -Real.log (500000000000 / 1170807484549) ∧
    -Real.log (500000000000 / 1170807484549) ≤ (17016817 / 20000000) := by
  have h := checkLog_sound (w := (170807484549 / 2170807484549)) (n := 12)
    (lo := (39423417 / 250000000)) (hi := (157693669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170807484549 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1170807484549 / 1000000000000) = 1/(500000000000 / 1170807484549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13597 : Bounds (53177553 / 62500000) (17016817 / 20000000) (Real.log (1170807484549 / 500000000000)) := by
  have h := reflection_log_13597_neg
  have he : Real.log (1170807484549 / 500000000000) = -Real.log (500000000000 / 1170807484549) := by
    rw [show ((1170807484549 / 500000000000) : ℝ) = ((500000000000 / 1170807484549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13598_neg : (857334717 / 1000000000) ≤ -Real.log (500000000000 / 1178435295481) ∧
    -Real.log (500000000000 / 1178435295481) ≤ (857334719 / 1000000000) := by
  have h := checkLog_sound (w := (178435295481 / 2178435295481)) (n := 12)
    (lo := (164187537 / 1000000000)) (hi := (82093769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178435295481 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1178435295481 / 1000000000000) = 1/(500000000000 / 1178435295481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13598 : Bounds (857334717 / 1000000000) (857334719 / 1000000000) (Real.log (1178435295481 / 500000000000)) := by
  have h := reflection_log_13598_neg
  have he : Real.log (1178435295481 / 500000000000) = -Real.log (500000000000 / 1178435295481) := by
    rw [show ((1178435295481 / 500000000000) : ℝ) = ((500000000000 / 1178435295481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13599_neg : (182362057 / 100000000) ≤ -Real.log (250000000000 / 1548561151079) ∧
    -Real.log (250000000000 / 1548561151079) ≤ (1823620573 / 1000000000) := by
  have h := checkLog_sound (w := (548561151079 / 2548561151079)) (n := 12)
    (lo := (43732621 / 100000000)) (hi := (437326211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1548561151079 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1548561151079 / 1000000000000) = 1/(250000000000 / 1548561151079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13599 : Bounds (182362057 / 100000000) (1823620573 / 1000000000) (Real.log (1548561151079 / 250000000000)) := by
  have h := reflection_log_13599_neg
  have he : Real.log (1548561151079 / 250000000000) = -Real.log (250000000000 / 1548561151079) := by
    rw [show ((1548561151079 / 250000000000) : ℝ) = ((250000000000 / 1548561151079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13600_neg : (183621123 / 100000000) ≤ -Real.log (125000000000 / 784090909091) ∧
    -Real.log (125000000000 / 784090909091) ≤ (1836211233 / 1000000000) := by
  have h := checkLog_sound (w := (284090909091 / 1284090909091)) (n := 12)
    (lo := (44991687 / 100000000)) (hi := (449916871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784090909091 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(784090909091 / 500000000000) = 1/(125000000000 / 784090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13600 : Bounds (183621123 / 100000000) (1836211233 / 1000000000) (Real.log (784090909091 / 125000000000)) := by
  have h := reflection_log_13600_neg
  have he : Real.log (784090909091 / 125000000000) = -Real.log (125000000000 / 784090909091) := by
    rw [show ((784090909091 / 125000000000) : ℝ) = ((125000000000 / 784090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13601_neg : (54696467 / 100000000) ≤ -Real.log (125 / 216) ∧
    -Real.log (125 / 216) ≤ (546964671 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 341)) (n := 12)
    (lo := (54696467 / 100000000)) (hi := (546964671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216 / 125) = 1/(125 / 216) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13601 : Bounds (54696467 / 100000000) (546964671 / 1000000000) (Real.log (216 / 125)) := by
  have h := reflection_log_13601_neg
  have he : Real.log (216 / 125) = -Real.log (125 / 216) := by
    rw [show ((216 / 125) : ℝ) = ((125 / 216) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13602_neg : (325488303 / 250000000) ≤ -Real.log (34 / 125) ∧
    -Real.log (34 / 125) ≤ (650976607 / 500000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 68) = 1/(34 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13602 : Bounds (-650976607 / 500000000) (-325488303 / 250000000) (Real.log (34 / 125)) := by
  have h := reflection_log_13602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13603_neg : (145547 / 200000000) ≤ -Real.log (125000 / 125091) ∧
    -Real.log (125000 / 125091) ≤ (90967 / 125000000) := by
  have h := checkLog_sound (w := (91 / 250091)) (n := 12)
    (lo := (145547 / 200000000)) (hi := (90967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125091 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125091 / 125000) = 1/(125000 / 125091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13603 : Bounds (145547 / 200000000) (90967 / 125000000) (Real.log (125091 / 125000)) := by
  have h := reflection_log_13603_neg
  have he : Real.log (125091 / 125000) = -Real.log (125000 / 125091) := by
    rw [show ((125091 / 125000) : ℝ) = ((125000 / 125091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13604_neg : (145653 / 200000000) ≤ -Real.log (124909 / 125000) ∧
    -Real.log (124909 / 125000) ≤ (364133 / 500000000) := by
  have h := checkLog_sound (w := (91 / 249909)) (n := 12)
    (lo := (145653 / 200000000)) (hi := (364133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124909) = 1/(124909 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13604 : Bounds (-364133 / 500000000) (-145653 / 200000000) (Real.log (124909 / 125000)) := by
  have h := reflection_log_13604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13605_neg : (169511989 / 500000000) ≤ -Real.log (1000000 / 1403577) ∧
    -Real.log (1000000 / 1403577) ≤ (339023979 / 1000000000) := by
  have h := checkLog_sound (w := (403577 / 2403577)) (n := 12)
    (lo := (169511989 / 500000000)) (hi := (339023979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403577 / 1000000) = 1/(1000000 / 1403577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13605 : Bounds (169511989 / 500000000) (339023979 / 1000000000) (Real.log (1403577 / 1000000)) := by
  have h := reflection_log_13605_neg
  have he : Real.log (1403577 / 1000000) = -Real.log (1000000 / 1403577) := by
    rw [show ((1403577 / 1000000) : ℝ) = ((1000000 / 1403577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13606_neg : (129201283 / 250000000) ≤ -Real.log (596423 / 1000000) ∧
    -Real.log (596423 / 1000000) ≤ (516805133 / 1000000000) := by
  have h := checkLog_sound (w := (403577 / 1596423)) (n := 12)
    (lo := (129201283 / 250000000)) (hi := (516805133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 596423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 596423) = 1/(596423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13606 : Bounds (-516805133 / 1000000000) (-129201283 / 250000000) (Real.log (596423 / 1000000)) := by
  have h := reflection_log_13606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13607_neg : (340965697 / 1000000000) ≤ -Real.log (200000 / 281261) ∧
    -Real.log (200000 / 281261) ≤ (170482849 / 500000000) := by
  have h := checkLog_sound (w := (81261 / 481261)) (n := 12)
    (lo := (340965697 / 1000000000)) (hi := (170482849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281261 / 200000) = 1/(200000 / 281261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13607 : Bounds (340965697 / 1000000000) (170482849 / 500000000) (Real.log (281261 / 200000)) := by
  have h := reflection_log_13607_neg
  have he : Real.log (281261 / 200000) = -Real.log (200000 / 281261) := by
    rw [show ((281261 / 200000) : ℝ) = ((200000 / 281261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13608_neg : (521389559 / 1000000000) ≤ -Real.log (118739 / 200000) ∧
    -Real.log (118739 / 200000) ≤ (13034739 / 25000000) := by
  have h := checkLog_sound (w := (81261 / 318739)) (n := 12)
    (lo := (521389559 / 1000000000)) (hi := (13034739 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 118739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 118739) = 1/(118739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13608 : Bounds (-13034739 / 25000000) (-521389559 / 1000000000) (Real.log (118739 / 200000)) := by
  have h := reflection_log_13608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13609_neg : (90211931 / 500000000) ≤ -Real.log (33396649879 / 40000000000) ∧
    -Real.log (33396649879 / 40000000000) ≤ (180423863 / 1000000000) := by
  have h := checkLog_sound (w := (6603350121 / 73396649879)) (n := 12)
    (lo := (90211931 / 500000000)) (hi := (180423863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33396649879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33396649879) = 1/(33396649879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13609 : Bounds (-180423863 / 1000000000) (-90211931 / 500000000) (Real.log (33396649879 / 40000000000)) := by
  have h := reflection_log_13609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13610_neg : (177781153 / 1000000000) ≤ -Real.log (837125605071 / 1000000000000) ∧
    -Real.log (837125605071 / 1000000000000) ≤ (88890577 / 500000000) := by
  have h := checkLog_sound (w := (162874394929 / 1837125605071)) (n := 12)
    (lo := (177781153 / 1000000000)) (hi := (88890577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 837125605071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 837125605071) = 1/(837125605071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13610 : Bounds (-88890577 / 500000000) (-177781153 / 1000000000) (Real.log (837125605071 / 1000000000000)) := by
  have h := reflection_log_13610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13611_neg : (855829109 / 1000000000) ≤ -Real.log (250000000000 / 588331184411) ∧
    -Real.log (250000000000 / 588331184411) ≤ (855829111 / 1000000000) := by
  have h := checkLog_sound (w := (88331184411 / 1088331184411)) (n := 12)
    (lo := (162681929 / 1000000000)) (hi := (16268193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588331184411 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(588331184411 / 500000000000) = 1/(250000000000 / 588331184411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13611 : Bounds (855829109 / 1000000000) (855829111 / 1000000000) (Real.log (588331184411 / 250000000000)) := by
  have h := reflection_log_13611_neg
  have he : Real.log (588331184411 / 250000000000) = -Real.log (250000000000 / 588331184411) := by
    rw [show ((588331184411 / 250000000000) : ℝ) = ((250000000000 / 588331184411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13612_neg : (107794407 / 125000000) ≤ -Real.log (10000000000 / 23687331037) ∧
    -Real.log (10000000000 / 23687331037) ≤ (431177629 / 500000000) := by
  have h := checkLog_sound (w := (3687331037 / 43687331037)) (n := 12)
    (lo := (42302019 / 250000000)) (hi := (169208077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23687331037 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23687331037 / 20000000000) = 1/(10000000000 / 23687331037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13612 : Bounds (107794407 / 125000000) (431177629 / 500000000) (Real.log (23687331037 / 10000000000)) := by
  have h := reflection_log_13612_neg
  have he : Real.log (23687331037 / 10000000000) = -Real.log (10000000000 / 23687331037) := by
    rw [show ((23687331037 / 10000000000) : ℝ) = ((10000000000 / 23687331037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13613_neg : (183621123 / 100000000) ≤ -Real.log (500000000000 / 3136363636363) ∧
    -Real.log (500000000000 / 3136363636363) ≤ (1836211233 / 1000000000) := by
  have h := checkLog_sound (w := (1136363636363 / 5136363636363)) (n := 12)
    (lo := (44991687 / 100000000)) (hi := (449916871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3136363636363 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3136363636363 / 2000000000000) = 1/(500000000000 / 3136363636363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13613 : Bounds (183621123 / 100000000) (1836211233 / 1000000000) (Real.log (3136363636363 / 500000000000)) := by
  have h := reflection_log_13613_neg
  have he : Real.log (3136363636363 / 500000000000) = -Real.log (500000000000 / 3136363636363) := by
    rw [show ((3136363636363 / 500000000000) : ℝ) = ((500000000000 / 3136363636363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13614_neg : (1848917881 / 1000000000) ≤ -Real.log (125000000000 / 794117647059) ∧
    -Real.log (125000000000 / 794117647059) ≤ (462229471 / 250000000) := by
  have h := checkLog_sound (w := (294117647059 / 1294117647059)) (n := 12)
    (lo := (462623521 / 1000000000)) (hi := (231311761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794117647059 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(794117647059 / 500000000000) = 1/(125000000000 / 794117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13614 : Bounds (1848917881 / 1000000000) (462229471 / 250000000) (Real.log (794117647059 / 125000000000)) := by
  have h := reflection_log_13614_neg
  have he : Real.log (794117647059 / 125000000000) = -Real.log (125000000000 / 794117647059) := by
    rw [show ((794117647059 / 125000000000) : ℝ) = ((125000000000 / 794117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13615_neg : (137174819 / 250000000) ≤ -Real.log (1000 / 1731) ∧
    -Real.log (1000 / 1731) ≤ (548699277 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 2731)) (n := 12)
    (lo := (137174819 / 250000000)) (hi := (548699277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1000) = 1/(1000 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13615 : Bounds (137174819 / 250000000) (548699277 / 1000000000) (Real.log (1731 / 1000)) := by
  have h := reflection_log_13615_neg
  have he : Real.log (1731 / 1000) = -Real.log (1000 / 1731) := by
    rw [show ((1731 / 1000) : ℝ) = ((1000 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13616_neg : (656521949 / 500000000) ≤ -Real.log (269 / 1000) ∧
    -Real.log (269 / 1000) ≤ (13130439 / 10000000) := by
  have h := checkLog_sound (w := (231 / 769)) (n := 12)
    (lo := (309948359 / 500000000)) (hi := (619896719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 269) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 269) = 1/(269 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13616 : Bounds (-13130439 / 10000000) (-656521949 / 500000000) (Real.log (269 / 1000)) := by
  have h := reflection_log_13616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13617_neg : (182683 / 250000000) ≤ -Real.log (1000000 / 1000731) ∧
    -Real.log (1000000 / 1000731) ≤ (730733 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 2000731)) (n := 12)
    (lo := (182683 / 250000000)) (hi := (730733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000731 / 1000000) = 1/(1000000 / 1000731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13617 : Bounds (182683 / 250000000) (730733 / 1000000000) (Real.log (1000731 / 1000000)) := by
  have h := reflection_log_13617_neg
  have he : Real.log (1000731 / 1000000) = -Real.log (1000000 / 1000731) := by
    rw [show ((1000731 / 1000000) : ℝ) = ((1000000 / 1000731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13618_neg : (731267 / 1000000000) ≤ -Real.log (999269 / 1000000) ∧
    -Real.log (999269 / 1000000) ≤ (182817 / 250000000) := by
  have h := checkLog_sound (w := (731 / 1999269)) (n := 12)
    (lo := (731267 / 1000000000)) (hi := (182817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999269) = 1/(999269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13618 : Bounds (-182817 / 250000000) (-731267 / 1000000000) (Real.log (999269 / 1000000)) := by
  have h := reflection_log_13618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13619_neg : (340516903 / 1000000000) ≤ -Real.log (500000 / 702837) ∧
    -Real.log (500000 / 702837) ≤ (42564613 / 125000000) := by
  have h := checkLog_sound (w := (202837 / 1202837)) (n := 12)
    (lo := (340516903 / 1000000000)) (hi := (42564613 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702837 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702837 / 500000) = 1/(500000 / 702837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13619 : Bounds (340516903 / 1000000000) (42564613 / 125000000) (Real.log (702837 / 500000)) := by
  have h := reflection_log_13619_neg
  have he : Real.log (702837 / 500000) = -Real.log (500000 / 702837) := by
    rw [show ((702837 / 500000) : ℝ) = ((500000 / 702837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13620_neg : (65040911 / 125000000) ≤ -Real.log (297163 / 500000) ∧
    -Real.log (297163 / 500000) ≤ (520327289 / 1000000000) := by
  have h := checkLog_sound (w := (202837 / 797163)) (n := 12)
    (lo := (65040911 / 125000000)) (hi := (520327289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297163) = 1/(297163 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13620 : Bounds (-520327289 / 1000000000) (-65040911 / 125000000) (Real.log (297163 / 500000)) := by
  have h := reflection_log_13620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13621_neg : (171231059 / 500000000) ≤ -Real.log (1000000 / 1408411) ∧
    -Real.log (1000000 / 1408411) ≤ (342462119 / 1000000000) := by
  have h := checkLog_sound (w := (408411 / 2408411)) (n := 12)
    (lo := (171231059 / 500000000)) (hi := (342462119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1408411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1408411 / 1000000) = 1/(1000000 / 1408411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13621 : Bounds (171231059 / 500000000) (342462119 / 1000000000) (Real.log (1408411 / 1000000)) := by
  have h := reflection_log_13621_neg
  have he : Real.log (1408411 / 1000000) = -Real.log (1000000 / 1408411) := by
    rw [show ((1408411 / 1000000) : ℝ) = ((1000000 / 1408411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13622_neg : (524943141 / 1000000000) ≤ -Real.log (591589 / 1000000) ∧
    -Real.log (591589 / 1000000) ≤ (262471571 / 500000000) := by
  have h := checkLog_sound (w := (408411 / 1591589)) (n := 12)
    (lo := (524943141 / 1000000000)) (hi := (262471571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 591589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 591589) = 1/(591589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13622 : Bounds (-262471571 / 500000000) (-524943141 / 1000000000) (Real.log (591589 / 1000000)) := by
  have h := reflection_log_13622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13623_neg : (182481023 / 1000000000) ≤ -Real.log (833200455079 / 1000000000000) ∧
    -Real.log (833200455079 / 1000000000000) ≤ (1425633 / 7812500) := by
  have h := checkLog_sound (w := (166799544921 / 1833200455079)) (n := 12)
    (lo := (182481023 / 1000000000)) (hi := (1425633 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 833200455079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 833200455079) = 1/(833200455079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13623 : Bounds (-1425633 / 7812500) (-182481023 / 1000000000) (Real.log (833200455079 / 1000000000000)) := by
  have h := reflection_log_13623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13624_neg : (35962077 / 200000000) ≤ -Real.log (208857151431 / 250000000000) ∧
    -Real.log (208857151431 / 250000000000) ≤ (89905193 / 500000000) := by
  have h := checkLog_sound (w := (41142848569 / 458857151431)) (n := 12)
    (lo := (35962077 / 200000000)) (hi := (89905193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 208857151431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 208857151431) = 1/(208857151431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13624 : Bounds (-89905193 / 500000000) (-35962077 / 200000000) (Real.log (208857151431 / 250000000000)) := by
  have h := reflection_log_13624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13625_neg : (860844191 / 1000000000) ≤ -Real.log (500000000000 / 1182578248301) ∧
    -Real.log (500000000000 / 1182578248301) ≤ (860844193 / 1000000000) := by
  have h := checkLog_sound (w := (182578248301 / 2182578248301)) (n := 12)
    (lo := (167697011 / 1000000000)) (hi := (41924253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182578248301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1182578248301 / 1000000000000) = 1/(500000000000 / 1182578248301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13625 : Bounds (860844191 / 1000000000) (860844193 / 1000000000) (Real.log (1182578248301 / 500000000000)) := by
  have h := reflection_log_13625_neg
  have he : Real.log (1182578248301 / 500000000000) = -Real.log (500000000000 / 1182578248301) := by
    rw [show ((1182578248301 / 500000000000) : ℝ) = ((500000000000 / 1182578248301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13626_neg : (867405259 / 1000000000) ≤ -Real.log (25000000000 / 59518136747) ∧
    -Real.log (25000000000 / 59518136747) ≤ (867405261 / 1000000000) := by
  have h := checkLog_sound (w := (9518136747 / 109518136747)) (n := 12)
    (lo := (174258079 / 1000000000)) (hi := (1089113 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59518136747 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(59518136747 / 50000000000) = 1/(25000000000 / 59518136747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13626 : Bounds (867405259 / 1000000000) (867405261 / 1000000000) (Real.log (59518136747 / 25000000000)) := by
  have h := reflection_log_13626_neg
  have he : Real.log (59518136747 / 25000000000) = -Real.log (25000000000 / 59518136747) := by
    rw [show ((59518136747 / 25000000000) : ℝ) = ((25000000000 / 59518136747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13627_neg : (1848917881 / 1000000000) ≤ -Real.log (100000000000 / 635294117647) ∧
    -Real.log (100000000000 / 635294117647) ≤ (462229471 / 250000000) := by
  have h := checkLog_sound (w := (235294117647 / 1035294117647)) (n := 12)
    (lo := (462623521 / 1000000000)) (hi := (231311761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635294117647 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(635294117647 / 400000000000) = 1/(100000000000 / 635294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13627 : Bounds (1848917881 / 1000000000) (462229471 / 250000000) (Real.log (635294117647 / 100000000000)) := by
  have h := reflection_log_13627_neg
  have he : Real.log (635294117647 / 100000000000) = -Real.log (100000000000 / 635294117647) := by
    rw [show ((635294117647 / 100000000000) : ℝ) = ((100000000000 / 635294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13628_neg : (930871587 / 500000000) ≤ -Real.log (6250000000 / 40218401487) ∧
    -Real.log (6250000000 / 40218401487) ≤ (1861743177 / 1000000000) := by
  have h := checkLog_sound (w := (15218401487 / 65218401487)) (n := 12)
    (lo := (237724407 / 500000000)) (hi := (95089763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40218401487 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40218401487 / 25000000000) = 1/(6250000000 / 40218401487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13628 : Bounds (930871587 / 500000000) (1861743177 / 1000000000) (Real.log (40218401487 / 6250000000)) := by
  have h := reflection_log_13628_neg
  have he : Real.log (40218401487 / 6250000000) = -Real.log (6250000000 / 40218401487) := by
    rw [show ((40218401487 / 6250000000) : ℝ) = ((6250000000 / 40218401487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13629_neg : (275215439 / 500000000) ≤ -Real.log (500 / 867) ∧
    -Real.log (500 / 867) ≤ (550430879 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1367)) (n := 12)
    (lo := (275215439 / 500000000)) (hi := (550430879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867 / 500) = 1/(500 / 867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13629 : Bounds (275215439 / 500000000) (550430879 / 1000000000) (Real.log (867 / 500)) := by
  have h := reflection_log_13629_neg
  have he : Real.log (867 / 500) = -Real.log (500 / 867) := by
    rw [show ((867 / 500) : ℝ) = ((500 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13630_neg : (1324258969 / 1000000000) ≤ -Real.log (133 / 500) ∧
    -Real.log (133 / 500) ≤ (1324258971 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 383)) (n := 12)
    (lo := (631111789 / 1000000000)) (hi := (63111179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 133) = 1/(133 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13630 : Bounds (-1324258971 / 1000000000) (-1324258969 / 1000000000) (Real.log (133 / 500)) := by
  have h := reflection_log_13630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13631_neg : (73373 / 100000000) ≤ -Real.log (500000 / 500367) ∧
    -Real.log (500000 / 500367) ≤ (733731 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1000367)) (n := 12)
    (lo := (73373 / 100000000)) (hi := (733731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500367 / 500000) = 1/(500000 / 500367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13631 : Bounds (73373 / 100000000) (733731 / 1000000000) (Real.log (500367 / 500000)) := by
  have h := reflection_log_13631_neg
  have he : Real.log (500367 / 500000) = -Real.log (500000 / 500367) := by
    rw [show ((500367 / 500000) : ℝ) = ((500000 / 500367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
