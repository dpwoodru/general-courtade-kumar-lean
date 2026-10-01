import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4416_neg : (2103627 / 250000000) ≤ -Real.log (247905198639 / 250000000000) ∧
    -Real.log (247905198639 / 250000000000) ≤ (8414509 / 1000000000) := by
  have h := checkLog_sound (w := (2094801361 / 497905198639)) (n := 12)
    (lo := (2103627 / 250000000)) (hi := (8414509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247905198639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247905198639) = 1/(247905198639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4416 : Bounds (-8414509 / 1000000000) (-2103627 / 250000000) (Real.log (247905198639 / 250000000000)) := by
  have h := reflection_log_4416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4417_neg : (4185773 / 500000000) ≤ -Real.log (39666535879 / 40000000000) ∧
    -Real.log (39666535879 / 40000000000) ≤ (8371547 / 1000000000) := by
  have h := checkLog_sound (w := (333464121 / 79666535879)) (n := 12)
    (lo := (4185773 / 500000000)) (hi := (8371547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39666535879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39666535879) = 1/(39666535879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4417 : Bounds (-8371547 / 1000000000) (-4185773 / 500000000) (Real.log (39666535879 / 40000000000)) := by
  have h := reflection_log_4417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4418_neg : (91560001 / 500000000) ≤ -Real.log (500000000000 / 600479258717) ∧
    -Real.log (500000000000 / 600479258717) ≤ (183120003 / 1000000000) := by
  have h := checkLog_sound (w := (100479258717 / 1100479258717)) (n := 12)
    (lo := (91560001 / 500000000)) (hi := (183120003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600479258717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600479258717 / 500000000000) = 1/(500000000000 / 600479258717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4418 : Bounds (91560001 / 500000000) (183120003 / 1000000000) (Real.log (600479258717 / 500000000000)) := by
  have h := reflection_log_4418_neg
  have he : Real.log (600479258717 / 500000000000) = -Real.log (500000000000 / 600479258717) := by
    rw [show ((600479258717 / 500000000000) : ℝ) = ((500000000000 / 600479258717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4419_neg : (18358993 / 100000000) ≤ -Real.log (500000000000 / 600761506811) ∧
    -Real.log (500000000000 / 600761506811) ≤ (183589931 / 1000000000) := by
  have h := checkLog_sound (w := (100761506811 / 1100761506811)) (n := 12)
    (lo := (18358993 / 100000000)) (hi := (183589931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600761506811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600761506811 / 500000000000) = 1/(500000000000 / 600761506811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4419 : Bounds (18358993 / 100000000) (183589931 / 1000000000) (Real.log (600761506811 / 500000000000)) := by
  have h := reflection_log_4419_neg
  have he : Real.log (600761506811 / 500000000000) = -Real.log (500000000000 / 600761506811) := by
    rw [show ((600761506811 / 500000000000) : ℝ) = ((500000000000 / 600761506811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4420_neg : (367480341 / 1000000000) ≤ -Real.log (500000000000 / 722045704509) ∧
    -Real.log (500000000000 / 722045704509) ≤ (183740171 / 500000000) := by
  have h := checkLog_sound (w := (222045704509 / 1222045704509)) (n := 12)
    (lo := (367480341 / 1000000000)) (hi := (183740171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722045704509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722045704509 / 500000000000) = 1/(500000000000 / 722045704509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4420 : Bounds (367480341 / 1000000000) (183740171 / 500000000) (Real.log (722045704509 / 500000000000)) := by
  have h := reflection_log_4420_neg
  have he : Real.log (722045704509 / 500000000000) = -Real.log (500000000000 / 722045704509) := by
    rw [show ((722045704509 / 500000000000) : ℝ) = ((500000000000 / 722045704509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4421_neg : (367687173 / 1000000000) ≤ -Real.log (125000000000 / 180548765583) ∧
    -Real.log (125000000000 / 180548765583) ≤ (183843587 / 500000000) := by
  have h := checkLog_sound (w := (55548765583 / 305548765583)) (n := 12)
    (lo := (367687173 / 1000000000)) (hi := (183843587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180548765583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180548765583 / 125000000000) = 1/(125000000000 / 180548765583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4421 : Bounds (367687173 / 1000000000) (183843587 / 500000000) (Real.log (180548765583 / 125000000000)) := by
  have h := reflection_log_4421_neg
  have he : Real.log (180548765583 / 125000000000) = -Real.log (125000000000 / 180548765583) := by
    rw [show ((180548765583 / 125000000000) : ℝ) = ((125000000000 / 180548765583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4422_neg : (167123313 / 1000000000) ≤ -Real.log (10000 / 11819) ∧
    -Real.log (10000 / 11819) ≤ (83561657 / 500000000) := by
  have h := checkLog_sound (w := (1819 / 21819)) (n := 12)
    (lo := (167123313 / 1000000000)) (hi := (83561657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11819 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11819 / 10000) = 1/(10000 / 11819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4422 : Bounds (167123313 / 1000000000) (83561657 / 500000000) (Real.log (11819 / 10000)) := by
  have h := reflection_log_4422_neg
  have he : Real.log (11819 / 10000) = -Real.log (10000 / 11819) := by
    rw [show ((11819 / 10000) : ℝ) = ((10000 / 11819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4423_neg : (2007707 / 10000000) ≤ -Real.log (8181 / 10000) ∧
    -Real.log (8181 / 10000) ≤ (200770701 / 1000000000) := by
  have h := checkLog_sound (w := (1819 / 18181)) (n := 12)
    (lo := (2007707 / 10000000)) (hi := (200770701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8181) = 1/(8181 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4423 : Bounds (-200770701 / 1000000000) (-2007707 / 10000000) (Real.log (8181 / 10000)) := by
  have h := reflection_log_4423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4424_neg : (181883 / 1000000000) ≤ -Real.log (10000000 / 10001819) ∧
    -Real.log (10000000 / 10001819) ≤ (45471 / 250000000) := by
  have h := checkLog_sound (w := (1819 / 20001819)) (n := 12)
    (lo := (181883 / 1000000000)) (hi := (45471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001819 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001819 / 10000000) = 1/(10000000 / 10001819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4424 : Bounds (181883 / 1000000000) (45471 / 250000000) (Real.log (10001819 / 10000000)) := by
  have h := reflection_log_4424_neg
  have he : Real.log (10001819 / 10000000) = -Real.log (10000000 / 10001819) := by
    rw [show ((10001819 / 10000000) : ℝ) = ((10000000 / 10001819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4425_neg : (45479 / 250000000) ≤ -Real.log (9998181 / 10000000) ∧
    -Real.log (9998181 / 10000000) ≤ (181917 / 1000000000) := by
  have h := checkLog_sound (w := (1819 / 19998181)) (n := 12)
    (lo := (45479 / 250000000)) (hi := (181917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998181) = 1/(9998181 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4425 : Bounds (-181917 / 1000000000) (-45479 / 250000000) (Real.log (9998181 / 10000000)) := by
  have h := reflection_log_4425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4426_neg : (87420959 / 1000000000) ≤ -Real.log (250000 / 272839) ∧
    -Real.log (250000 / 272839) ≤ (546381 / 6250000) := by
  have h := checkLog_sound (w := (22839 / 522839)) (n := 12)
    (lo := (87420959 / 1000000000)) (hi := (546381 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272839 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272839 / 250000) = 1/(250000 / 272839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4426 : Bounds (87420959 / 1000000000) (546381 / 6250000) (Real.log (272839 / 250000)) := by
  have h := reflection_log_4426_neg
  have he : Real.log (272839 / 250000) = -Real.log (250000 / 272839) := by
    rw [show ((272839 / 250000) : ℝ) = ((250000 / 272839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4427_neg : (958019 / 10000000) ≤ -Real.log (227161 / 250000) ∧
    -Real.log (227161 / 250000) ≤ (95801901 / 1000000000) := by
  have h := checkLog_sound (w := (22839 / 477161)) (n := 12)
    (lo := (958019 / 10000000)) (hi := (95801901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227161) = 1/(227161 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4427 : Bounds (-95801901 / 1000000000) (-958019 / 10000000) (Real.log (227161 / 250000)) := by
  have h := reflection_log_4427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4428_neg : (171161 / 1953125) ≤ -Real.log (1000000 / 1091589) ∧
    -Real.log (1000000 / 1091589) ≤ (87634433 / 1000000000) := by
  have h := checkLog_sound (w := (91589 / 2091589)) (n := 12)
    (lo := (171161 / 1953125)) (hi := (87634433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091589 / 1000000) = 1/(1000000 / 1091589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4428 : Bounds (171161 / 1953125) (87634433 / 1000000000) (Real.log (1091589 / 1000000)) := by
  have h := reflection_log_4428_neg
  have he : Real.log (1091589 / 1000000) = -Real.log (1000000 / 1091589) := by
    rw [show ((1091589 / 1000000) : ℝ) = ((1000000 / 1091589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4429_neg : (96058359 / 1000000000) ≤ -Real.log (908411 / 1000000) ∧
    -Real.log (908411 / 1000000) ≤ (2401459 / 25000000) := by
  have h := checkLog_sound (w := (91589 / 1908411)) (n := 12)
    (lo := (96058359 / 1000000000)) (hi := (2401459 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908411) = 1/(908411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4429 : Bounds (-2401459 / 25000000) (-96058359 / 1000000000) (Real.log (908411 / 1000000)) := by
  have h := reflection_log_4429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4430_neg : (4211963 / 500000000) ≤ -Real.log (991611455079 / 1000000000000) ∧
    -Real.log (991611455079 / 1000000000000) ≤ (8423927 / 1000000000) := by
  have h := checkLog_sound (w := (8388544921 / 1991611455079)) (n := 12)
    (lo := (4211963 / 500000000)) (hi := (8423927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991611455079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991611455079) = 1/(991611455079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4430 : Bounds (-8423927 / 1000000000) (-4211963 / 500000000) (Real.log (991611455079 / 1000000000000)) := by
  have h := reflection_log_4430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4431_neg : (419047 / 50000000) ≤ -Real.log (61978380079 / 62500000000) ∧
    -Real.log (61978380079 / 62500000000) ≤ (8380941 / 1000000000) := by
  have h := checkLog_sound (w := (521619921 / 124478380079)) (n := 12)
    (lo := (419047 / 50000000)) (hi := (8380941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61978380079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61978380079) = 1/(61978380079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4431 : Bounds (-8380941 / 1000000000) (-419047 / 50000000) (Real.log (61978380079 / 62500000000)) := by
  have h := reflection_log_4431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4432_neg : (9161143 / 50000000) ≤ -Real.log (31250000000 / 37533814123) ∧
    -Real.log (31250000000 / 37533814123) ≤ (183222861 / 1000000000) := by
  have h := checkLog_sound (w := (6283814123 / 68783814123)) (n := 12)
    (lo := (9161143 / 50000000)) (hi := (183222861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37533814123 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37533814123 / 31250000000) = 1/(31250000000 / 37533814123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4432 : Bounds (9161143 / 50000000) (183222861 / 1000000000) (Real.log (37533814123 / 31250000000)) := by
  have h := reflection_log_4432_neg
  have he : Real.log (37533814123 / 31250000000) = -Real.log (31250000000 / 37533814123) := by
    rw [show ((37533814123 / 31250000000) : ℝ) = ((31250000000 / 37533814123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4433_neg : (22961599 / 125000000) ≤ -Real.log (500000000000 / 600823305751) ∧
    -Real.log (500000000000 / 600823305751) ≤ (183692793 / 1000000000) := by
  have h := checkLog_sound (w := (100823305751 / 1100823305751)) (n := 12)
    (lo := (22961599 / 125000000)) (hi := (183692793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600823305751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600823305751 / 500000000000) = 1/(500000000000 / 600823305751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4433 : Bounds (22961599 / 125000000) (183692793 / 1000000000) (Real.log (600823305751 / 500000000000)) := by
  have h := reflection_log_4433_neg
  have he : Real.log (600823305751 / 500000000000) = -Real.log (500000000000 / 600823305751) := by
    rw [show ((600823305751 / 500000000000) : ℝ) = ((500000000000 / 600823305751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4434_neg : (367687173 / 1000000000) ≤ -Real.log (500000000000 / 722195062331) ∧
    -Real.log (500000000000 / 722195062331) ≤ (183843587 / 500000000) := by
  have h := checkLog_sound (w := (222195062331 / 1222195062331)) (n := 12)
    (lo := (367687173 / 1000000000)) (hi := (183843587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722195062331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722195062331 / 500000000000) = 1/(500000000000 / 722195062331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4434 : Bounds (367687173 / 1000000000) (183843587 / 500000000) (Real.log (722195062331 / 500000000000)) := by
  have h := reflection_log_4434_neg
  have he : Real.log (722195062331 / 500000000000) = -Real.log (500000000000 / 722195062331) := by
    rw [show ((722195062331 / 500000000000) : ℝ) = ((500000000000 / 722195062331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4435_neg : (367894013 / 1000000000) ≤ -Real.log (125000000000 / 180586114167) ∧
    -Real.log (125000000000 / 180586114167) ≤ (183947007 / 500000000) := by
  have h := checkLog_sound (w := (55586114167 / 305586114167)) (n := 12)
    (lo := (367894013 / 1000000000)) (hi := (183947007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180586114167 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180586114167 / 125000000000) = 1/(125000000000 / 180586114167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4435 : Bounds (367894013 / 1000000000) (183947007 / 500000000) (Real.log (180586114167 / 125000000000)) := by
  have h := reflection_log_4435_neg
  have he : Real.log (180586114167 / 125000000000) = -Real.log (125000000000 / 180586114167) := by
    rw [show ((180586114167 / 125000000000) : ℝ) = ((125000000000 / 180586114167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4436_neg : (83603959 / 500000000) ≤ -Real.log (500 / 591) ∧
    -Real.log (500 / 591) ≤ (167207919 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 1091)) (n := 12)
    (lo := (83603959 / 500000000)) (hi := (167207919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591 / 500) = 1/(500 / 591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4436 : Bounds (83603959 / 500000000) (167207919 / 1000000000) (Real.log (591 / 500)) := by
  have h := reflection_log_4436_neg
  have he : Real.log (591 / 500) = -Real.log (500 / 591) := by
    rw [show ((591 / 500) : ℝ) = ((500 / 591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4437_neg : (100446471 / 500000000) ≤ -Real.log (409 / 500) ∧
    -Real.log (409 / 500) ≤ (200892943 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 909)) (n := 12)
    (lo := (100446471 / 500000000)) (hi := (200892943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 409) = 1/(409 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4437 : Bounds (-200892943 / 1000000000) (-100446471 / 500000000) (Real.log (409 / 500)) := by
  have h := reflection_log_4437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4438_neg : (181983 / 1000000000) ≤ -Real.log (500000 / 500091) ∧
    -Real.log (500000 / 500091) ≤ (5687 / 31250000) := by
  have h := checkLog_sound (w := (91 / 1000091)) (n := 12)
    (lo := (181983 / 1000000000)) (hi := (5687 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500091 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500091 / 500000) = 1/(500000 / 500091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4438 : Bounds (181983 / 1000000000) (5687 / 31250000) (Real.log (500091 / 500000)) := by
  have h := reflection_log_4438_neg
  have he : Real.log (500091 / 500000) = -Real.log (500000 / 500091) := by
    rw [show ((500091 / 500000) : ℝ) = ((500000 / 500091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4439_neg : (711 / 3906250) ≤ -Real.log (499909 / 500000) ∧
    -Real.log (499909 / 500000) ≤ (182017 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 999909)) (n := 12)
    (lo := (711 / 3906250)) (hi := (182017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499909) = 1/(499909 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4439 : Bounds (-182017 / 1000000000) (-711 / 3906250) (Real.log (499909 / 500000)) := by
  have h := reflection_log_4439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4440_neg : (87467689 / 1000000000) ≤ -Real.log (1000000 / 1091407) ∧
    -Real.log (1000000 / 1091407) ≤ (8746769 / 100000000) := by
  have h := checkLog_sound (w := (91407 / 2091407)) (n := 12)
    (lo := (87467689 / 1000000000)) (hi := (8746769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091407 / 1000000) = 1/(1000000 / 1091407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4440 : Bounds (87467689 / 1000000000) (8746769 / 100000000) (Real.log (1091407 / 1000000)) := by
  have h := reflection_log_4440_neg
  have he : Real.log (1091407 / 1000000) = -Real.log (1000000 / 1091407) := by
    rw [show ((1091407 / 1000000) : ℝ) = ((1000000 / 1091407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4441_neg : (95858029 / 1000000000) ≤ -Real.log (908593 / 1000000) ∧
    -Real.log (908593 / 1000000) ≤ (9585803 / 100000000) := by
  have h := checkLog_sound (w := (91407 / 1908593)) (n := 12)
    (lo := (95858029 / 1000000000)) (hi := (9585803 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908593) = 1/(908593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4441 : Bounds (-9585803 / 100000000) (-95858029 / 1000000000) (Real.log (908593 / 1000000)) := by
  have h := reflection_log_4441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4442_neg : (685009 / 7812500) ≤ -Real.log (25000 / 27291) ∧
    -Real.log (25000 / 27291) ≤ (87681153 / 1000000000) := by
  have h := checkLog_sound (w := (2291 / 52291)) (n := 12)
    (lo := (685009 / 7812500)) (hi := (87681153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27291 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27291 / 25000) = 1/(25000 / 27291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4442 : Bounds (685009 / 7812500) (87681153 / 1000000000) (Real.log (27291 / 25000)) := by
  have h := reflection_log_4442_neg
  have he : Real.log (27291 / 25000) = -Real.log (25000 / 27291) := by
    rw [show ((27291 / 25000) : ℝ) = ((25000 / 27291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4443_neg : (96114503 / 1000000000) ≤ -Real.log (22709 / 25000) ∧
    -Real.log (22709 / 25000) ≤ (12014313 / 125000000) := by
  have h := checkLog_sound (w := (2291 / 47709)) (n := 12)
    (lo := (96114503 / 1000000000)) (hi := (12014313 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22709) = 1/(22709 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4443 : Bounds (-12014313 / 125000000) (-96114503 / 1000000000) (Real.log (22709 / 25000)) := by
  have h := reflection_log_4443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4444_neg : (168667 / 20000000) ≤ -Real.log (619751319 / 625000000) ∧
    -Real.log (619751319 / 625000000) ≤ (8433351 / 1000000000) := by
  have h := checkLog_sound (w := (5248681 / 1244751319)) (n := 12)
    (lo := (168667 / 20000000)) (hi := (8433351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 619751319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 619751319) = 1/(619751319 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4444 : Bounds (-8433351 / 1000000000) (-168667 / 20000000) (Real.log (619751319 / 625000000)) := by
  have h := reflection_log_4444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4445_neg : (419517 / 50000000) ≤ -Real.log (991644760351 / 1000000000000) ∧
    -Real.log (991644760351 / 1000000000000) ≤ (8390341 / 1000000000) := by
  have h := checkLog_sound (w := (8355239649 / 1991644760351)) (n := 12)
    (lo := (419517 / 50000000)) (hi := (8390341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991644760351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991644760351) = 1/(991644760351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4445 : Bounds (-8390341 / 1000000000) (-419517 / 50000000) (Real.log (991644760351 / 1000000000000)) := by
  have h := reflection_log_4445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4446_neg : (183325719 / 1000000000) ≤ -Real.log (500000000000 / 600602800153) ∧
    -Real.log (500000000000 / 600602800153) ≤ (4583143 / 25000000) := by
  have h := checkLog_sound (w := (100602800153 / 1100602800153)) (n := 12)
    (lo := (183325719 / 1000000000)) (hi := (4583143 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600602800153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600602800153 / 500000000000) = 1/(500000000000 / 600602800153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4446 : Bounds (183325719 / 1000000000) (4583143 / 25000000) (Real.log (600602800153 / 500000000000)) := by
  have h := reflection_log_4446_neg
  have he : Real.log (600602800153 / 500000000000) = -Real.log (500000000000 / 600602800153) := by
    rw [show ((600602800153 / 500000000000) : ℝ) = ((500000000000 / 600602800153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4447_neg : (36759131 / 200000000) ≤ -Real.log (50000000000 / 60088511163) ∧
    -Real.log (50000000000 / 60088511163) ≤ (22974457 / 125000000) := by
  have h := checkLog_sound (w := (10088511163 / 110088511163)) (n := 12)
    (lo := (36759131 / 200000000)) (hi := (22974457 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60088511163 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60088511163 / 50000000000) = 1/(50000000000 / 60088511163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4447 : Bounds (36759131 / 200000000) (22974457 / 125000000) (Real.log (60088511163 / 50000000000)) := by
  have h := reflection_log_4447_neg
  have he : Real.log (60088511163 / 50000000000) = -Real.log (50000000000 / 60088511163) := by
    rw [show ((60088511163 / 50000000000) : ℝ) = ((50000000000 / 60088511163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4448_neg : (367894013 / 1000000000) ≤ -Real.log (500000000000 / 722344456667) ∧
    -Real.log (500000000000 / 722344456667) ≤ (183947007 / 500000000) := by
  have h := checkLog_sound (w := (222344456667 / 1222344456667)) (n := 12)
    (lo := (367894013 / 1000000000)) (hi := (183947007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722344456667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722344456667 / 500000000000) = 1/(500000000000 / 722344456667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4448 : Bounds (367894013 / 1000000000) (183947007 / 500000000) (Real.log (722344456667 / 500000000000)) := by
  have h := reflection_log_4448_neg
  have he : Real.log (722344456667 / 500000000000) = -Real.log (500000000000 / 722344456667) := by
    rw [show ((722344456667 / 500000000000) : ℝ) = ((500000000000 / 722344456667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4449_neg : (368100861 / 1000000000) ≤ -Real.log (500000000000 / 722493887531) ∧
    -Real.log (500000000000 / 722493887531) ≤ (184050431 / 500000000) := by
  have h := checkLog_sound (w := (222493887531 / 1222493887531)) (n := 12)
    (lo := (368100861 / 1000000000)) (hi := (184050431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722493887531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722493887531 / 500000000000) = 1/(500000000000 / 722493887531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4449 : Bounds (368100861 / 1000000000) (184050431 / 500000000) (Real.log (722493887531 / 500000000000)) := by
  have h := reflection_log_4449_neg
  have he : Real.log (722493887531 / 500000000000) = -Real.log (500000000000 / 722493887531) := by
    rw [show ((722493887531 / 500000000000) : ℝ) = ((500000000000 / 722493887531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4450_neg : (167292517 / 1000000000) ≤ -Real.log (10000 / 11821) ∧
    -Real.log (10000 / 11821) ≤ (83646259 / 500000000) := by
  have h := checkLog_sound (w := (1821 / 21821)) (n := 12)
    (lo := (167292517 / 1000000000)) (hi := (83646259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11821 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11821 / 10000) = 1/(10000 / 11821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4450 : Bounds (167292517 / 1000000000) (83646259 / 500000000) (Real.log (11821 / 10000)) := by
  have h := reflection_log_4450_neg
  have he : Real.log (11821 / 10000) = -Real.log (10000 / 11821) := by
    rw [show ((11821 / 10000) : ℝ) = ((10000 / 11821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4451_neg : (201015199 / 1000000000) ≤ -Real.log (8179 / 10000) ∧
    -Real.log (8179 / 10000) ≤ (251269 / 1250000) := by
  have h := checkLog_sound (w := (1821 / 18179)) (n := 12)
    (lo := (201015199 / 1000000000)) (hi := (251269 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8179) = 1/(8179 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4451 : Bounds (-251269 / 1250000) (-201015199 / 1000000000) (Real.log (8179 / 10000)) := by
  have h := reflection_log_4451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4452_neg : (182083 / 1000000000) ≤ -Real.log (10000000 / 10001821) ∧
    -Real.log (10000000 / 10001821) ≤ (45521 / 250000000) := by
  have h := checkLog_sound (w := (1821 / 20001821)) (n := 12)
    (lo := (182083 / 1000000000)) (hi := (45521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001821 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001821 / 10000000) = 1/(10000000 / 10001821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4452 : Bounds (182083 / 1000000000) (45521 / 250000000) (Real.log (10001821 / 10000000)) := by
  have h := reflection_log_4452_neg
  have he : Real.log (10001821 / 10000000) = -Real.log (10000000 / 10001821) := by
    rw [show ((10001821 / 10000000) : ℝ) = ((10000000 / 10001821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4453_neg : (45529 / 250000000) ≤ -Real.log (9998179 / 10000000) ∧
    -Real.log (9998179 / 10000000) ≤ (182117 / 1000000000) := by
  have h := checkLog_sound (w := (1821 / 19998179)) (n := 12)
    (lo := (45529 / 250000000)) (hi := (182117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998179) = 1/(9998179 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4453 : Bounds (-182117 / 1000000000) (-45529 / 250000000) (Real.log (9998179 / 10000000)) := by
  have h := reflection_log_4453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4454_neg : (87514417 / 1000000000) ≤ -Real.log (500000 / 545729) ∧
    -Real.log (500000 / 545729) ≤ (43757209 / 500000000) := by
  have h := checkLog_sound (w := (45729 / 1045729)) (n := 12)
    (lo := (87514417 / 1000000000)) (hi := (43757209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545729 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545729 / 500000) = 1/(500000 / 545729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4454 : Bounds (87514417 / 1000000000) (43757209 / 500000000) (Real.log (545729 / 500000)) := by
  have h := reflection_log_4454_neg
  have he : Real.log (545729 / 500000) = -Real.log (500000 / 545729) := by
    rw [show ((545729 / 500000) : ℝ) = ((500000 / 545729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4455_neg : (47957081 / 500000000) ≤ -Real.log (454271 / 500000) ∧
    -Real.log (454271 / 500000) ≤ (95914163 / 1000000000) := by
  have h := checkLog_sound (w := (45729 / 954271)) (n := 12)
    (lo := (47957081 / 500000000)) (hi := (95914163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454271) = 1/(454271 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4455 : Bounds (-95914163 / 1000000000) (-47957081 / 500000000) (Real.log (454271 / 500000)) := by
  have h := reflection_log_4455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4456_neg : (8772787 / 100000000) ≤ -Real.log (1000000 / 1091691) ∧
    -Real.log (1000000 / 1091691) ≤ (87727871 / 1000000000) := by
  have h := checkLog_sound (w := (91691 / 2091691)) (n := 12)
    (lo := (8772787 / 100000000)) (hi := (87727871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091691 / 1000000) = 1/(1000000 / 1091691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4456 : Bounds (8772787 / 100000000) (87727871 / 1000000000) (Real.log (1091691 / 1000000)) := by
  have h := reflection_log_4456_neg
  have he : Real.log (1091691 / 1000000) = -Real.log (1000000 / 1091691) := by
    rw [show ((1091691 / 1000000) : ℝ) = ((1000000 / 1091691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4457_neg : (96170649 / 1000000000) ≤ -Real.log (908309 / 1000000) ∧
    -Real.log (908309 / 1000000) ≤ (1923413 / 20000000) := by
  have h := checkLog_sound (w := (91691 / 1908309)) (n := 12)
    (lo := (96170649 / 1000000000)) (hi := (1923413 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908309) = 1/(908309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4457 : Bounds (-1923413 / 20000000) (-96170649 / 1000000000) (Real.log (908309 / 1000000)) := by
  have h := reflection_log_4457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4458_neg : (8442779 / 1000000000) ≤ -Real.log (991592760519 / 1000000000000) ∧
    -Real.log (991592760519 / 1000000000000) ≤ (422139 / 50000000) := by
  have h := checkLog_sound (w := (8407239481 / 1991592760519)) (n := 12)
    (lo := (8442779 / 1000000000)) (hi := (422139 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991592760519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991592760519) = 1/(991592760519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4458 : Bounds (-422139 / 50000000) (-8442779 / 1000000000) (Real.log (991592760519 / 1000000000000)) := by
  have h := reflection_log_4458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4459_neg : (1679949 / 200000000) ≤ -Real.log (247908858559 / 250000000000) ∧
    -Real.log (247908858559 / 250000000000) ≤ (4199873 / 500000000) := by
  have h := checkLog_sound (w := (2091141441 / 497908858559)) (n := 12)
    (lo := (1679949 / 200000000)) (hi := (4199873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247908858559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247908858559) = 1/(247908858559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4459 : Bounds (-4199873 / 500000000) (-1679949 / 200000000) (Real.log (247908858559 / 250000000000)) := by
  have h := reflection_log_4459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4460_neg : (183428579 / 1000000000) ≤ -Real.log (250000000000 / 300332290637) ∧
    -Real.log (250000000000 / 300332290637) ≤ (9171429 / 50000000) := by
  have h := checkLog_sound (w := (50332290637 / 550332290637)) (n := 12)
    (lo := (183428579 / 1000000000)) (hi := (9171429 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300332290637 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300332290637 / 250000000000) = 1/(250000000000 / 300332290637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4460 : Bounds (183428579 / 1000000000) (9171429 / 50000000) (Real.log (300332290637 / 250000000000)) := by
  have h := reflection_log_4460_neg
  have he : Real.log (300332290637 / 250000000000) = -Real.log (250000000000 / 300332290637) := by
    rw [show ((300332290637 / 250000000000) : ℝ) = ((250000000000 / 300332290637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4461_neg : (4597463 / 25000000) ≤ -Real.log (10000000000 / 12018938489) ∧
    -Real.log (10000000000 / 12018938489) ≤ (183898521 / 1000000000) := by
  have h := checkLog_sound (w := (2018938489 / 22018938489)) (n := 12)
    (lo := (4597463 / 25000000)) (hi := (183898521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12018938489 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12018938489 / 10000000000) = 1/(10000000000 / 12018938489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4461 : Bounds (4597463 / 25000000) (183898521 / 1000000000) (Real.log (12018938489 / 10000000000)) := by
  have h := reflection_log_4461_neg
  have he : Real.log (12018938489 / 10000000000) = -Real.log (10000000000 / 12018938489) := by
    rw [show ((12018938489 / 10000000000) : ℝ) = ((10000000000 / 12018938489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4462_neg : (368100861 / 1000000000) ≤ -Real.log (50000000000 / 72249388753) ∧
    -Real.log (50000000000 / 72249388753) ≤ (184050431 / 500000000) := by
  have h := checkLog_sound (w := (22249388753 / 122249388753)) (n := 12)
    (lo := (368100861 / 1000000000)) (hi := (184050431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72249388753 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72249388753 / 50000000000) = 1/(50000000000 / 72249388753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4462 : Bounds (368100861 / 1000000000) (184050431 / 500000000) (Real.log (72249388753 / 50000000000)) := by
  have h := reflection_log_4462_neg
  have he : Real.log (72249388753 / 50000000000) = -Real.log (50000000000 / 72249388753) := by
    rw [show ((72249388753 / 50000000000) : ℝ) = ((50000000000 / 72249388753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4463_neg : (368307717 / 1000000000) ≤ -Real.log (250000000000 / 361321677467) ∧
    -Real.log (250000000000 / 361321677467) ≤ (184153859 / 500000000) := by
  have h := checkLog_sound (w := (111321677467 / 611321677467)) (n := 12)
    (lo := (368307717 / 1000000000)) (hi := (184153859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361321677467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361321677467 / 250000000000) = 1/(250000000000 / 361321677467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4463 : Bounds (368307717 / 1000000000) (184153859 / 500000000) (Real.log (361321677467 / 250000000000)) := by
  have h := reflection_log_4463_neg
  have he : Real.log (361321677467 / 250000000000) = -Real.log (250000000000 / 361321677467) := by
    rw [show ((361321677467 / 250000000000) : ℝ) = ((250000000000 / 361321677467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4464_neg : (167377109 / 1000000000) ≤ -Real.log (5000 / 5911) ∧
    -Real.log (5000 / 5911) ≤ (16737711 / 100000000) := by
  have h := checkLog_sound (w := (911 / 10911)) (n := 12)
    (lo := (167377109 / 1000000000)) (hi := (16737711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5911 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5911 / 5000) = 1/(5000 / 5911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4464 : Bounds (167377109 / 1000000000) (16737711 / 100000000) (Real.log (5911 / 5000)) := by
  have h := reflection_log_4464_neg
  have he : Real.log (5911 / 5000) = -Real.log (5000 / 5911) := by
    rw [show ((5911 / 5000) : ℝ) = ((5000 / 5911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4465_neg : (201137471 / 1000000000) ≤ -Real.log (4089 / 5000) ∧
    -Real.log (4089 / 5000) ≤ (3142773 / 15625000) := by
  have h := checkLog_sound (w := (911 / 9089)) (n := 12)
    (lo := (201137471 / 1000000000)) (hi := (3142773 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4089) = 1/(4089 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4465 : Bounds (-3142773 / 15625000) (-201137471 / 1000000000) (Real.log (4089 / 5000)) := by
  have h := reflection_log_4465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4466_neg : (182183 / 1000000000) ≤ -Real.log (5000000 / 5000911) ∧
    -Real.log (5000000 / 5000911) ≤ (22773 / 125000000) := by
  have h := checkLog_sound (w := (911 / 10000911)) (n := 12)
    (lo := (182183 / 1000000000)) (hi := (22773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000911 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000911 / 5000000) = 1/(5000000 / 5000911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4466 : Bounds (182183 / 1000000000) (22773 / 125000000) (Real.log (5000911 / 5000000)) := by
  have h := reflection_log_4466_neg
  have he : Real.log (5000911 / 5000000) = -Real.log (5000000 / 5000911) := by
    rw [show ((5000911 / 5000000) : ℝ) = ((5000000 / 5000911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4467_neg : (22777 / 125000000) ≤ -Real.log (4999089 / 5000000) ∧
    -Real.log (4999089 / 5000000) ≤ (182217 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 9999089)) (n := 12)
    (lo := (22777 / 125000000)) (hi := (182217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999089) = 1/(4999089 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4467 : Bounds (-182217 / 1000000000) (-22777 / 125000000) (Real.log (4999089 / 5000000)) := by
  have h := reflection_log_4467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4468_neg : (43780571 / 500000000) ≤ -Real.log (1000000 / 1091509) ∧
    -Real.log (1000000 / 1091509) ≤ (87561143 / 1000000000) := by
  have h := checkLog_sound (w := (91509 / 2091509)) (n := 12)
    (lo := (43780571 / 500000000)) (hi := (87561143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091509 / 1000000) = 1/(1000000 / 1091509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4468 : Bounds (43780571 / 500000000) (87561143 / 1000000000) (Real.log (1091509 / 1000000)) := by
  have h := reflection_log_4468_neg
  have he : Real.log (1091509 / 1000000) = -Real.log (1000000 / 1091509) := by
    rw [show ((1091509 / 1000000) : ℝ) = ((1000000 / 1091509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4469_neg : (95970297 / 1000000000) ≤ -Real.log (908491 / 1000000) ∧
    -Real.log (908491 / 1000000) ≤ (47985149 / 500000000) := by
  have h := checkLog_sound (w := (91509 / 1908491)) (n := 12)
    (lo := (95970297 / 1000000000)) (hi := (47985149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908491) = 1/(908491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4469 : Bounds (-47985149 / 500000000) (-95970297 / 1000000000) (Real.log (908491 / 1000000)) := by
  have h := reflection_log_4469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4470_neg : (17554917 / 200000000) ≤ -Real.log (500000 / 545871) ∧
    -Real.log (500000 / 545871) ≤ (43887293 / 500000000) := by
  have h := checkLog_sound (w := (45871 / 1045871)) (n := 12)
    (lo := (17554917 / 200000000)) (hi := (43887293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545871 / 500000) = 1/(500000 / 545871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4470 : Bounds (17554917 / 200000000) (43887293 / 500000000) (Real.log (545871 / 500000)) := by
  have h := reflection_log_4470_neg
  have he : Real.log (545871 / 500000) = -Real.log (500000 / 545871) := by
    rw [show ((545871 / 500000) : ℝ) = ((500000 / 545871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4471_neg : (96226799 / 1000000000) ≤ -Real.log (454129 / 500000) ∧
    -Real.log (454129 / 500000) ≤ (240567 / 2500000) := by
  have h := checkLog_sound (w := (45871 / 954129)) (n := 12)
    (lo := (96226799 / 1000000000)) (hi := (240567 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454129) = 1/(454129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4471 : Bounds (-240567 / 2500000) (-96226799 / 1000000000) (Real.log (454129 / 500000)) := by
  have h := reflection_log_4471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4472_neg : (4226107 / 500000000) ≤ -Real.log (247895851359 / 250000000000) ∧
    -Real.log (247895851359 / 250000000000) ≤ (1690443 / 200000000) := by
  have h := checkLog_sound (w := (2104148641 / 497895851359)) (n := 12)
    (lo := (4226107 / 500000000)) (hi := (1690443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247895851359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247895851359) = 1/(247895851359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4472 : Bounds (-1690443 / 200000000) (-4226107 / 500000000) (Real.log (247895851359 / 250000000000)) := by
  have h := reflection_log_4472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4473_neg : (1681831 / 200000000) ≤ -Real.log (991626102919 / 1000000000000) ∧
    -Real.log (991626102919 / 1000000000000) ≤ (2102289 / 250000000) := by
  have h := checkLog_sound (w := (8373897081 / 1991626102919)) (n := 12)
    (lo := (1681831 / 200000000)) (hi := (2102289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991626102919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991626102919) = 1/(991626102919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4473 : Bounds (-2102289 / 250000000) (-1681831 / 200000000) (Real.log (991626102919 / 1000000000000)) := by
  have h := reflection_log_4473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4474_neg : (2294143 / 12500000) ≤ -Real.log (500000000000 / 600726369331) ∧
    -Real.log (500000000000 / 600726369331) ≤ (183531441 / 1000000000) := by
  have h := checkLog_sound (w := (100726369331 / 1100726369331)) (n := 12)
    (lo := (2294143 / 12500000)) (hi := (183531441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600726369331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600726369331 / 500000000000) = 1/(500000000000 / 600726369331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4474 : Bounds (2294143 / 12500000) (183531441 / 1000000000) (Real.log (600726369331 / 500000000000)) := by
  have h := reflection_log_4474_neg
  have he : Real.log (600726369331 / 500000000000) = -Real.log (500000000000 / 600726369331) := by
    rw [show ((600726369331 / 500000000000) : ℝ) = ((500000000000 / 600726369331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4475_neg : (36800277 / 200000000) ≤ -Real.log (125000000000 / 150252186053) ∧
    -Real.log (125000000000 / 150252186053) ≤ (92000693 / 500000000) := by
  have h := checkLog_sound (w := (25252186053 / 275252186053)) (n := 12)
    (lo := (36800277 / 200000000)) (hi := (92000693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150252186053 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150252186053 / 125000000000) = 1/(125000000000 / 150252186053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4475 : Bounds (36800277 / 200000000) (92000693 / 500000000) (Real.log (150252186053 / 125000000000)) := by
  have h := reflection_log_4475_neg
  have he : Real.log (150252186053 / 125000000000) = -Real.log (125000000000 / 150252186053) := by
    rw [show ((150252186053 / 125000000000) : ℝ) = ((125000000000 / 150252186053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4476_neg : (368307717 / 1000000000) ≤ -Real.log (500000000000 / 722643354933) ∧
    -Real.log (500000000000 / 722643354933) ≤ (184153859 / 500000000) := by
  have h := checkLog_sound (w := (222643354933 / 1222643354933)) (n := 12)
    (lo := (368307717 / 1000000000)) (hi := (184153859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722643354933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722643354933 / 500000000000) = 1/(500000000000 / 722643354933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4476 : Bounds (368307717 / 1000000000) (184153859 / 500000000) (Real.log (722643354933 / 500000000000)) := by
  have h := reflection_log_4476_neg
  have he : Real.log (722643354933 / 500000000000) = -Real.log (500000000000 / 722643354933) := by
    rw [show ((722643354933 / 500000000000) : ℝ) = ((500000000000 / 722643354933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4477_neg : (18425729 / 50000000) ≤ -Real.log (50000000000 / 72279285889) ∧
    -Real.log (50000000000 / 72279285889) ≤ (368514581 / 1000000000) := by
  have h := checkLog_sound (w := (22279285889 / 122279285889)) (n := 12)
    (lo := (18425729 / 50000000)) (hi := (368514581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72279285889 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72279285889 / 50000000000) = 1/(50000000000 / 72279285889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4477 : Bounds (18425729 / 50000000) (368514581 / 1000000000) (Real.log (72279285889 / 50000000000)) := by
  have h := reflection_log_4477_neg
  have he : Real.log (72279285889 / 50000000000) = -Real.log (50000000000 / 72279285889) := by
    rw [show ((72279285889 / 50000000000) : ℝ) = ((50000000000 / 72279285889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4478_neg : (167461693 / 1000000000) ≤ -Real.log (10000 / 11823) ∧
    -Real.log (10000 / 11823) ≤ (83730847 / 500000000) := by
  have h := checkLog_sound (w := (1823 / 21823)) (n := 12)
    (lo := (167461693 / 1000000000)) (hi := (83730847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11823 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11823 / 10000) = 1/(10000 / 11823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4478 : Bounds (167461693 / 1000000000) (83730847 / 500000000) (Real.log (11823 / 10000)) := by
  have h := reflection_log_4478_neg
  have he : Real.log (11823 / 10000) = -Real.log (10000 / 11823) := by
    rw [show ((11823 / 10000) : ℝ) = ((10000 / 11823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4479_neg : (201259757 / 1000000000) ≤ -Real.log (8177 / 10000) ∧
    -Real.log (8177 / 10000) ≤ (100629879 / 500000000) := by
  have h := checkLog_sound (w := (1823 / 18177)) (n := 12)
    (lo := (201259757 / 1000000000)) (hi := (100629879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8177) = 1/(8177 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4479 : Bounds (-100629879 / 500000000) (-201259757 / 1000000000) (Real.log (8177 / 10000)) := by
  have h := reflection_log_4479_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
