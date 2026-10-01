import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10624_neg : (187805303 / 500000000) ≤ -Real.log (500000000000 / 727940056879) ∧
    -Real.log (500000000000 / 727940056879) ≤ (375610607 / 1000000000) := by
  have h := checkLog_sound (w := (227940056879 / 1227940056879)) (n := 12)
    (lo := (187805303 / 500000000)) (hi := (375610607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727940056879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727940056879 / 500000000000) = 1/(500000000000 / 727940056879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10624 : Bounds (187805303 / 500000000) (375610607 / 1000000000) (Real.log (727940056879 / 500000000000)) := by
  have h := reflection_log_10624_neg
  have he : Real.log (727940056879 / 500000000000) = -Real.log (500000000000 / 727940056879) := by
    rw [show ((727940056879 / 500000000000) : ℝ) = ((500000000000 / 727940056879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10625_neg : (756070547 / 1000000000) ≤ -Real.log (500000000000 / 1064945226917) ∧
    -Real.log (500000000000 / 1064945226917) ≤ (756070549 / 1000000000) := by
  have h := checkLog_sound (w := (64945226917 / 2064945226917)) (n := 12)
    (lo := (62923367 / 1000000000)) (hi := (7865421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064945226917 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064945226917 / 1000000000000) = 1/(500000000000 / 1064945226917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10625 : Bounds (756070547 / 1000000000) (756070549 / 1000000000) (Real.log (1064945226917 / 500000000000)) := by
  have h := reflection_log_10625_neg
  have he : Real.log (1064945226917 / 500000000000) = -Real.log (500000000000 / 1064945226917) := by
    rw [show ((1064945226917 / 500000000000) : ℝ) = ((500000000000 / 1064945226917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10626_neg : (379185601 / 500000000) ≤ -Real.log (500000000000 / 1067398119123) ∧
    -Real.log (500000000000 / 1067398119123) ≤ (189592801 / 250000000) := by
  have h := checkLog_sound (w := (67398119123 / 2067398119123)) (n := 12)
    (lo := (32612011 / 500000000)) (hi := (65224023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067398119123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067398119123 / 1000000000000) = 1/(500000000000 / 1067398119123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10626 : Bounds (379185601 / 500000000) (189592801 / 250000000) (Real.log (1067398119123 / 500000000000)) := by
  have h := reflection_log_10626_neg
  have he : Real.log (1067398119123 / 500000000000) = -Real.log (500000000000 / 1067398119123) := by
    rw [show ((1067398119123 / 500000000000) : ℝ) = ((500000000000 / 1067398119123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10627_neg : (38711019 / 125000000) ≤ -Real.log (1000 / 1363) ∧
    -Real.log (1000 / 1363) ≤ (309688153 / 1000000000) := by
  have h := checkLog_sound (w := (363 / 2363)) (n := 12)
    (lo := (38711019 / 125000000)) (hi := (309688153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363 / 1000) = 1/(1000 / 1363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10627 : Bounds (38711019 / 125000000) (309688153 / 1000000000) (Real.log (1363 / 1000)) := by
  have h := reflection_log_10627_neg
  have he : Real.log (1363 / 1000) = -Real.log (1000 / 1363) := by
    rw [show ((1363 / 1000) : ℝ) = ((1000 / 1363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10628_neg : (450985623 / 1000000000) ≤ -Real.log (637 / 1000) ∧
    -Real.log (637 / 1000) ≤ (56373203 / 125000000) := by
  have h := checkLog_sound (w := (363 / 1637)) (n := 12)
    (lo := (450985623 / 1000000000)) (hi := (56373203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 637) = 1/(637 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10628 : Bounds (-56373203 / 125000000) (-450985623 / 1000000000) (Real.log (637 / 1000)) := by
  have h := reflection_log_10628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10629_neg : (181467 / 500000000) ≤ -Real.log (1000000 / 1000363) ∧
    -Real.log (1000000 / 1000363) ≤ (72587 / 200000000) := by
  have h := checkLog_sound (w := (363 / 2000363)) (n := 12)
    (lo := (181467 / 500000000)) (hi := (72587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000363 / 1000000) = 1/(1000000 / 1000363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10629 : Bounds (181467 / 500000000) (72587 / 200000000) (Real.log (1000363 / 1000000)) := by
  have h := reflection_log_10629_neg
  have he : Real.log (1000363 / 1000000) = -Real.log (1000000 / 1000363) := by
    rw [show ((1000363 / 1000000) : ℝ) = ((1000000 / 1000363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10630_neg : (72613 / 200000000) ≤ -Real.log (999637 / 1000000) ∧
    -Real.log (999637 / 1000000) ≤ (181533 / 500000000) := by
  have h := checkLog_sound (w := (363 / 1999637)) (n := 12)
    (lo := (72613 / 200000000)) (hi := (181533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999637) = 1/(999637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10630 : Bounds (-181533 / 500000000) (-72613 / 200000000) (Real.log (999637 / 1000000)) := by
  have h := reflection_log_10630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10631_neg : (169973971 / 1000000000) ≤ -Real.log (500000 / 592637) ∧
    -Real.log (500000 / 592637) ≤ (42493493 / 250000000) := by
  have h := checkLog_sound (w := (92637 / 1092637)) (n := 12)
    (lo := (169973971 / 1000000000)) (hi := (42493493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592637 / 500000) = 1/(500000 / 592637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10631 : Bounds (169973971 / 1000000000) (42493493 / 250000000) (Real.log (592637 / 500000)) := by
  have h := reflection_log_10631_neg
  have he : Real.log (592637 / 500000) = -Real.log (500000 / 592637) := by
    rw [show ((592637 / 500000) : ℝ) = ((500000 / 592637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10632_neg : (102451709 / 500000000) ≤ -Real.log (407363 / 500000) ∧
    -Real.log (407363 / 500000) ≤ (204903419 / 1000000000) := by
  have h := checkLog_sound (w := (92637 / 907363)) (n := 12)
    (lo := (102451709 / 500000000)) (hi := (204903419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407363) = 1/(407363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10632 : Bounds (-204903419 / 1000000000) (-102451709 / 500000000) (Real.log (407363 / 500000)) := by
  have h := reflection_log_10632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10633_neg : (170726257 / 1000000000) ≤ -Real.log (500000 / 593083) ∧
    -Real.log (500000 / 593083) ≤ (85363129 / 500000000) := by
  have h := checkLog_sound (w := (93083 / 1093083)) (n := 12)
    (lo := (170726257 / 1000000000)) (hi := (85363129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593083 / 500000) = 1/(500000 / 593083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10633 : Bounds (170726257 / 1000000000) (85363129 / 500000000) (Real.log (593083 / 500000)) := by
  have h := reflection_log_10633_neg
  have he : Real.log (593083 / 500000) = -Real.log (500000 / 593083) := by
    rw [show ((593083 / 500000) : ℝ) = ((500000 / 593083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10634_neg : (12874929 / 62500000) ≤ -Real.log (406917 / 500000) ∧
    -Real.log (406917 / 500000) ≤ (41199773 / 200000000) := by
  have h := checkLog_sound (w := (93083 / 906917)) (n := 12)
    (lo := (12874929 / 62500000)) (hi := (41199773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406917) = 1/(406917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10634 : Bounds (-41199773 / 200000000) (-12874929 / 62500000) (Real.log (406917 / 500000)) := by
  have h := reflection_log_10634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10635_neg : (35272607 / 1000000000) ≤ -Real.log (241335555111 / 250000000000) ∧
    -Real.log (241335555111 / 250000000000) ≤ (1102269 / 31250000) := by
  have h := checkLog_sound (w := (8664444889 / 491335555111)) (n := 12)
    (lo := (35272607 / 1000000000)) (hi := (1102269 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241335555111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241335555111) = 1/(241335555111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10635 : Bounds (-1102269 / 31250000) (-35272607 / 1000000000) (Real.log (241335555111 / 250000000000)) := by
  have h := reflection_log_10635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10636_neg : (34929447 / 1000000000) ≤ -Real.log (241418386231 / 250000000000) ∧
    -Real.log (241418386231 / 250000000000) ≤ (4366181 / 125000000) := by
  have h := checkLog_sound (w := (8581613769 / 491418386231)) (n := 12)
    (lo := (34929447 / 1000000000)) (hi := (4366181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241418386231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241418386231) = 1/(241418386231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10636 : Bounds (-4366181 / 125000000) (-34929447 / 1000000000) (Real.log (241418386231 / 250000000000)) := by
  have h := reflection_log_10636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10637_neg : (37487739 / 100000000) ≤ -Real.log (250000000000 / 363703257291) ∧
    -Real.log (250000000000 / 363703257291) ≤ (374877391 / 1000000000) := by
  have h := checkLog_sound (w := (113703257291 / 613703257291)) (n := 12)
    (lo := (37487739 / 100000000)) (hi := (374877391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363703257291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363703257291 / 250000000000) = 1/(250000000000 / 363703257291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10637 : Bounds (37487739 / 100000000) (374877391 / 1000000000) (Real.log (363703257291 / 250000000000)) := by
  have h := reflection_log_10637_neg
  have he : Real.log (363703257291 / 250000000000) = -Real.log (250000000000 / 363703257291) := by
    rw [show ((363703257291 / 250000000000) : ℝ) = ((250000000000 / 363703257291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10638_neg : (188362561 / 500000000) ≤ -Real.log (250000000000 / 364375904669) ∧
    -Real.log (250000000000 / 364375904669) ≤ (376725123 / 1000000000) := by
  have h := checkLog_sound (w := (114375904669 / 614375904669)) (n := 12)
    (lo := (188362561 / 500000000)) (hi := (376725123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364375904669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364375904669 / 250000000000) = 1/(250000000000 / 364375904669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10638 : Bounds (188362561 / 500000000) (376725123 / 1000000000) (Real.log (364375904669 / 250000000000)) := by
  have h := reflection_log_10638_neg
  have he : Real.log (364375904669 / 250000000000) = -Real.log (250000000000 / 364375904669) := by
    rw [show ((364375904669 / 250000000000) : ℝ) = ((250000000000 / 364375904669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10639_neg : (379185601 / 500000000) ≤ -Real.log (250000000000 / 533699059561) ∧
    -Real.log (250000000000 / 533699059561) ≤ (189592801 / 250000000) := by
  have h := checkLog_sound (w := (33699059561 / 1033699059561)) (n := 12)
    (lo := (32612011 / 500000000)) (hi := (65224023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533699059561 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533699059561 / 500000000000) = 1/(250000000000 / 533699059561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10639 : Bounds (379185601 / 500000000) (189592801 / 250000000) (Real.log (533699059561 / 250000000000)) := by
  have h := reflection_log_10639_neg
  have he : Real.log (533699059561 / 250000000000) = -Real.log (250000000000 / 533699059561) := by
    rw [show ((533699059561 / 250000000000) : ℝ) = ((250000000000 / 533699059561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10640_neg : (30426951 / 40000000) ≤ -Real.log (125000000000 / 267464678179) ∧
    -Real.log (125000000000 / 267464678179) ≤ (760673777 / 1000000000) := by
  have h := checkLog_sound (w := (17464678179 / 517464678179)) (n := 12)
    (lo := (13505319 / 200000000)) (hi := (16881649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267464678179 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267464678179 / 250000000000) = 1/(125000000000 / 267464678179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10640 : Bounds (30426951 / 40000000) (760673777 / 1000000000) (Real.log (267464678179 / 125000000000)) := by
  have h := reflection_log_10640_neg
  have he : Real.log (267464678179 / 125000000000) = -Real.log (125000000000 / 267464678179) := by
    rw [show ((267464678179 / 125000000000) : ℝ) = ((125000000000 / 267464678179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10641_neg : (310421559 / 1000000000) ≤ -Real.log (250 / 341) ∧
    -Real.log (250 / 341) ≤ (7760539 / 25000000) := by
  have h := checkLog_sound (w := (91 / 591)) (n := 12)
    (lo := (310421559 / 1000000000)) (hi := (7760539 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 250) = 1/(250 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10641 : Bounds (310421559 / 1000000000) (7760539 / 25000000) (Real.log (341 / 250)) := by
  have h := reflection_log_10641_neg
  have he : Real.log (341 / 250) = -Real.log (250 / 341) := by
    rw [show ((341 / 250) : ℝ) = ((250 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10642_neg : (90511343 / 200000000) ≤ -Real.log (159 / 250) ∧
    -Real.log (159 / 250) ≤ (113139179 / 250000000) := by
  have h := checkLog_sound (w := (91 / 409)) (n := 12)
    (lo := (90511343 / 200000000)) (hi := (113139179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 159) = 1/(159 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10642 : Bounds (-113139179 / 250000000) (-90511343 / 200000000) (Real.log (159 / 250)) := by
  have h := reflection_log_10642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10643_neg : (363933 / 1000000000) ≤ -Real.log (250000 / 250091) ∧
    -Real.log (250000 / 250091) ≤ (181967 / 500000000) := by
  have h := checkLog_sound (w := (91 / 500091)) (n := 12)
    (lo := (363933 / 1000000000)) (hi := (181967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250091 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250091 / 250000) = 1/(250000 / 250091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10643 : Bounds (363933 / 1000000000) (181967 / 500000000) (Real.log (250091 / 250000)) := by
  have h := reflection_log_10643_neg
  have he : Real.log (250091 / 250000) = -Real.log (250000 / 250091) := by
    rw [show ((250091 / 250000) : ℝ) = ((250000 / 250091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10644_neg : (182033 / 500000000) ≤ -Real.log (249909 / 250000) ∧
    -Real.log (249909 / 250000) ≤ (364067 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 499909)) (n := 12)
    (lo := (182033 / 500000000)) (hi := (364067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249909) = 1/(249909 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10644 : Bounds (-364067 / 1000000000) (-182033 / 500000000) (Real.log (249909 / 250000)) := by
  have h := reflection_log_10644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10645_neg : (170427771 / 1000000000) ≤ -Real.log (250000 / 296453) ∧
    -Real.log (250000 / 296453) ≤ (42606943 / 250000000) := by
  have h := checkLog_sound (w := (46453 / 546453)) (n := 12)
    (lo := (170427771 / 1000000000)) (hi := (42606943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296453 / 250000) = 1/(250000 / 296453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10645 : Bounds (170427771 / 1000000000) (42606943 / 250000000) (Real.log (296453 / 250000)) := by
  have h := reflection_log_10645_neg
  have he : Real.log (296453 / 250000) = -Real.log (250000 / 296453) := by
    rw [show ((296453 / 250000) : ℝ) = ((250000 / 296453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10646_neg : (205563981 / 1000000000) ≤ -Real.log (203547 / 250000) ∧
    -Real.log (203547 / 250000) ≤ (102781991 / 500000000) := by
  have h := checkLog_sound (w := (46453 / 453547)) (n := 12)
    (lo := (205563981 / 1000000000)) (hi := (102781991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203547) = 1/(203547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10646 : Bounds (-102781991 / 500000000) (-205563981 / 1000000000) (Real.log (203547 / 250000)) := by
  have h := reflection_log_10646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10647_neg : (171180559 / 1000000000) ≤ -Real.log (200000 / 237341) ∧
    -Real.log (200000 / 237341) ≤ (2139757 / 12500000) := by
  have h := checkLog_sound (w := (37341 / 437341)) (n := 12)
    (lo := (171180559 / 1000000000)) (hi := (2139757 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237341 / 200000) = 1/(200000 / 237341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10647 : Bounds (171180559 / 1000000000) (2139757 / 12500000) (Real.log (237341 / 200000)) := by
  have h := reflection_log_10647_neg
  have he : Real.log (237341 / 200000) = -Real.log (200000 / 237341) := by
    rw [show ((237341 / 200000) : ℝ) = ((200000 / 237341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10648_neg : (206661381 / 1000000000) ≤ -Real.log (162659 / 200000) ∧
    -Real.log (162659 / 200000) ≤ (103330691 / 500000000) := by
  have h := checkLog_sound (w := (37341 / 362659)) (n := 12)
    (lo := (206661381 / 1000000000)) (hi := (103330691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162659) = 1/(162659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10648 : Bounds (-103330691 / 500000000) (-206661381 / 1000000000) (Real.log (162659 / 200000)) := by
  have h := reflection_log_10648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10649_neg : (17740411 / 500000000) ≤ -Real.log (38605649719 / 40000000000) ∧
    -Real.log (38605649719 / 40000000000) ≤ (35480823 / 1000000000) := by
  have h := checkLog_sound (w := (1394350281 / 78605649719)) (n := 12)
    (lo := (17740411 / 500000000)) (hi := (35480823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38605649719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38605649719) = 1/(38605649719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10649 : Bounds (-35480823 / 1000000000) (-17740411 / 500000000) (Real.log (38605649719 / 40000000000)) := by
  have h := reflection_log_10649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10650_neg : (35136209 / 1000000000) ≤ -Real.log (60342118791 / 62500000000) ∧
    -Real.log (60342118791 / 62500000000) ≤ (3513621 / 100000000) := by
  have h := checkLog_sound (w := (2157881209 / 122842118791)) (n := 12)
    (lo := (35136209 / 1000000000)) (hi := (3513621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60342118791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60342118791) = 1/(60342118791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10650 : Bounds (-3513621 / 100000000) (-35136209 / 1000000000) (Real.log (60342118791 / 62500000000)) := by
  have h := reflection_log_10650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10651_neg : (375991753 / 1000000000) ≤ -Real.log (100000000000 / 145643512309) ∧
    -Real.log (100000000000 / 145643512309) ≤ (187995877 / 500000000) := by
  have h := checkLog_sound (w := (45643512309 / 245643512309)) (n := 12)
    (lo := (375991753 / 1000000000)) (hi := (187995877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145643512309 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145643512309 / 100000000000) = 1/(100000000000 / 145643512309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10651 : Bounds (375991753 / 1000000000) (187995877 / 500000000) (Real.log (145643512309 / 100000000000)) := by
  have h := reflection_log_10651_neg
  have he : Real.log (145643512309 / 100000000000) = -Real.log (100000000000 / 145643512309) := by
    rw [show ((145643512309 / 100000000000) : ℝ) = ((100000000000 / 145643512309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10652_neg : (18892097 / 50000000) ≤ -Real.log (100000000000 / 145913229517) ∧
    -Real.log (100000000000 / 145913229517) ≤ (377841941 / 1000000000) := by
  have h := checkLog_sound (w := (45913229517 / 245913229517)) (n := 12)
    (lo := (18892097 / 50000000)) (hi := (377841941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145913229517 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145913229517 / 100000000000) = 1/(100000000000 / 145913229517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10652 : Bounds (18892097 / 50000000) (377841941 / 1000000000) (Real.log (145913229517 / 100000000000)) := by
  have h := reflection_log_10652_neg
  have he : Real.log (145913229517 / 100000000000) = -Real.log (100000000000 / 145913229517) := by
    rw [show ((145913229517 / 100000000000) : ℝ) = ((100000000000 / 145913229517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10653_neg : (30426951 / 40000000) ≤ -Real.log (100000000000 / 213971742543) ∧
    -Real.log (100000000000 / 213971742543) ≤ (760673777 / 1000000000) := by
  have h := checkLog_sound (w := (13971742543 / 413971742543)) (n := 12)
    (lo := (13505319 / 200000000)) (hi := (16881649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213971742543 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(213971742543 / 200000000000) = 1/(100000000000 / 213971742543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10653 : Bounds (30426951 / 40000000) (760673777 / 1000000000) (Real.log (213971742543 / 100000000000)) := by
  have h := reflection_log_10653_neg
  have he : Real.log (213971742543 / 100000000000) = -Real.log (100000000000 / 213971742543) := by
    rw [show ((213971742543 / 100000000000) : ℝ) = ((100000000000 / 213971742543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10654_neg : (381489137 / 500000000) ≤ -Real.log (250000000000 / 536163522013) ∧
    -Real.log (250000000000 / 536163522013) ≤ (190744569 / 250000000) := by
  have h := checkLog_sound (w := (36163522013 / 1036163522013)) (n := 12)
    (lo := (34915547 / 500000000)) (hi := (13966219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536163522013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(536163522013 / 500000000000) = 1/(250000000000 / 536163522013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10654 : Bounds (381489137 / 500000000) (190744569 / 250000000) (Real.log (536163522013 / 250000000000)) := by
  have h := reflection_log_10654_neg
  have he : Real.log (536163522013 / 250000000000) = -Real.log (250000000000 / 536163522013) := by
    rw [show ((536163522013 / 250000000000) : ℝ) = ((250000000000 / 536163522013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10655_neg : (77788607 / 250000000) ≤ -Real.log (200 / 273) ∧
    -Real.log (200 / 273) ≤ (311154429 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 473)) (n := 12)
    (lo := (77788607 / 250000000)) (hi := (311154429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273 / 200) = 1/(200 / 273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10655 : Bounds (77788607 / 250000000) (311154429 / 1000000000) (Real.log (273 / 200)) := by
  have h := reflection_log_10655_neg
  have he : Real.log (273 / 200) = -Real.log (200 / 273) := by
    rw [show ((273 / 200) : ℝ) = ((200 / 273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10656_neg : (11353257 / 25000000) ≤ -Real.log (127 / 200) ∧
    -Real.log (127 / 200) ≤ (454130281 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 127) = 1/(127 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10656 : Bounds (-454130281 / 1000000000) (-11353257 / 25000000) (Real.log (127 / 200)) := by
  have h := reflection_log_10656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10657_neg : (364933 / 1000000000) ≤ -Real.log (200000 / 200073) ∧
    -Real.log (200000 / 200073) ≤ (182467 / 500000000) := by
  have h := checkLog_sound (w := (73 / 400073)) (n := 12)
    (lo := (364933 / 1000000000)) (hi := (182467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200073 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200073 / 200000) = 1/(200000 / 200073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10657 : Bounds (364933 / 1000000000) (182467 / 500000000) (Real.log (200073 / 200000)) := by
  have h := reflection_log_10657_neg
  have he : Real.log (200073 / 200000) = -Real.log (200000 / 200073) := by
    rw [show ((200073 / 200000) : ℝ) = ((200000 / 200073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10658_neg : (182533 / 500000000) ≤ -Real.log (199927 / 200000) ∧
    -Real.log (199927 / 200000) ≤ (365067 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 399927)) (n := 12)
    (lo := (182533 / 500000000)) (hi := (365067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199927) = 1/(199927 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10658 : Bounds (-365067 / 1000000000) (-182533 / 500000000) (Real.log (199927 / 200000)) := by
  have h := reflection_log_10658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10659_neg : (170880523 / 1000000000) ≤ -Real.log (1000000 / 1186349) ∧
    -Real.log (1000000 / 1186349) ≤ (42720131 / 250000000) := by
  have h := checkLog_sound (w := (186349 / 2186349)) (n := 12)
    (lo := (170880523 / 1000000000)) (hi := (42720131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186349 / 1000000) = 1/(1000000 / 1186349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10659 : Bounds (170880523 / 1000000000) (42720131 / 250000000) (Real.log (1186349 / 1000000)) := by
  have h := reflection_log_10659_neg
  have he : Real.log (1186349 / 1000000) = -Real.log (1000000 / 1186349) := by
    rw [show ((1186349 / 1000000) : ℝ) = ((1000000 / 1186349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10660_neg : (206223751 / 1000000000) ≤ -Real.log (813651 / 1000000) ∧
    -Real.log (813651 / 1000000) ≤ (25777969 / 125000000) := by
  have h := checkLog_sound (w := (186349 / 1813651)) (n := 12)
    (lo := (206223751 / 1000000000)) (hi := (25777969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813651) = 1/(813651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10660 : Bounds (-25777969 / 125000000) (-206223751 / 1000000000) (Real.log (813651 / 1000000)) := by
  have h := reflection_log_10660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10661_neg : (85817327 / 500000000) ≤ -Real.log (250000 / 296811) ∧
    -Real.log (250000 / 296811) ≤ (34326931 / 200000000) := by
  have h := checkLog_sound (w := (46811 / 546811)) (n := 12)
    (lo := (85817327 / 500000000)) (hi := (34326931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296811 / 250000) = 1/(250000 / 296811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10661 : Bounds (85817327 / 500000000) (34326931 / 200000000) (Real.log (296811 / 250000)) := by
  have h := reflection_log_10661_neg
  have he : Real.log (296811 / 250000) = -Real.log (250000 / 296811) := by
    rw [show ((296811 / 250000) : ℝ) = ((250000 / 296811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10662_neg : (207324337 / 1000000000) ≤ -Real.log (203189 / 250000) ∧
    -Real.log (203189 / 250000) ≤ (103662169 / 500000000) := by
  have h := checkLog_sound (w := (46811 / 453189)) (n := 12)
    (lo := (207324337 / 1000000000)) (hi := (103662169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203189) = 1/(203189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10662 : Bounds (-103662169 / 500000000) (-207324337 / 1000000000) (Real.log (203189 / 250000)) := by
  have h := reflection_log_10662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10663_neg : (17844841 / 500000000) ≤ -Real.log (60308730279 / 62500000000) ∧
    -Real.log (60308730279 / 62500000000) ≤ (35689683 / 1000000000) := by
  have h := checkLog_sound (w := (2191269721 / 122808730279)) (n := 12)
    (lo := (17844841 / 500000000)) (hi := (35689683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60308730279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60308730279) = 1/(60308730279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10663 : Bounds (-35689683 / 1000000000) (-17844841 / 500000000) (Real.log (60308730279 / 62500000000)) := by
  have h := reflection_log_10663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10664_neg : (8835807 / 250000000) ≤ -Real.log (965274050199 / 1000000000000) ∧
    -Real.log (965274050199 / 1000000000000) ≤ (35343229 / 1000000000) := by
  have h := checkLog_sound (w := (34725949801 / 1965274050199)) (n := 12)
    (lo := (8835807 / 250000000)) (hi := (35343229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965274050199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965274050199) = 1/(965274050199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10664 : Bounds (-35343229 / 1000000000) (-8835807 / 250000000) (Real.log (965274050199 / 1000000000000)) := by
  have h := reflection_log_10664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10665_neg : (15084171 / 40000000) ≤ -Real.log (250000000000 / 364514085277) ∧
    -Real.log (250000000000 / 364514085277) ≤ (94276069 / 250000000) := by
  have h := checkLog_sound (w := (114514085277 / 614514085277)) (n := 12)
    (lo := (15084171 / 40000000)) (hi := (94276069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364514085277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364514085277 / 250000000000) = 1/(250000000000 / 364514085277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10665 : Bounds (15084171 / 40000000) (94276069 / 250000000) (Real.log (364514085277 / 250000000000)) := by
  have h := reflection_log_10665_neg
  have he : Real.log (364514085277 / 250000000000) = -Real.log (250000000000 / 364514085277) := by
    rw [show ((364514085277 / 250000000000) : ℝ) = ((250000000000 / 364514085277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10666_neg : (23684937 / 62500000) ≤ -Real.log (125000000000 / 182595391483) ∧
    -Real.log (125000000000 / 182595391483) ≤ (378958993 / 1000000000) := by
  have h := checkLog_sound (w := (57595391483 / 307595391483)) (n := 12)
    (lo := (23684937 / 62500000)) (hi := (378958993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182595391483 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182595391483 / 125000000000) = 1/(125000000000 / 182595391483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10666 : Bounds (23684937 / 62500000) (378958993 / 1000000000) (Real.log (182595391483 / 125000000000)) := by
  have h := reflection_log_10666_neg
  have he : Real.log (182595391483 / 125000000000) = -Real.log (125000000000 / 182595391483) := by
    rw [show ((182595391483 / 125000000000) : ℝ) = ((125000000000 / 182595391483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10667_neg : (381489137 / 500000000) ≤ -Real.log (20000000000 / 42893081761) ∧
    -Real.log (20000000000 / 42893081761) ≤ (190744569 / 250000000) := by
  have h := checkLog_sound (w := (2893081761 / 82893081761)) (n := 12)
    (lo := (34915547 / 500000000)) (hi := (13966219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42893081761 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42893081761 / 40000000000) = 1/(20000000000 / 42893081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10667 : Bounds (381489137 / 500000000) (190744569 / 250000000) (Real.log (42893081761 / 20000000000)) := by
  have h := reflection_log_10667_neg
  have he : Real.log (42893081761 / 20000000000) = -Real.log (20000000000 / 42893081761) := by
    rw [show ((42893081761 / 20000000000) : ℝ) = ((20000000000 / 42893081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10668_neg : (191321177 / 250000000) ≤ -Real.log (500000000000 / 1074803149607) ∧
    -Real.log (500000000000 / 1074803149607) ≤ (76528471 / 100000000) := by
  have h := checkLog_sound (w := (74803149607 / 2074803149607)) (n := 12)
    (lo := (9017191 / 125000000)) (hi := (72137529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074803149607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074803149607 / 1000000000000) = 1/(500000000000 / 1074803149607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10668 : Bounds (191321177 / 250000000) (76528471 / 100000000) (Real.log (1074803149607 / 500000000000)) := by
  have h := reflection_log_10668_neg
  have he : Real.log (1074803149607 / 500000000000) = -Real.log (500000000000 / 1074803149607) := by
    rw [show ((1074803149607 / 500000000000) : ℝ) = ((500000000000 / 1074803149607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10669_neg : (311886761 / 1000000000) ≤ -Real.log (500 / 683) ∧
    -Real.log (500 / 683) ≤ (155943381 / 500000000) := by
  have h := checkLog_sound (w := (183 / 1183)) (n := 12)
    (lo := (311886761 / 1000000000)) (hi := (155943381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683 / 500) = 1/(500 / 683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10669 : Bounds (311886761 / 1000000000) (155943381 / 500000000) (Real.log (683 / 500)) := by
  have h := reflection_log_10669_neg
  have he : Real.log (683 / 500) = -Real.log (500 / 683) := by
    rw [show ((683 / 500) : ℝ) = ((500 / 683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10670_neg : (113926581 / 250000000) ≤ -Real.log (317 / 500) ∧
    -Real.log (317 / 500) ≤ (18228253 / 40000000) := by
  have h := checkLog_sound (w := (183 / 817)) (n := 12)
    (lo := (113926581 / 250000000)) (hi := (18228253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 317) = 1/(317 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10670 : Bounds (-18228253 / 40000000) (-113926581 / 250000000) (Real.log (317 / 500)) := by
  have h := reflection_log_10670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10671_neg : (365933 / 1000000000) ≤ -Real.log (500000 / 500183) ∧
    -Real.log (500000 / 500183) ≤ (182967 / 500000000) := by
  have h := checkLog_sound (w := (183 / 1000183)) (n := 12)
    (lo := (365933 / 1000000000)) (hi := (182967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500183 / 500000) = 1/(500000 / 500183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10671 : Bounds (365933 / 1000000000) (182967 / 500000000) (Real.log (500183 / 500000)) := by
  have h := reflection_log_10671_neg
  have he : Real.log (500183 / 500000) = -Real.log (500000 / 500183) := by
    rw [show ((500183 / 500000) : ℝ) = ((500000 / 500183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10672_neg : (183033 / 500000000) ≤ -Real.log (499817 / 500000) ∧
    -Real.log (499817 / 500000) ≤ (366067 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 999817)) (n := 12)
    (lo := (183033 / 500000000)) (hi := (366067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499817) = 1/(499817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10672 : Bounds (-366067 / 1000000000) (-183033 / 500000000) (Real.log (499817 / 500000)) := by
  have h := reflection_log_10672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10673_neg : (171333913 / 1000000000) ≤ -Real.log (1000000 / 1186887) ∧
    -Real.log (1000000 / 1186887) ≤ (85666957 / 500000000) := by
  have h := checkLog_sound (w := (186887 / 2186887)) (n := 12)
    (lo := (171333913 / 1000000000)) (hi := (85666957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186887 / 1000000) = 1/(1000000 / 1186887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10673 : Bounds (171333913 / 1000000000) (85666957 / 500000000) (Real.log (1186887 / 1000000)) := by
  have h := reflection_log_10673_neg
  have he : Real.log (1186887 / 1000000) = -Real.log (1000000 / 1186887) := by
    rw [show ((1186887 / 1000000) : ℝ) = ((1000000 / 1186887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10674_neg : (206885187 / 1000000000) ≤ -Real.log (813113 / 1000000) ∧
    -Real.log (813113 / 1000000) ≤ (51721297 / 250000000) := by
  have h := checkLog_sound (w := (186887 / 1813113)) (n := 12)
    (lo := (206885187 / 1000000000)) (hi := (51721297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813113) = 1/(813113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10674 : Bounds (-51721297 / 250000000) (-206885187 / 1000000000) (Real.log (813113 / 1000000)) := by
  have h := reflection_log_10674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10675_neg : (5377767 / 31250000) ≤ -Real.log (1000000 / 1187783) ∧
    -Real.log (1000000 / 1187783) ≤ (34417709 / 200000000) := by
  have h := checkLog_sound (w := (187783 / 2187783)) (n := 12)
    (lo := (5377767 / 31250000)) (hi := (34417709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187783 / 1000000) = 1/(1000000 / 1187783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10675 : Bounds (5377767 / 31250000) (34417709 / 200000000) (Real.log (1187783 / 1000000)) := by
  have h := reflection_log_10675_neg
  have he : Real.log (1187783 / 1000000) = -Real.log (1000000 / 1187783) := by
    rw [show ((1187783 / 1000000) : ℝ) = ((1000000 / 1187783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10676_neg : (207987733 / 1000000000) ≤ -Real.log (812217 / 1000000) ∧
    -Real.log (812217 / 1000000) ≤ (103993867 / 500000000) := by
  have h := checkLog_sound (w := (187783 / 1812217)) (n := 12)
    (lo := (207987733 / 1000000000)) (hi := (103993867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812217) = 1/(812217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10676 : Bounds (-103993867 / 500000000) (-207987733 / 1000000000) (Real.log (812217 / 1000000)) := by
  have h := reflection_log_10676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10677_neg : (8974797 / 250000000) ≤ -Real.log (964737544911 / 1000000000000) ∧
    -Real.log (964737544911 / 1000000000000) ≤ (35899189 / 1000000000) := by
  have h := checkLog_sound (w := (35262455089 / 1964737544911)) (n := 12)
    (lo := (8974797 / 250000000)) (hi := (35899189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964737544911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964737544911) = 1/(964737544911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10677 : Bounds (-35899189 / 1000000000) (-8974797 / 250000000) (Real.log (964737544911 / 1000000000000)) := by
  have h := reflection_log_10677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10678_neg : (17775637 / 500000000) ≤ -Real.log (965073249231 / 1000000000000) ∧
    -Real.log (965073249231 / 1000000000000) ≤ (1422051 / 40000000) := by
  have h := checkLog_sound (w := (34926750769 / 1965073249231)) (n := 12)
    (lo := (17775637 / 500000000)) (hi := (1422051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965073249231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965073249231) = 1/(965073249231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10678 : Bounds (-1422051 / 40000000) (-17775637 / 500000000) (Real.log (965073249231 / 1000000000000)) := by
  have h := reflection_log_10678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10679_neg : (3782191 / 10000000) ≤ -Real.log (250000000000 / 364920681381) ∧
    -Real.log (250000000000 / 364920681381) ≤ (378219101 / 1000000000) := by
  have h := checkLog_sound (w := (114920681381 / 614920681381)) (n := 12)
    (lo := (3782191 / 10000000)) (hi := (378219101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364920681381 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364920681381 / 250000000000) = 1/(250000000000 / 364920681381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10679 : Bounds (3782191 / 10000000) (378219101 / 1000000000) (Real.log (364920681381 / 250000000000)) := by
  have h := reflection_log_10679_neg
  have he : Real.log (364920681381 / 250000000000) = -Real.log (250000000000 / 364920681381) := by
    rw [show ((364920681381 / 250000000000) : ℝ) = ((250000000000 / 364920681381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10680_neg : (380076277 / 1000000000) ≤ -Real.log (500000000000 / 731198066527) ∧
    -Real.log (500000000000 / 731198066527) ≤ (190038139 / 500000000) := by
  have h := checkLog_sound (w := (231198066527 / 1231198066527)) (n := 12)
    (lo := (380076277 / 1000000000)) (hi := (190038139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731198066527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731198066527 / 500000000000) = 1/(500000000000 / 731198066527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10680 : Bounds (380076277 / 1000000000) (190038139 / 500000000) (Real.log (731198066527 / 500000000000)) := by
  have h := reflection_log_10680_neg
  have he : Real.log (731198066527 / 500000000000) = -Real.log (500000000000 / 731198066527) := by
    rw [show ((731198066527 / 500000000000) : ℝ) = ((500000000000 / 731198066527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10681_neg : (191321177 / 250000000) ≤ -Real.log (250000000000 / 537401574803) ∧
    -Real.log (250000000000 / 537401574803) ≤ (76528471 / 100000000) := by
  have h := checkLog_sound (w := (37401574803 / 1037401574803)) (n := 12)
    (lo := (9017191 / 125000000)) (hi := (72137529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537401574803 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537401574803 / 500000000000) = 1/(250000000000 / 537401574803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10681 : Bounds (191321177 / 250000000) (76528471 / 100000000) (Real.log (537401574803 / 250000000000)) := by
  have h := reflection_log_10681_neg
  have he : Real.log (537401574803 / 250000000000) = -Real.log (250000000000 / 537401574803) := by
    rw [show ((537401574803 / 250000000000) : ℝ) = ((250000000000 / 537401574803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10682_neg : (153518617 / 200000000) ≤ -Real.log (500000000000 / 1077287066247) ∧
    -Real.log (500000000000 / 1077287066247) ≤ (767593087 / 1000000000) := by
  have h := checkLog_sound (w := (77287066247 / 2077287066247)) (n := 12)
    (lo := (14889181 / 200000000)) (hi := (37222953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077287066247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077287066247 / 1000000000000) = 1/(500000000000 / 1077287066247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10682 : Bounds (153518617 / 200000000) (767593087 / 1000000000) (Real.log (1077287066247 / 500000000000)) := by
  have h := reflection_log_10682_neg
  have he : Real.log (1077287066247 / 500000000000) = -Real.log (500000000000 / 1077287066247) := by
    rw [show ((1077287066247 / 500000000000) : ℝ) = ((500000000000 / 1077287066247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10683_neg : (312618557 / 1000000000) ≤ -Real.log (1000 / 1367) ∧
    -Real.log (1000 / 1367) ≤ (156309279 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2367)) (n := 12)
    (lo := (312618557 / 1000000000)) (hi := (156309279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1000) = 1/(1000 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10683 : Bounds (312618557 / 1000000000) (156309279 / 500000000) (Real.log (1367 / 1000)) := by
  have h := reflection_log_10683_neg
  have he : Real.log (1367 / 1000) = -Real.log (1000 / 1367) := by
    rw [show ((1367 / 1000) : ℝ) = ((1000 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10684_neg : (57160607 / 125000000) ≤ -Real.log (633 / 1000) ∧
    -Real.log (633 / 1000) ≤ (457284857 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1633)) (n := 12)
    (lo := (57160607 / 125000000)) (hi := (457284857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 633) = 1/(633 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10684 : Bounds (-457284857 / 1000000000) (-57160607 / 125000000) (Real.log (633 / 1000)) := by
  have h := reflection_log_10684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10685_neg : (91733 / 250000000) ≤ -Real.log (1000000 / 1000367) ∧
    -Real.log (1000000 / 1000367) ≤ (366933 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2000367)) (n := 12)
    (lo := (91733 / 250000000)) (hi := (366933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000367 / 1000000) = 1/(1000000 / 1000367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10685 : Bounds (91733 / 250000000) (366933 / 1000000000) (Real.log (1000367 / 1000000)) := by
  have h := reflection_log_10685_neg
  have he : Real.log (1000367 / 1000000) = -Real.log (1000000 / 1000367) := by
    rw [show ((1000367 / 1000000) : ℝ) = ((1000000 / 1000367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10686_neg : (367067 / 1000000000) ≤ -Real.log (999633 / 1000000) ∧
    -Real.log (999633 / 1000000) ≤ (91767 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1999633)) (n := 12)
    (lo := (367067 / 1000000000)) (hi := (91767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999633) = 1/(999633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10686 : Bounds (-91767 / 250000000) (-367067 / 1000000000) (Real.log (999633 / 1000000)) := by
  have h := reflection_log_10686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10687_neg : (171787939 / 1000000000) ≤ -Real.log (500000 / 593713) ∧
    -Real.log (500000 / 593713) ≤ (8589397 / 50000000) := by
  have h := checkLog_sound (w := (93713 / 1093713)) (n := 12)
    (lo := (171787939 / 1000000000)) (hi := (8589397 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593713 / 500000) = 1/(500000 / 593713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10687 : Bounds (171787939 / 1000000000) (8589397 / 50000000) (Real.log (593713 / 500000)) := by
  have h := reflection_log_10687_neg
  have he : Real.log (593713 / 500000) = -Real.log (500000 / 593713) := by
    rw [show ((593713 / 500000) : ℝ) = ((500000 / 593713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
