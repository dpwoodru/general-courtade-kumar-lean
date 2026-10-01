import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1664_neg : (32708523 / 100000000) ≤ -Real.log (500000000000 / 693459840077) ∧
    -Real.log (500000000000 / 693459840077) ≤ (327085231 / 1000000000) := by
  have h := checkLog_sound (w := (193459840077 / 1193459840077)) (n := 12)
    (lo := (32708523 / 100000000)) (hi := (327085231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693459840077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693459840077 / 500000000000) = 1/(500000000000 / 693459840077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1664 : Bounds (32708523 / 100000000) (327085231 / 1000000000) (Real.log (693459840077 / 500000000000)) := by
  have h := reflection_log_1664_neg
  have he : Real.log (693459840077 / 500000000000) = -Real.log (500000000000 / 693459840077) := by
    rw [show ((693459840077 / 500000000000) : ℝ) = ((500000000000 / 693459840077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1665_neg : (3757869 / 25000000) ≤ -Real.log (5000 / 5811) ∧
    -Real.log (5000 / 5811) ≤ (150314761 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 10811)) (n := 12)
    (lo := (3757869 / 25000000)) (hi := (150314761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5811 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5811 / 5000) = 1/(5000 / 5811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1665 : Bounds (3757869 / 25000000) (150314761 / 1000000000) (Real.log (5811 / 5000)) := by
  have h := reflection_log_1665_neg
  have he : Real.log (5811 / 5000) = -Real.log (5000 / 5811) := by
    rw [show ((5811 / 5000) : ℝ) = ((5000 / 5811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1666_neg : (17697587 / 100000000) ≤ -Real.log (4189 / 5000) ∧
    -Real.log (4189 / 5000) ≤ (176975871 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 9189)) (n := 12)
    (lo := (17697587 / 100000000)) (hi := (176975871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4189) = 1/(4189 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1666 : Bounds (-176975871 / 1000000000) (-17697587 / 100000000) (Real.log (4189 / 5000)) := by
  have h := reflection_log_1666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1667_neg : (81093 / 500000000) ≤ -Real.log (5000000 / 5000811) ∧
    -Real.log (5000000 / 5000811) ≤ (162187 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 10000811)) (n := 12)
    (lo := (81093 / 500000000)) (hi := (162187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000811 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000811 / 5000000) = 1/(5000000 / 5000811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1667 : Bounds (81093 / 500000000) (162187 / 1000000000) (Real.log (5000811 / 5000000)) := by
  have h := reflection_log_1667_neg
  have he : Real.log (5000811 / 5000000) = -Real.log (5000000 / 5000811) := by
    rw [show ((5000811 / 5000000) : ℝ) = ((5000000 / 5000811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1668_neg : (162213 / 1000000000) ≤ -Real.log (4999189 / 5000000) ∧
    -Real.log (4999189 / 5000000) ≤ (81107 / 500000000) := by
  have h := checkLog_sound (w := (811 / 9999189)) (n := 12)
    (lo := (162213 / 1000000000)) (hi := (81107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999189) = 1/(4999189 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1668 : Bounds (-81107 / 500000000) (-162213 / 1000000000) (Real.log (4999189 / 5000000)) := by
  have h := reflection_log_1668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1669_neg : (78215809 / 1000000000) ≤ -Real.log (250000 / 270339) ∧
    -Real.log (250000 / 270339) ≤ (7821581 / 100000000) := by
  have h := checkLog_sound (w := (20339 / 520339)) (n := 12)
    (lo := (78215809 / 1000000000)) (hi := (7821581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270339 / 250000) = 1/(250000 / 270339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1669 : Bounds (78215809 / 1000000000) (7821581 / 100000000) (Real.log (270339 / 250000)) := by
  have h := reflection_log_1669_neg
  have he : Real.log (270339 / 250000) = -Real.log (250000 / 270339) := by
    rw [show ((270339 / 250000) : ℝ) = ((250000 / 270339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1670_neg : (84856609 / 1000000000) ≤ -Real.log (229661 / 250000) ∧
    -Real.log (229661 / 250000) ≤ (8485661 / 100000000) := by
  have h := checkLog_sound (w := (20339 / 479661)) (n := 12)
    (lo := (84856609 / 1000000000)) (hi := (8485661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229661) = 1/(229661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1670 : Bounds (-8485661 / 100000000) (-84856609 / 1000000000) (Real.log (229661 / 250000)) := by
  have h := reflection_log_1670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1671_neg : (19603191 / 250000000) ≤ -Real.log (1000000 / 1081569) ∧
    -Real.log (1000000 / 1081569) ≤ (15682553 / 200000000) := by
  have h := checkLog_sound (w := (81569 / 2081569)) (n := 12)
    (lo := (19603191 / 250000000)) (hi := (15682553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081569 / 1000000) = 1/(1000000 / 1081569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1671 : Bounds (19603191 / 250000000) (15682553 / 200000000) (Real.log (1081569 / 1000000)) := by
  have h := reflection_log_1671_neg
  have he : Real.log (1081569 / 1000000) = -Real.log (1000000 / 1081569) := by
    rw [show ((1081569 / 1000000) : ℝ) = ((1000000 / 1081569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1672_neg : (85088499 / 1000000000) ≤ -Real.log (918431 / 1000000) ∧
    -Real.log (918431 / 1000000) ≤ (170177 / 2000000) := by
  have h := checkLog_sound (w := (81569 / 1918431)) (n := 12)
    (lo := (85088499 / 1000000000)) (hi := (170177 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918431) = 1/(918431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1672 : Bounds (-170177 / 2000000) (-85088499 / 1000000000) (Real.log (918431 / 1000000)) := by
  have h := reflection_log_1672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1673_neg : (3337867 / 500000000) ≤ -Real.log (993346498239 / 1000000000000) ∧
    -Real.log (993346498239 / 1000000000000) ≤ (1335147 / 200000000) := by
  have h := checkLog_sound (w := (6653501761 / 1993346498239)) (n := 12)
    (lo := (3337867 / 500000000)) (hi := (1335147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993346498239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993346498239) = 1/(993346498239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1673 : Bounds (-1335147 / 200000000) (-3337867 / 500000000) (Real.log (993346498239 / 1000000000000)) := by
  have h := reflection_log_1673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1674_neg : (8301 / 1250000) ≤ -Real.log (62086325079 / 62500000000) ∧
    -Real.log (62086325079 / 62500000000) ≤ (6640801 / 1000000000) := by
  have h := checkLog_sound (w := (413674921 / 124586325079)) (n := 12)
    (lo := (8301 / 1250000)) (hi := (6640801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62086325079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62086325079) = 1/(62086325079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1674 : Bounds (-6640801 / 1000000000) (-8301 / 1250000) (Real.log (62086325079 / 62500000000)) := by
  have h := reflection_log_1674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1675_neg : (81536209 / 500000000) ≤ -Real.log (100000000000 / 117712193189) ∧
    -Real.log (100000000000 / 117712193189) ≤ (163072419 / 1000000000) := by
  have h := checkLog_sound (w := (17712193189 / 217712193189)) (n := 12)
    (lo := (81536209 / 500000000)) (hi := (163072419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117712193189 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117712193189 / 100000000000) = 1/(100000000000 / 117712193189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1675 : Bounds (81536209 / 500000000) (163072419 / 1000000000) (Real.log (117712193189 / 100000000000)) := by
  have h := reflection_log_1675_neg
  have he : Real.log (117712193189 / 100000000000) = -Real.log (100000000000 / 117712193189) := by
    rw [show ((117712193189 / 100000000000) : ℝ) = ((100000000000 / 117712193189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1676_neg : (10218829 / 62500000) ≤ -Real.log (500000000000 / 588813422021) ∧
    -Real.log (500000000000 / 588813422021) ≤ (32700253 / 200000000) := by
  have h := checkLog_sound (w := (88813422021 / 1088813422021)) (n := 12)
    (lo := (10218829 / 62500000)) (hi := (32700253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588813422021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588813422021 / 500000000000) = 1/(500000000000 / 588813422021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1676 : Bounds (10218829 / 62500000) (32700253 / 200000000) (Real.log (588813422021 / 500000000000)) := by
  have h := reflection_log_1676_neg
  have he : Real.log (588813422021 / 500000000000) = -Real.log (500000000000 / 588813422021) := by
    rw [show ((588813422021 / 500000000000) : ℝ) = ((500000000000 / 588813422021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1677_neg : (32708523 / 100000000) ≤ -Real.log (125000000000 / 173364960019) ∧
    -Real.log (125000000000 / 173364960019) ≤ (327085231 / 1000000000) := by
  have h := checkLog_sound (w := (48364960019 / 298364960019)) (n := 12)
    (lo := (32708523 / 100000000)) (hi := (327085231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173364960019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173364960019 / 125000000000) = 1/(125000000000 / 173364960019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1677 : Bounds (32708523 / 100000000) (327085231 / 1000000000) (Real.log (173364960019 / 125000000000)) := by
  have h := reflection_log_1677_neg
  have he : Real.log (173364960019 / 125000000000) = -Real.log (125000000000 / 173364960019) := by
    rw [show ((173364960019 / 125000000000) : ℝ) = ((125000000000 / 173364960019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1678_neg : (327290631 / 1000000000) ≤ -Real.log (500000000000 / 693602291717) ∧
    -Real.log (500000000000 / 693602291717) ≤ (40911329 / 125000000) := by
  have h := checkLog_sound (w := (193602291717 / 1193602291717)) (n := 12)
    (lo := (327290631 / 1000000000)) (hi := (40911329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693602291717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693602291717 / 500000000000) = 1/(500000000000 / 693602291717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1678 : Bounds (327290631 / 1000000000) (40911329 / 125000000) (Real.log (693602291717 / 500000000000)) := by
  have h := reflection_log_1678_neg
  have he : Real.log (693602291717 / 500000000000) = -Real.log (500000000000 / 693602291717) := by
    rw [show ((693602291717 / 500000000000) : ℝ) = ((500000000000 / 693602291717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1679_neg : (188001 / 1250000) ≤ -Real.log (10000 / 11623) ∧
    -Real.log (10000 / 11623) ≤ (150400801 / 1000000000) := by
  have h := checkLog_sound (w := (1623 / 21623)) (n := 12)
    (lo := (188001 / 1250000)) (hi := (150400801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11623 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11623 / 10000) = 1/(10000 / 11623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1679 : Bounds (188001 / 1250000) (150400801 / 1000000000) (Real.log (11623 / 10000)) := by
  have h := reflection_log_1679_neg
  have he : Real.log (11623 / 10000) = -Real.log (10000 / 11623) := by
    rw [show ((11623 / 10000) : ℝ) = ((10000 / 11623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1680_neg : (177095237 / 1000000000) ≤ -Real.log (8377 / 10000) ∧
    -Real.log (8377 / 10000) ≤ (88547619 / 500000000) := by
  have h := checkLog_sound (w := (1623 / 18377)) (n := 12)
    (lo := (177095237 / 1000000000)) (hi := (88547619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8377) = 1/(8377 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1680 : Bounds (-88547619 / 500000000) (-177095237 / 1000000000) (Real.log (8377 / 10000)) := by
  have h := reflection_log_1680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1681_neg : (81143 / 500000000) ≤ -Real.log (10000000 / 10001623) ∧
    -Real.log (10000000 / 10001623) ≤ (162287 / 1000000000) := by
  have h := checkLog_sound (w := (1623 / 20001623)) (n := 12)
    (lo := (81143 / 500000000)) (hi := (162287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001623 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001623 / 10000000) = 1/(10000000 / 10001623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1681 : Bounds (81143 / 500000000) (162287 / 1000000000) (Real.log (10001623 / 10000000)) := by
  have h := reflection_log_1681_neg
  have he : Real.log (10001623 / 10000000) = -Real.log (10000000 / 10001623) := by
    rw [show ((10001623 / 10000000) : ℝ) = ((10000000 / 10001623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1682_neg : (162313 / 1000000000) ≤ -Real.log (9998377 / 10000000) ∧
    -Real.log (9998377 / 10000000) ≤ (81157 / 500000000) := by
  have h := checkLog_sound (w := (1623 / 19998377)) (n := 12)
    (lo := (162313 / 1000000000)) (hi := (81157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998377) = 1/(9998377 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1682 : Bounds (-81157 / 500000000) (-162313 / 1000000000) (Real.log (9998377 / 10000000)) := by
  have h := reflection_log_1682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1683_neg : (78262971 / 1000000000) ≤ -Real.log (1000000 / 1081407) ∧
    -Real.log (1000000 / 1081407) ≤ (19565743 / 250000000) := by
  have h := checkLog_sound (w := (81407 / 2081407)) (n := 12)
    (lo := (78262971 / 1000000000)) (hi := (19565743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081407 / 1000000) = 1/(1000000 / 1081407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1683 : Bounds (78262971 / 1000000000) (19565743 / 250000000) (Real.log (1081407 / 1000000)) := by
  have h := reflection_log_1683_neg
  have he : Real.log (1081407 / 1000000) = -Real.log (1000000 / 1081407) := by
    rw [show ((1081407 / 1000000) : ℝ) = ((1000000 / 1081407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1684_neg : (84912127 / 1000000000) ≤ -Real.log (918593 / 1000000) ∧
    -Real.log (918593 / 1000000) ≤ (165844 / 1953125) := by
  have h := checkLog_sound (w := (81407 / 1918593)) (n := 12)
    (lo := (84912127 / 1000000000)) (hi := (165844 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918593) = 1/(918593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1684 : Bounds (-165844 / 1953125) (-84912127 / 1000000000) (Real.log (918593 / 1000000)) := by
  have h := reflection_log_1684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1685_neg : (78459917 / 1000000000) ≤ -Real.log (50000 / 54081) ∧
    -Real.log (50000 / 54081) ≤ (39229959 / 500000000) := by
  have h := checkLog_sound (w := (4081 / 104081)) (n := 12)
    (lo := (78459917 / 1000000000)) (hi := (39229959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54081 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54081 / 50000) = 1/(50000 / 54081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1685 : Bounds (78459917 / 1000000000) (39229959 / 500000000) (Real.log (54081 / 50000)) := by
  have h := reflection_log_1685_neg
  have he : Real.log (54081 / 50000) = -Real.log (50000 / 54081) := by
    rw [show ((54081 / 50000) : ℝ) = ((50000 / 54081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1686_neg : (8514403 / 100000000) ≤ -Real.log (45919 / 50000) ∧
    -Real.log (45919 / 50000) ≤ (85144031 / 1000000000) := by
  have h := checkLog_sound (w := (4081 / 95919)) (n := 12)
    (lo := (8514403 / 100000000)) (hi := (85144031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45919) = 1/(45919 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1686 : Bounds (-85144031 / 1000000000) (-8514403 / 100000000) (Real.log (45919 / 50000)) := by
  have h := reflection_log_1686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1687_neg : (6684113 / 1000000000) ≤ -Real.log (2483345439 / 2500000000) ∧
    -Real.log (2483345439 / 2500000000) ≤ (3342057 / 500000000) := by
  have h := checkLog_sound (w := (16654561 / 4983345439)) (n := 12)
    (lo := (6684113 / 1000000000)) (hi := (3342057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483345439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483345439) = 1/(2483345439 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1687 : Bounds (-3342057 / 500000000) (-6684113 / 1000000000) (Real.log (2483345439 / 2500000000)) := by
  have h := reflection_log_1687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1688_neg : (1662289 / 250000000) ≤ -Real.log (993372900351 / 1000000000000) ∧
    -Real.log (993372900351 / 1000000000000) ≤ (6649157 / 1000000000) := by
  have h := checkLog_sound (w := (6627099649 / 1993372900351)) (n := 12)
    (lo := (1662289 / 250000000)) (hi := (6649157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993372900351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993372900351) = 1/(993372900351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1688 : Bounds (-6649157 / 1000000000) (-1662289 / 250000000) (Real.log (993372900351 / 1000000000000)) := by
  have h := reflection_log_1688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1689_neg : (81587549 / 500000000) ≤ -Real.log (250000000000 / 294310701257) ∧
    -Real.log (250000000000 / 294310701257) ≤ (163175099 / 1000000000) := by
  have h := checkLog_sound (w := (44310701257 / 544310701257)) (n := 12)
    (lo := (81587549 / 500000000)) (hi := (163175099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294310701257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294310701257 / 250000000000) = 1/(250000000000 / 294310701257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1689 : Bounds (81587549 / 500000000) (163175099 / 1000000000) (Real.log (294310701257 / 250000000000)) := by
  have h := reflection_log_1689_neg
  have he : Real.log (294310701257 / 250000000000) = -Real.log (250000000000 / 294310701257) := by
    rw [show ((294310701257 / 250000000000) : ℝ) = ((250000000000 / 294310701257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1690_neg : (163603947 / 1000000000) ≤ -Real.log (500000000000 / 588873886627) ∧
    -Real.log (500000000000 / 588873886627) ≤ (40900987 / 250000000) := by
  have h := checkLog_sound (w := (88873886627 / 1088873886627)) (n := 12)
    (lo := (163603947 / 1000000000)) (hi := (40900987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588873886627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588873886627 / 500000000000) = 1/(500000000000 / 588873886627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1690 : Bounds (163603947 / 1000000000) (40900987 / 250000000) (Real.log (588873886627 / 500000000000)) := by
  have h := reflection_log_1690_neg
  have he : Real.log (588873886627 / 500000000000) = -Real.log (500000000000 / 588873886627) := by
    rw [show ((588873886627 / 500000000000) : ℝ) = ((500000000000 / 588873886627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1691_neg : (327290631 / 1000000000) ≤ -Real.log (125000000000 / 173400572929) ∧
    -Real.log (125000000000 / 173400572929) ≤ (40911329 / 125000000) := by
  have h := checkLog_sound (w := (48400572929 / 298400572929)) (n := 12)
    (lo := (327290631 / 1000000000)) (hi := (40911329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173400572929 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173400572929 / 125000000000) = 1/(125000000000 / 173400572929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1691 : Bounds (327290631 / 1000000000) (40911329 / 125000000) (Real.log (173400572929 / 125000000000)) := by
  have h := reflection_log_1691_neg
  have he : Real.log (173400572929 / 125000000000) = -Real.log (125000000000 / 173400572929) := by
    rw [show ((173400572929 / 125000000000) : ℝ) = ((125000000000 / 173400572929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1692_neg : (163748019 / 500000000) ≤ -Real.log (500000000000 / 693744777367) ∧
    -Real.log (500000000000 / 693744777367) ≤ (327496039 / 1000000000) := by
  have h := checkLog_sound (w := (193744777367 / 1193744777367)) (n := 12)
    (lo := (163748019 / 500000000)) (hi := (327496039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693744777367 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693744777367 / 500000000000) = 1/(500000000000 / 693744777367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1692 : Bounds (163748019 / 500000000) (327496039 / 1000000000) (Real.log (693744777367 / 500000000000)) := by
  have h := reflection_log_1692_neg
  have he : Real.log (693744777367 / 500000000000) = -Real.log (500000000000 / 693744777367) := by
    rw [show ((693744777367 / 500000000000) : ℝ) = ((500000000000 / 693744777367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1693_neg : (150486833 / 1000000000) ≤ -Real.log (1250 / 1453) ∧
    -Real.log (1250 / 1453) ≤ (75243417 / 500000000) := by
  have h := checkLog_sound (w := (203 / 2703)) (n := 12)
    (lo := (150486833 / 1000000000)) (hi := (75243417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453 / 1250) = 1/(1250 / 1453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1693 : Bounds (150486833 / 1000000000) (75243417 / 500000000) (Real.log (1453 / 1250)) := by
  have h := reflection_log_1693_neg
  have he : Real.log (1453 / 1250) = -Real.log (1250 / 1453) := by
    rw [show ((1453 / 1250) : ℝ) = ((1250 / 1453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1694_neg : (177214619 / 1000000000) ≤ -Real.log (1047 / 1250) ∧
    -Real.log (1047 / 1250) ≤ (8860731 / 50000000) := by
  have h := checkLog_sound (w := (203 / 2297)) (n := 12)
    (lo := (177214619 / 1000000000)) (hi := (8860731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1047) = 1/(1047 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1694 : Bounds (-8860731 / 50000000) (-177214619 / 1000000000) (Real.log (1047 / 1250)) := by
  have h := reflection_log_1694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1695_neg : (81193 / 500000000) ≤ -Real.log (1250000 / 1250203) ∧
    -Real.log (1250000 / 1250203) ≤ (162387 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2500203)) (n := 12)
    (lo := (81193 / 500000000)) (hi := (162387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250203 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250203 / 1250000) = 1/(1250000 / 1250203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1695 : Bounds (81193 / 500000000) (162387 / 1000000000) (Real.log (1250203 / 1250000)) := by
  have h := reflection_log_1695_neg
  have he : Real.log (1250203 / 1250000) = -Real.log (1250000 / 1250203) := by
    rw [show ((1250203 / 1250000) : ℝ) = ((1250000 / 1250203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1696_neg : (162413 / 1000000000) ≤ -Real.log (1249797 / 1250000) ∧
    -Real.log (1249797 / 1250000) ≤ (81207 / 500000000) := by
  have h := checkLog_sound (w := (203 / 2499797)) (n := 12)
    (lo := (162413 / 1000000000)) (hi := (81207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249797) = 1/(1249797 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1696 : Bounds (-81207 / 500000000) (-162413 / 1000000000) (Real.log (1249797 / 1250000)) := by
  have h := reflection_log_1696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1697_neg : (39154603 / 500000000) ≤ -Real.log (1000000 / 1081457) ∧
    -Real.log (1000000 / 1081457) ≤ (78309207 / 1000000000) := by
  have h := checkLog_sound (w := (81457 / 2081457)) (n := 12)
    (lo := (39154603 / 500000000)) (hi := (78309207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081457 / 1000000) = 1/(1000000 / 1081457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1697 : Bounds (39154603 / 500000000) (78309207 / 1000000000) (Real.log (1081457 / 1000000)) := by
  have h := reflection_log_1697_neg
  have he : Real.log (1081457 / 1000000) = -Real.log (1000000 / 1081457) := by
    rw [show ((1081457 / 1000000) : ℝ) = ((1000000 / 1081457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1698_neg : (84966559 / 1000000000) ≤ -Real.log (918543 / 1000000) ∧
    -Real.log (918543 / 1000000) ≤ (531041 / 6250000) := by
  have h := checkLog_sound (w := (81457 / 1918543)) (n := 12)
    (lo := (84966559 / 1000000000)) (hi := (531041 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918543) = 1/(918543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1698 : Bounds (-531041 / 6250000) (-84966559 / 1000000000) (Real.log (918543 / 1000000)) := by
  have h := reflection_log_1698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1699_neg : (78507067 / 1000000000) ≤ -Real.log (1000000 / 1081671) ∧
    -Real.log (1000000 / 1081671) ≤ (19626767 / 250000000) := by
  have h := checkLog_sound (w := (81671 / 2081671)) (n := 12)
    (lo := (78507067 / 1000000000)) (hi := (19626767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081671 / 1000000) = 1/(1000000 / 1081671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1699 : Bounds (78507067 / 1000000000) (19626767 / 250000000) (Real.log (1081671 / 1000000)) := by
  have h := reflection_log_1699_neg
  have he : Real.log (1081671 / 1000000) = -Real.log (1000000 / 1081671) := by
    rw [show ((1081671 / 1000000) : ℝ) = ((1000000 / 1081671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1700_neg : (21299891 / 250000000) ≤ -Real.log (918329 / 1000000) ∧
    -Real.log (918329 / 1000000) ≤ (17039913 / 200000000) := by
  have h := checkLog_sound (w := (81671 / 1918329)) (n := 12)
    (lo := (21299891 / 250000000)) (hi := (17039913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918329) = 1/(918329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1700 : Bounds (-17039913 / 200000000) (-21299891 / 250000000) (Real.log (918329 / 1000000)) := by
  have h := reflection_log_1700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1701_neg : (6692497 / 1000000000) ≤ -Real.log (993329847759 / 1000000000000) ∧
    -Real.log (993329847759 / 1000000000000) ≤ (3346249 / 500000000) := by
  have h := checkLog_sound (w := (6670152241 / 1993329847759)) (n := 12)
    (lo := (6692497 / 1000000000)) (hi := (3346249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993329847759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993329847759) = 1/(993329847759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1701 : Bounds (-3346249 / 500000000) (-6692497 / 1000000000) (Real.log (993329847759 / 1000000000000)) := by
  have h := reflection_log_1701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1702_neg : (6657353 / 1000000000) ≤ -Real.log (993364757151 / 1000000000000) ∧
    -Real.log (993364757151 / 1000000000000) ≤ (3328677 / 500000000) := by
  have h := checkLog_sound (w := (6635242849 / 1993364757151)) (n := 12)
    (lo := (6657353 / 1000000000)) (hi := (3328677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993364757151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993364757151) = 1/(993364757151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1702 : Bounds (-3328677 / 500000000) (-6657353 / 1000000000) (Real.log (993364757151 / 1000000000000)) := by
  have h := reflection_log_1702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1703_neg : (32655153 / 200000000) ≤ -Real.log (500000000000 / 588680660567) ∧
    -Real.log (500000000000 / 588680660567) ≤ (81637883 / 500000000) := by
  have h := checkLog_sound (w := (88680660567 / 1088680660567)) (n := 12)
    (lo := (32655153 / 200000000)) (hi := (81637883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588680660567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588680660567 / 500000000000) = 1/(500000000000 / 588680660567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1703 : Bounds (32655153 / 200000000) (81637883 / 500000000) (Real.log (588680660567 / 500000000000)) := by
  have h := reflection_log_1703_neg
  have he : Real.log (588680660567 / 500000000000) = -Real.log (500000000000 / 588680660567) := by
    rw [show ((588680660567 / 500000000000) : ℝ) = ((500000000000 / 588680660567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1704_neg : (20463329 / 125000000) ≤ -Real.log (125000000000 / 147233589487) ∧
    -Real.log (125000000000 / 147233589487) ≤ (163706633 / 1000000000) := by
  have h := checkLog_sound (w := (22233589487 / 272233589487)) (n := 12)
    (lo := (20463329 / 125000000)) (hi := (163706633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147233589487 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147233589487 / 125000000000) = 1/(125000000000 / 147233589487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1704 : Bounds (20463329 / 125000000) (163706633 / 1000000000) (Real.log (147233589487 / 125000000000)) := by
  have h := reflection_log_1704_neg
  have he : Real.log (147233589487 / 125000000000) = -Real.log (125000000000 / 147233589487) := by
    rw [show ((147233589487 / 125000000000) : ℝ) = ((125000000000 / 147233589487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1705_neg : (163748019 / 500000000) ≤ -Real.log (250000000000 / 346872388683) ∧
    -Real.log (250000000000 / 346872388683) ≤ (327496039 / 1000000000) := by
  have h := checkLog_sound (w := (96872388683 / 596872388683)) (n := 12)
    (lo := (163748019 / 500000000)) (hi := (327496039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346872388683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346872388683 / 250000000000) = 1/(250000000000 / 346872388683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1705 : Bounds (163748019 / 500000000) (327496039 / 1000000000) (Real.log (346872388683 / 250000000000)) := by
  have h := reflection_log_1705_neg
  have he : Real.log (346872388683 / 250000000000) = -Real.log (250000000000 / 346872388683) := by
    rw [show ((346872388683 / 250000000000) : ℝ) = ((250000000000 / 346872388683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1706_neg : (81925363 / 250000000) ≤ -Real.log (6250000000 / 8673591213) ∧
    -Real.log (6250000000 / 8673591213) ≤ (327701453 / 1000000000) := by
  have h := checkLog_sound (w := (2423591213 / 14923591213)) (n := 12)
    (lo := (81925363 / 250000000)) (hi := (327701453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8673591213 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8673591213 / 6250000000) = 1/(6250000000 / 8673591213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1706 : Bounds (81925363 / 250000000) (327701453 / 1000000000) (Real.log (8673591213 / 6250000000)) := by
  have h := reflection_log_1706_neg
  have he : Real.log (8673591213 / 6250000000) = -Real.log (6250000000 / 8673591213) := by
    rw [show ((8673591213 / 6250000000) : ℝ) = ((6250000000 / 8673591213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1707_neg : (75286429 / 500000000) ≤ -Real.log (80 / 93) ∧
    -Real.log (80 / 93) ≤ (150572859 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 173)) (n := 12)
    (lo := (75286429 / 500000000)) (hi := (150572859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 80) = 1/(80 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1707 : Bounds (75286429 / 500000000) (150572859 / 1000000000) (Real.log (93 / 80)) := by
  have h := reflection_log_1707_neg
  have he : Real.log (93 / 80) = -Real.log (80 / 93) := by
    rw [show ((93 / 80) : ℝ) = ((80 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1708_neg : (35466803 / 200000000) ≤ -Real.log (67 / 80) ∧
    -Real.log (67 / 80) ≤ (692711 / 3906250) := by
  have h := checkLog_sound (w := (13 / 147)) (n := 12)
    (lo := (35466803 / 200000000)) (hi := (692711 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 67) = 1/(67 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1708 : Bounds (-692711 / 3906250) (-35466803 / 200000000) (Real.log (67 / 80)) := by
  have h := reflection_log_1708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1709_neg : (81243 / 500000000) ≤ -Real.log (80000 / 80013) ∧
    -Real.log (80000 / 80013) ≤ (162487 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 160013)) (n := 12)
    (lo := (81243 / 500000000)) (hi := (162487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80013 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80013 / 80000) = 1/(80000 / 80013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1709 : Bounds (81243 / 500000000) (162487 / 1000000000) (Real.log (80013 / 80000)) := by
  have h := reflection_log_1709_neg
  have he : Real.log (80013 / 80000) = -Real.log (80000 / 80013) := by
    rw [show ((80013 / 80000) : ℝ) = ((80000 / 80013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1710_neg : (162513 / 1000000000) ≤ -Real.log (79987 / 80000) ∧
    -Real.log (79987 / 80000) ≤ (81257 / 500000000) := by
  have h := checkLog_sound (w := (13 / 159987)) (n := 12)
    (lo := (162513 / 1000000000)) (hi := (81257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79987) = 1/(79987 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1710 : Bounds (-81257 / 500000000) (-162513 / 1000000000) (Real.log (79987 / 80000)) := by
  have h := reflection_log_1710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1711_neg : (78356363 / 1000000000) ≤ -Real.log (250000 / 270377) ∧
    -Real.log (250000 / 270377) ≤ (19589091 / 250000000) := by
  have h := checkLog_sound (w := (20377 / 520377)) (n := 12)
    (lo := (78356363 / 1000000000)) (hi := (19589091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270377 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270377 / 250000) = 1/(250000 / 270377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1711 : Bounds (78356363 / 1000000000) (19589091 / 250000000) (Real.log (270377 / 250000)) := by
  have h := reflection_log_1711_neg
  have he : Real.log (270377 / 250000) = -Real.log (250000 / 270377) := by
    rw [show ((270377 / 250000) : ℝ) = ((250000 / 270377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1712_neg : (21255521 / 250000000) ≤ -Real.log (229623 / 250000) ∧
    -Real.log (229623 / 250000) ≤ (17004417 / 200000000) := by
  have h := checkLog_sound (w := (20377 / 479623)) (n := 12)
    (lo := (21255521 / 250000000)) (hi := (17004417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229623) = 1/(229623 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1712 : Bounds (-17004417 / 200000000) (-21255521 / 250000000) (Real.log (229623 / 250000)) := by
  have h := reflection_log_1712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1713_neg : (78553291 / 1000000000) ≤ -Real.log (1000000 / 1081721) ∧
    -Real.log (1000000 / 1081721) ≤ (19638323 / 250000000) := by
  have h := checkLog_sound (w := (81721 / 2081721)) (n := 12)
    (lo := (78553291 / 1000000000)) (hi := (19638323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081721 / 1000000) = 1/(1000000 / 1081721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1713 : Bounds (78553291 / 1000000000) (19638323 / 250000000) (Real.log (1081721 / 1000000)) := by
  have h := reflection_log_1713_neg
  have he : Real.log (1081721 / 1000000) = -Real.log (1000000 / 1081721) := by
    rw [show ((1081721 / 1000000) : ℝ) = ((1000000 / 1081721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1714_neg : (21313503 / 250000000) ≤ -Real.log (918279 / 1000000) ∧
    -Real.log (918279 / 1000000) ≤ (85254013 / 1000000000) := by
  have h := checkLog_sound (w := (81721 / 1918279)) (n := 12)
    (lo := (21313503 / 250000000)) (hi := (85254013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918279) = 1/(918279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1714 : Bounds (-85254013 / 1000000000) (-21313503 / 250000000) (Real.log (918279 / 1000000)) := by
  have h := reflection_log_1714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1715_neg : (6700721 / 1000000000) ≤ -Real.log (993321678159 / 1000000000000) ∧
    -Real.log (993321678159 / 1000000000000) ≤ (3350361 / 500000000) := by
  have h := checkLog_sound (w := (6678321841 / 1993321678159)) (n := 12)
    (lo := (6700721 / 1000000000)) (hi := (3350361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993321678159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993321678159) = 1/(993321678159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1715 : Bounds (-3350361 / 500000000) (-6700721 / 1000000000) (Real.log (993321678159 / 1000000000000)) := by
  have h := reflection_log_1715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1716_neg : (166643 / 25000000) ≤ -Real.log (62084777871 / 62500000000) ∧
    -Real.log (62084777871 / 62500000000) ≤ (6665721 / 1000000000) := by
  have h := checkLog_sound (w := (415222129 / 124584777871)) (n := 12)
    (lo := (166643 / 25000000)) (hi := (6665721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62084777871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62084777871) = 1/(62084777871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1716 : Bounds (-6665721 / 1000000000) (-166643 / 25000000) (Real.log (62084777871 / 62500000000)) := by
  have h := reflection_log_1716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1717_neg : (163378447 / 1000000000) ≤ -Real.log (125000000000 / 147185277607) ∧
    -Real.log (125000000000 / 147185277607) ≤ (10211153 / 62500000) := by
  have h := checkLog_sound (w := (22185277607 / 272185277607)) (n := 12)
    (lo := (163378447 / 1000000000)) (hi := (10211153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147185277607 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147185277607 / 125000000000) = 1/(125000000000 / 147185277607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1717 : Bounds (163378447 / 1000000000) (10211153 / 62500000) (Real.log (147185277607 / 125000000000)) := by
  have h := reflection_log_1717_neg
  have he : Real.log (147185277607 / 125000000000) = -Real.log (125000000000 / 147185277607) := by
    rw [show ((147185277607 / 125000000000) : ℝ) = ((125000000000 / 147185277607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1718_neg : (20475913 / 125000000) ≤ -Real.log (500000000000 / 588993650079) ∧
    -Real.log (500000000000 / 588993650079) ≤ (32761461 / 200000000) := by
  have h := checkLog_sound (w := (88993650079 / 1088993650079)) (n := 12)
    (lo := (20475913 / 125000000)) (hi := (32761461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588993650079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588993650079 / 500000000000) = 1/(500000000000 / 588993650079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1718 : Bounds (20475913 / 125000000) (32761461 / 200000000) (Real.log (588993650079 / 500000000000)) := by
  have h := reflection_log_1718_neg
  have he : Real.log (588993650079 / 500000000000) = -Real.log (500000000000 / 588993650079) := by
    rw [show ((588993650079 / 500000000000) : ℝ) = ((500000000000 / 588993650079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1719_neg : (81925363 / 250000000) ≤ -Real.log (500000000000 / 693887297039) ∧
    -Real.log (500000000000 / 693887297039) ≤ (327701453 / 1000000000) := by
  have h := checkLog_sound (w := (193887297039 / 1193887297039)) (n := 12)
    (lo := (81925363 / 250000000)) (hi := (327701453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693887297039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693887297039 / 500000000000) = 1/(500000000000 / 693887297039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1719 : Bounds (81925363 / 250000000) (327701453 / 1000000000) (Real.log (693887297039 / 500000000000)) := by
  have h := reflection_log_1719_neg
  have he : Real.log (693887297039 / 500000000000) = -Real.log (500000000000 / 693887297039) := by
    rw [show ((693887297039 / 500000000000) : ℝ) = ((500000000000 / 693887297039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1720_neg : (327906873 / 1000000000) ≤ -Real.log (500000000000 / 694029850747) ∧
    -Real.log (500000000000 / 694029850747) ≤ (163953437 / 500000000) := by
  have h := checkLog_sound (w := (194029850747 / 1194029850747)) (n := 12)
    (lo := (327906873 / 1000000000)) (hi := (163953437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694029850747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694029850747 / 500000000000) = 1/(500000000000 / 694029850747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1720 : Bounds (327906873 / 1000000000) (163953437 / 500000000) (Real.log (694029850747 / 500000000000)) := by
  have h := reflection_log_1720_neg
  have he : Real.log (694029850747 / 500000000000) = -Real.log (500000000000 / 694029850747) := by
    rw [show ((694029850747 / 500000000000) : ℝ) = ((500000000000 / 694029850747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1721_neg : (37664719 / 250000000) ≤ -Real.log (5000 / 5813) ∧
    -Real.log (5000 / 5813) ≤ (150658877 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 10813)) (n := 12)
    (lo := (37664719 / 250000000)) (hi := (150658877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5813 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5813 / 5000) = 1/(5000 / 5813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1721 : Bounds (37664719 / 250000000) (150658877 / 1000000000) (Real.log (5813 / 5000)) := by
  have h := reflection_log_1721_neg
  have he : Real.log (5813 / 5000) = -Real.log (5000 / 5813) := by
    rw [show ((5813 / 5000) : ℝ) = ((5000 / 5813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1722_neg : (7098137 / 40000000) ≤ -Real.log (4187 / 5000) ∧
    -Real.log (4187 / 5000) ≤ (88726713 / 500000000) := by
  have h := checkLog_sound (w := (813 / 9187)) (n := 12)
    (lo := (7098137 / 40000000)) (hi := (88726713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4187) = 1/(4187 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1722 : Bounds (-88726713 / 500000000) (-7098137 / 40000000) (Real.log (4187 / 5000)) := by
  have h := reflection_log_1722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1723_neg : (81293 / 500000000) ≤ -Real.log (5000000 / 5000813) ∧
    -Real.log (5000000 / 5000813) ≤ (162587 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 10000813)) (n := 12)
    (lo := (81293 / 500000000)) (hi := (162587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000813 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000813 / 5000000) = 1/(5000000 / 5000813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1723 : Bounds (81293 / 500000000) (162587 / 1000000000) (Real.log (5000813 / 5000000)) := by
  have h := reflection_log_1723_neg
  have he : Real.log (5000813 / 5000000) = -Real.log (5000000 / 5000813) := by
    rw [show ((5000813 / 5000000) : ℝ) = ((5000000 / 5000813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1724_neg : (162613 / 1000000000) ≤ -Real.log (4999187 / 5000000) ∧
    -Real.log (4999187 / 5000000) ≤ (81307 / 500000000) := by
  have h := checkLog_sound (w := (813 / 9999187)) (n := 12)
    (lo := (162613 / 1000000000)) (hi := (81307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999187) = 1/(4999187 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1724 : Bounds (-81307 / 500000000) (-162613 / 1000000000) (Real.log (4999187 / 5000000)) := by
  have h := reflection_log_1724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1725_neg : (39201759 / 500000000) ≤ -Real.log (1000000 / 1081559) ∧
    -Real.log (1000000 / 1081559) ≤ (78403519 / 1000000000) := by
  have h := checkLog_sound (w := (81559 / 2081559)) (n := 12)
    (lo := (39201759 / 500000000)) (hi := (78403519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081559 / 1000000) = 1/(1000000 / 1081559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1725 : Bounds (39201759 / 500000000) (78403519 / 1000000000) (Real.log (1081559 / 1000000)) := by
  have h := reflection_log_1725_neg
  have he : Real.log (1081559 / 1000000) = -Real.log (1000000 / 1081559) := by
    rw [show ((1081559 / 1000000) : ℝ) = ((1000000 / 1081559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1726_neg : (85077611 / 1000000000) ≤ -Real.log (918441 / 1000000) ∧
    -Real.log (918441 / 1000000) ≤ (21269403 / 250000000) := by
  have h := checkLog_sound (w := (81559 / 1918441)) (n := 12)
    (lo := (85077611 / 1000000000)) (hi := (21269403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918441) = 1/(918441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1726 : Bounds (-21269403 / 250000000) (-85077611 / 1000000000) (Real.log (918441 / 1000000)) := by
  have h := reflection_log_1726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1727_neg : (78600437 / 1000000000) ≤ -Real.log (250000 / 270443) ∧
    -Real.log (250000 / 270443) ≤ (39300219 / 500000000) := by
  have h := checkLog_sound (w := (20443 / 520443)) (n := 12)
    (lo := (78600437 / 1000000000)) (hi := (39300219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270443 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270443 / 250000) = 1/(250000 / 270443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1727 : Bounds (78600437 / 1000000000) (39300219 / 500000000) (Real.log (270443 / 250000)) := by
  have h := reflection_log_1727_neg
  have he : Real.log (270443 / 250000) = -Real.log (250000 / 270443) := by
    rw [show ((270443 / 250000) : ℝ) = ((250000 / 270443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
