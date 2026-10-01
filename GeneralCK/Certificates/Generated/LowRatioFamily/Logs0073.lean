import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4672_neg : (92801129 / 250000000) ≤ -Real.log (125000000000 / 181184935701) ∧
    -Real.log (125000000000 / 181184935701) ≤ (371204517 / 1000000000) := by
  have h := checkLog_sound (w := (56184935701 / 306184935701)) (n := 12)
    (lo := (92801129 / 250000000)) (hi := (371204517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181184935701 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181184935701 / 125000000000) = 1/(125000000000 / 181184935701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4672 : Bounds (92801129 / 250000000) (371204517 / 1000000000) (Real.log (181184935701 / 125000000000)) := by
  have h := reflection_log_4672_neg
  have he : Real.log (181184935701 / 125000000000) = -Real.log (125000000000 / 181184935701) := by
    rw [show ((181184935701 / 125000000000) : ℝ) = ((125000000000 / 181184935701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4673_neg : (371411489 / 1000000000) ≤ -Real.log (250000000000 / 362444879961) ∧
    -Real.log (250000000000 / 362444879961) ≤ (37141149 / 100000000) := by
  have h := checkLog_sound (w := (112444879961 / 612444879961)) (n := 12)
    (lo := (371411489 / 1000000000)) (hi := (37141149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362444879961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362444879961 / 250000000000) = 1/(250000000000 / 362444879961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4673 : Bounds (371411489 / 1000000000) (37141149 / 100000000) (Real.log (362444879961 / 250000000000)) := by
  have h := reflection_log_4673_neg
  have he : Real.log (362444879961 / 250000000000) = -Real.log (250000000000 / 362444879961) := by
    rw [show ((362444879961 / 250000000000) : ℝ) = ((250000000000 / 362444879961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4674_neg : (1349161 / 8000000) ≤ -Real.log (10000 / 11837) ∧
    -Real.log (10000 / 11837) ≤ (84322563 / 500000000) := by
  have h := checkLog_sound (w := (1837 / 21837)) (n := 12)
    (lo := (1349161 / 8000000)) (hi := (84322563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11837 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11837 / 10000) = 1/(10000 / 11837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4674 : Bounds (1349161 / 8000000) (84322563 / 500000000) (Real.log (11837 / 10000)) := by
  have h := reflection_log_4674_neg
  have he : Real.log (11837 / 10000) = -Real.log (10000 / 11837) := by
    rw [show ((11837 / 10000) : ℝ) = ((10000 / 11837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4675_neg : (6342917 / 31250000) ≤ -Real.log (8163 / 10000) ∧
    -Real.log (8163 / 10000) ≤ (40594669 / 200000000) := by
  have h := checkLog_sound (w := (1837 / 18163)) (n := 12)
    (lo := (6342917 / 31250000)) (hi := (40594669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8163) = 1/(8163 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4675 : Bounds (-40594669 / 200000000) (-6342917 / 31250000) (Real.log (8163 / 10000)) := by
  have h := reflection_log_4675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4676_neg : (183683 / 1000000000) ≤ -Real.log (10000000 / 10001837) ∧
    -Real.log (10000000 / 10001837) ≤ (45921 / 250000000) := by
  have h := checkLog_sound (w := (1837 / 20001837)) (n := 12)
    (lo := (183683 / 1000000000)) (hi := (45921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001837 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001837 / 10000000) = 1/(10000000 / 10001837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4676 : Bounds (183683 / 1000000000) (45921 / 250000000) (Real.log (10001837 / 10000000)) := by
  have h := reflection_log_4676_neg
  have he : Real.log (10001837 / 10000000) = -Real.log (10000000 / 10001837) := by
    rw [show ((10001837 / 10000000) : ℝ) = ((10000000 / 10001837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4677_neg : (45929 / 250000000) ≤ -Real.log (9998163 / 10000000) ∧
    -Real.log (9998163 / 10000000) ≤ (183717 / 1000000000) := by
  have h := checkLog_sound (w := (1837 / 19998163)) (n := 12)
    (lo := (45929 / 250000000)) (hi := (183717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998163) = 1/(9998163 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4677 : Bounds (-183717 / 1000000000) (-45929 / 250000000) (Real.log (9998163 / 10000000)) := by
  have h := reflection_log_4677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4678_neg : (8825993 / 100000000) ≤ -Real.log (62500 / 68267) ∧
    -Real.log (62500 / 68267) ≤ (88259931 / 1000000000) := by
  have h := checkLog_sound (w := (5767 / 130767)) (n := 12)
    (lo := (8825993 / 100000000)) (hi := (88259931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68267 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68267 / 62500) = 1/(62500 / 68267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4678 : Bounds (8825993 / 100000000) (88259931 / 1000000000) (Real.log (68267 / 62500)) := by
  have h := reflection_log_4678_neg
  have he : Real.log (68267 / 62500) = -Real.log (62500 / 68267) := by
    rw [show ((68267 / 62500) : ℝ) = ((62500 / 68267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4679_neg : (12101313 / 125000000) ≤ -Real.log (56733 / 62500) ∧
    -Real.log (56733 / 62500) ≤ (19362101 / 200000000) := by
  have h := checkLog_sound (w := (5767 / 119233)) (n := 12)
    (lo := (12101313 / 125000000)) (hi := (19362101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56733) = 1/(56733 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4679 : Bounds (-19362101 / 200000000) (-12101313 / 125000000) (Real.log (56733 / 62500)) := by
  have h := reflection_log_4679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4680_neg : (88474139 / 1000000000) ≤ -Real.log (500000 / 546253) ∧
    -Real.log (500000 / 546253) ≤ (4423707 / 50000000) := by
  have h := checkLog_sound (w := (46253 / 1046253)) (n := 12)
    (lo := (88474139 / 1000000000)) (hi := (4423707 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546253 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546253 / 500000) = 1/(500000 / 546253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4680 : Bounds (88474139 / 1000000000) (4423707 / 50000000) (Real.log (546253 / 500000)) := by
  have h := reflection_log_4680_neg
  have he : Real.log (546253 / 500000) = -Real.log (500000 / 546253) := by
    rw [show ((546253 / 500000) : ℝ) = ((500000 / 546253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4681_neg : (24267081 / 250000000) ≤ -Real.log (453747 / 500000) ∧
    -Real.log (453747 / 500000) ≤ (3882733 / 40000000) := by
  have h := checkLog_sound (w := (46253 / 953747)) (n := 12)
    (lo := (24267081 / 250000000)) (hi := (3882733 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453747) = 1/(453747 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4681 : Bounds (-3882733 / 40000000) (-24267081 / 250000000) (Real.log (453747 / 500000)) := by
  have h := reflection_log_4681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4682_neg : (1074273 / 125000000) ≤ -Real.log (247860659991 / 250000000000) ∧
    -Real.log (247860659991 / 250000000000) ≤ (1718837 / 200000000) := by
  have h := checkLog_sound (w := (2139340009 / 497860659991)) (n := 12)
    (lo := (1074273 / 125000000)) (hi := (1718837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247860659991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247860659991) = 1/(247860659991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4682 : Bounds (-1718837 / 200000000) (-1074273 / 125000000) (Real.log (247860659991 / 250000000000)) := by
  have h := reflection_log_4682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4683_neg : (4275287 / 500000000) ≤ -Real.log (3872991711 / 3906250000) ∧
    -Real.log (3872991711 / 3906250000) ≤ (342023 / 40000000) := by
  have h := checkLog_sound (w := (33258289 / 7779241711)) (n := 12)
    (lo := (4275287 / 500000000)) (hi := (342023 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3872991711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3872991711) = 1/(3872991711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4683 : Bounds (-342023 / 40000000) (-4275287 / 500000000) (Real.log (3872991711 / 3906250000)) := by
  have h := reflection_log_4683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4684_neg : (37014087 / 200000000) ≤ -Real.log (62500000000 / 75206449509) ∧
    -Real.log (62500000000 / 75206449509) ≤ (46267609 / 250000000) := by
  have h := checkLog_sound (w := (12706449509 / 137706449509)) (n := 12)
    (lo := (37014087 / 200000000)) (hi := (46267609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75206449509 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75206449509 / 62500000000) = 1/(62500000000 / 75206449509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4684 : Bounds (37014087 / 200000000) (46267609 / 250000000) (Real.log (75206449509 / 62500000000)) := by
  have h := reflection_log_4684_neg
  have he : Real.log (75206449509 / 62500000000) = -Real.log (62500000000 / 75206449509) := by
    rw [show ((75206449509 / 62500000000) : ℝ) = ((62500000000 / 75206449509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4685_neg : (2899101 / 15625000) ≤ -Real.log (500000000000 / 601935660181) ∧
    -Real.log (500000000000 / 601935660181) ≤ (37108493 / 200000000) := by
  have h := checkLog_sound (w := (101935660181 / 1101935660181)) (n := 12)
    (lo := (2899101 / 15625000)) (hi := (37108493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601935660181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601935660181 / 500000000000) = 1/(500000000000 / 601935660181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4685 : Bounds (2899101 / 15625000) (37108493 / 200000000) (Real.log (601935660181 / 500000000000)) := by
  have h := reflection_log_4685_neg
  have he : Real.log (601935660181 / 500000000000) = -Real.log (500000000000 / 601935660181) := by
    rw [show ((601935660181 / 500000000000) : ℝ) = ((500000000000 / 601935660181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4686_neg : (371411489 / 1000000000) ≤ -Real.log (500000000000 / 724889759921) ∧
    -Real.log (500000000000 / 724889759921) ≤ (37141149 / 100000000) := by
  have h := checkLog_sound (w := (224889759921 / 1224889759921)) (n := 12)
    (lo := (371411489 / 1000000000)) (hi := (37141149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724889759921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724889759921 / 500000000000) = 1/(500000000000 / 724889759921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4686 : Bounds (371411489 / 1000000000) (37141149 / 100000000) (Real.log (724889759921 / 500000000000)) := by
  have h := reflection_log_4686_neg
  have he : Real.log (724889759921 / 500000000000) = -Real.log (500000000000 / 724889759921) := by
    rw [show ((724889759921 / 500000000000) : ℝ) = ((500000000000 / 724889759921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4687_neg : (37161847 / 100000000) ≤ -Real.log (250000000000 / 362519906897) ∧
    -Real.log (250000000000 / 362519906897) ≤ (371618471 / 1000000000) := by
  have h := checkLog_sound (w := (112519906897 / 612519906897)) (n := 12)
    (lo := (37161847 / 100000000)) (hi := (371618471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362519906897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362519906897 / 250000000000) = 1/(250000000000 / 362519906897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4687 : Bounds (37161847 / 100000000) (371618471 / 1000000000) (Real.log (362519906897 / 250000000000)) := by
  have h := reflection_log_4687_neg
  have he : Real.log (362519906897 / 250000000000) = -Real.log (250000000000 / 362519906897) := by
    rw [show ((362519906897 / 250000000000) : ℝ) = ((250000000000 / 362519906897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4688_neg : (168729603 / 1000000000) ≤ -Real.log (5000 / 5919) ∧
    -Real.log (5000 / 5919) ≤ (42182401 / 250000000) := by
  have h := checkLog_sound (w := (919 / 10919)) (n := 12)
    (lo := (168729603 / 1000000000)) (hi := (42182401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5919 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5919 / 5000) = 1/(5000 / 5919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4688 : Bounds (168729603 / 1000000000) (42182401 / 250000000) (Real.log (5919 / 5000)) := by
  have h := reflection_log_4688_neg
  have he : Real.log (5919 / 5000) = -Real.log (5000 / 5919) := by
    rw [show ((5919 / 5000) : ℝ) = ((5000 / 5919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4689_neg : (12693491 / 62500000) ≤ -Real.log (4081 / 5000) ∧
    -Real.log (4081 / 5000) ≤ (203095857 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 9081)) (n := 12)
    (lo := (12693491 / 62500000)) (hi := (203095857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4081) = 1/(4081 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4689 : Bounds (-203095857 / 1000000000) (-12693491 / 62500000) (Real.log (4081 / 5000)) := by
  have h := reflection_log_4689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4690_neg : (183783 / 1000000000) ≤ -Real.log (5000000 / 5000919) ∧
    -Real.log (5000000 / 5000919) ≤ (22973 / 125000000) := by
  have h := checkLog_sound (w := (919 / 10000919)) (n := 12)
    (lo := (183783 / 1000000000)) (hi := (22973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000919 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000919 / 5000000) = 1/(5000000 / 5000919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4690 : Bounds (183783 / 1000000000) (22973 / 125000000) (Real.log (5000919 / 5000000)) := by
  have h := reflection_log_4690_neg
  have he : Real.log (5000919 / 5000000) = -Real.log (5000000 / 5000919) := by
    rw [show ((5000919 / 5000000) : ℝ) = ((5000000 / 5000919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4691_neg : (22977 / 125000000) ≤ -Real.log (4999081 / 5000000) ∧
    -Real.log (4999081 / 5000000) ≤ (183817 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 9999081)) (n := 12)
    (lo := (22977 / 125000000)) (hi := (183817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999081) = 1/(4999081 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4691 : Bounds (-183817 / 1000000000) (-22977 / 125000000) (Real.log (4999081 / 5000000)) := by
  have h := reflection_log_4691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4692_neg : (88306621 / 1000000000) ≤ -Real.log (1000000 / 1092323) ∧
    -Real.log (1000000 / 1092323) ≤ (44153311 / 500000000) := by
  have h := checkLog_sound (w := (92323 / 2092323)) (n := 12)
    (lo := (88306621 / 1000000000)) (hi := (44153311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092323 / 1000000) = 1/(1000000 / 1092323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4692 : Bounds (88306621 / 1000000000) (44153311 / 500000000) (Real.log (1092323 / 1000000)) := by
  have h := reflection_log_4692_neg
  have he : Real.log (1092323 / 1000000) = -Real.log (1000000 / 1092323) := by
    rw [show ((1092323 / 1000000) : ℝ) = ((1000000 / 1092323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4693_neg : (9686669 / 100000000) ≤ -Real.log (907677 / 1000000) ∧
    -Real.log (907677 / 1000000) ≤ (96866691 / 1000000000) := by
  have h := checkLog_sound (w := (92323 / 1907677)) (n := 12)
    (lo := (9686669 / 100000000)) (hi := (96866691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907677) = 1/(907677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4693 : Bounds (-96866691 / 1000000000) (-9686669 / 100000000) (Real.log (907677 / 1000000)) := by
  have h := reflection_log_4693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4694_neg : (4426041 / 50000000) ≤ -Real.log (1000000 / 1092557) ∧
    -Real.log (1000000 / 1092557) ≤ (88520821 / 1000000000) := by
  have h := checkLog_sound (w := (92557 / 2092557)) (n := 12)
    (lo := (4426041 / 50000000)) (hi := (88520821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092557 / 1000000) = 1/(1000000 / 1092557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4694 : Bounds (4426041 / 50000000) (88520821 / 1000000000) (Real.log (1092557 / 1000000)) := by
  have h := reflection_log_4694_neg
  have he : Real.log (1092557 / 1000000) = -Real.log (1000000 / 1092557) := by
    rw [show ((1092557 / 1000000) : ℝ) = ((1000000 / 1092557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4695_neg : (24281131 / 250000000) ≤ -Real.log (907443 / 1000000) ∧
    -Real.log (907443 / 1000000) ≤ (3884981 / 40000000) := by
  have h := checkLog_sound (w := (92557 / 1907443)) (n := 12)
    (lo := (24281131 / 250000000)) (hi := (3884981 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907443) = 1/(907443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4695 : Bounds (-3884981 / 40000000) (-24281131 / 250000000) (Real.log (907443 / 1000000)) := by
  have h := reflection_log_4695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4696_neg : (1075463 / 125000000) ≤ -Real.log (991433201751 / 1000000000000) ∧
    -Real.log (991433201751 / 1000000000000) ≤ (1720741 / 200000000) := by
  have h := checkLog_sound (w := (8566798249 / 1991433201751)) (n := 12)
    (lo := (1075463 / 125000000)) (hi := (1720741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991433201751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991433201751) = 1/(991433201751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4696 : Bounds (-1720741 / 200000000) (-1075463 / 125000000) (Real.log (991433201751 / 1000000000000)) := by
  have h := reflection_log_4696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4697_neg : (8560069 / 1000000000) ≤ -Real.log (991476463671 / 1000000000000) ∧
    -Real.log (991476463671 / 1000000000000) ≤ (856007 / 100000000) := by
  have h := checkLog_sound (w := (8523536329 / 1991476463671)) (n := 12)
    (lo := (8560069 / 1000000000)) (hi := (856007 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991476463671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991476463671) = 1/(991476463671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4697 : Bounds (-856007 / 100000000) (-8560069 / 1000000000) (Real.log (991476463671 / 1000000000000)) := by
  have h := reflection_log_4697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4698_neg : (185173311 / 1000000000) ≤ -Real.log (250000000000 / 300856747499) ∧
    -Real.log (250000000000 / 300856747499) ≤ (2893333 / 15625000) := by
  have h := checkLog_sound (w := (50856747499 / 550856747499)) (n := 12)
    (lo := (185173311 / 1000000000)) (hi := (2893333 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300856747499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300856747499 / 250000000000) = 1/(250000000000 / 300856747499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4698 : Bounds (185173311 / 1000000000) (2893333 / 15625000) (Real.log (300856747499 / 250000000000)) := by
  have h := reflection_log_4698_neg
  have he : Real.log (300856747499 / 250000000000) = -Real.log (250000000000 / 300856747499) := by
    rw [show ((300856747499 / 250000000000) : ℝ) = ((250000000000 / 300856747499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4699_neg : (37129069 / 200000000) ≤ -Real.log (250000000000 / 300998795517) ∧
    -Real.log (250000000000 / 300998795517) ≤ (92822673 / 500000000) := by
  have h := checkLog_sound (w := (50998795517 / 550998795517)) (n := 12)
    (lo := (37129069 / 200000000)) (hi := (92822673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300998795517 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300998795517 / 250000000000) = 1/(250000000000 / 300998795517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4699 : Bounds (37129069 / 200000000) (92822673 / 500000000) (Real.log (300998795517 / 250000000000)) := by
  have h := reflection_log_4699_neg
  have he : Real.log (300998795517 / 250000000000) = -Real.log (250000000000 / 300998795517) := by
    rw [show ((300998795517 / 250000000000) : ℝ) = ((250000000000 / 300998795517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4700_neg : (37161847 / 100000000) ≤ -Real.log (500000000000 / 725039813793) ∧
    -Real.log (500000000000 / 725039813793) ≤ (371618471 / 1000000000) := by
  have h := checkLog_sound (w := (225039813793 / 1225039813793)) (n := 12)
    (lo := (37161847 / 100000000)) (hi := (371618471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725039813793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725039813793 / 500000000000) = 1/(500000000000 / 725039813793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4700 : Bounds (37161847 / 100000000) (371618471 / 1000000000) (Real.log (725039813793 / 500000000000)) := by
  have h := reflection_log_4700_neg
  have he : Real.log (725039813793 / 500000000000) = -Real.log (500000000000 / 725039813793) := by
    rw [show ((725039813793 / 500000000000) : ℝ) = ((500000000000 / 725039813793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4701_neg : (371825459 / 1000000000) ≤ -Real.log (125000000000 / 181297476109) ∧
    -Real.log (125000000000 / 181297476109) ≤ (18591273 / 50000000) := by
  have h := checkLog_sound (w := (56297476109 / 306297476109)) (n := 12)
    (lo := (371825459 / 1000000000)) (hi := (18591273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181297476109 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181297476109 / 125000000000) = 1/(125000000000 / 181297476109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4701 : Bounds (371825459 / 1000000000) (18591273 / 50000000) (Real.log (181297476109 / 125000000000)) := by
  have h := reflection_log_4701_neg
  have he : Real.log (181297476109 / 125000000000) = -Real.log (125000000000 / 181297476109) := by
    rw [show ((181297476109 / 125000000000) : ℝ) = ((125000000000 / 181297476109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4702_neg : (168814073 / 1000000000) ≤ -Real.log (10000 / 11839) ∧
    -Real.log (10000 / 11839) ≤ (84407037 / 500000000) := by
  have h := checkLog_sound (w := (1839 / 21839)) (n := 12)
    (lo := (168814073 / 1000000000)) (hi := (84407037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11839 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11839 / 10000) = 1/(10000 / 11839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4702 : Bounds (168814073 / 1000000000) (84407037 / 500000000) (Real.log (11839 / 10000)) := by
  have h := reflection_log_4702_neg
  have he : Real.log (11839 / 10000) = -Real.log (10000 / 11839) := by
    rw [show ((11839 / 10000) : ℝ) = ((10000 / 11839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4703_neg : (101609191 / 500000000) ≤ -Real.log (8161 / 10000) ∧
    -Real.log (8161 / 10000) ≤ (203218383 / 1000000000) := by
  have h := checkLog_sound (w := (1839 / 18161)) (n := 12)
    (lo := (101609191 / 500000000)) (hi := (203218383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8161) = 1/(8161 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4703 : Bounds (-203218383 / 1000000000) (-101609191 / 500000000) (Real.log (8161 / 10000)) := by
  have h := reflection_log_4703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4704_neg : (183883 / 1000000000) ≤ -Real.log (10000000 / 10001839) ∧
    -Real.log (10000000 / 10001839) ≤ (45971 / 250000000) := by
  have h := checkLog_sound (w := (1839 / 20001839)) (n := 12)
    (lo := (183883 / 1000000000)) (hi := (45971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001839 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001839 / 10000000) = 1/(10000000 / 10001839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4704 : Bounds (183883 / 1000000000) (45971 / 250000000) (Real.log (10001839 / 10000000)) := by
  have h := reflection_log_4704_neg
  have he : Real.log (10001839 / 10000000) = -Real.log (10000000 / 10001839) := by
    rw [show ((10001839 / 10000000) : ℝ) = ((10000000 / 10001839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4705_neg : (45979 / 250000000) ≤ -Real.log (9998161 / 10000000) ∧
    -Real.log (9998161 / 10000000) ≤ (183917 / 1000000000) := by
  have h := checkLog_sound (w := (1839 / 19998161)) (n := 12)
    (lo := (45979 / 250000000)) (hi := (183917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998161) = 1/(9998161 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4705 : Bounds (-183917 / 1000000000) (-45979 / 250000000) (Real.log (9998161 / 10000000)) := by
  have h := reflection_log_4705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4706_neg : (88353309 / 1000000000) ≤ -Real.log (500000 / 546187) ∧
    -Real.log (500000 / 546187) ≤ (8835331 / 100000000) := by
  have h := checkLog_sound (w := (46187 / 1046187)) (n := 12)
    (lo := (88353309 / 1000000000)) (hi := (8835331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546187 / 500000) = 1/(500000 / 546187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4706 : Bounds (88353309 / 1000000000) (8835331 / 100000000) (Real.log (546187 / 500000)) := by
  have h := reflection_log_4706_neg
  have he : Real.log (546187 / 500000) = -Real.log (500000 / 546187) := by
    rw [show ((546187 / 500000) : ℝ) = ((500000 / 546187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4707_neg : (96922879 / 1000000000) ≤ -Real.log (453813 / 500000) ∧
    -Real.log (453813 / 500000) ≤ (75721 / 781250) := by
  have h := checkLog_sound (w := (46187 / 953813)) (n := 12)
    (lo := (96922879 / 1000000000)) (hi := (75721 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453813) = 1/(453813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4707 : Bounds (-75721 / 781250) (-96922879 / 1000000000) (Real.log (453813 / 500000)) := by
  have h := reflection_log_4707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4708_neg : (44283749 / 500000000) ≤ -Real.log (15625 / 17072) ∧
    -Real.log (15625 / 17072) ≤ (88567499 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 32697)) (n := 12)
    (lo := (44283749 / 500000000)) (hi := (88567499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17072 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17072 / 15625) = 1/(15625 / 17072) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4708 : Bounds (44283749 / 500000000) (88567499 / 1000000000) (Real.log (17072 / 15625)) := by
  have h := reflection_log_4708_neg
  have he : Real.log (17072 / 15625) = -Real.log (15625 / 17072) := by
    rw [show ((17072 / 15625) : ℝ) = ((15625 / 17072) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4709_neg : (12147591 / 125000000) ≤ -Real.log (14178 / 15625) ∧
    -Real.log (14178 / 15625) ≤ (97180729 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 29803)) (n := 12)
    (lo := (12147591 / 125000000)) (hi := (97180729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14178) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14178) = 1/(14178 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4709 : Bounds (-97180729 / 1000000000) (-12147591 / 125000000) (Real.log (14178 / 15625)) := by
  have h := reflection_log_4709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4710_neg : (8613229 / 1000000000) ≤ -Real.log (242046816 / 244140625) ∧
    -Real.log (242046816 / 244140625) ≤ (861323 / 100000000) := by
  have h := checkLog_sound (w := (2093809 / 486187441)) (n := 12)
    (lo := (8613229 / 1000000000)) (hi := (861323 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242046816) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242046816) = 1/(242046816 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4710 : Bounds (-861323 / 100000000) (-8613229 / 1000000000) (Real.log (242046816 / 244140625)) := by
  have h := reflection_log_4710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4711_neg : (8569569 / 1000000000) ≤ -Real.log (247866761031 / 250000000000) ∧
    -Real.log (247866761031 / 250000000000) ≤ (856957 / 100000000) := by
  have h := checkLog_sound (w := (2133238969 / 497866761031)) (n := 12)
    (lo := (8569569 / 1000000000)) (hi := (856957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247866761031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247866761031) = 1/(247866761031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4711 : Bounds (-856957 / 100000000) (-8569569 / 1000000000) (Real.log (247866761031 / 250000000000)) := by
  have h := reflection_log_4711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4712_neg : (185276189 / 1000000000) ≤ -Real.log (6250000000 / 7522192511) ∧
    -Real.log (6250000000 / 7522192511) ≤ (18527619 / 100000000) := by
  have h := checkLog_sound (w := (1272192511 / 13772192511)) (n := 12)
    (lo := (185276189 / 1000000000)) (hi := (18527619 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7522192511 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7522192511 / 6250000000) = 1/(6250000000 / 7522192511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4712 : Bounds (185276189 / 1000000000) (18527619 / 100000000) (Real.log (7522192511 / 6250000000)) := by
  have h := reflection_log_4712_neg
  have he : Real.log (7522192511 / 6250000000) = -Real.log (6250000000 / 7522192511) := by
    rw [show ((7522192511 / 6250000000) : ℝ) = ((6250000000 / 7522192511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4713_neg : (185748227 / 1000000000) ≤ -Real.log (31250000000 / 37628720553) ∧
    -Real.log (31250000000 / 37628720553) ≤ (46437057 / 250000000) := by
  have h := checkLog_sound (w := (6378720553 / 68878720553)) (n := 12)
    (lo := (185748227 / 1000000000)) (hi := (46437057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37628720553 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37628720553 / 31250000000) = 1/(31250000000 / 37628720553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4713 : Bounds (185748227 / 1000000000) (46437057 / 250000000) (Real.log (37628720553 / 31250000000)) := by
  have h := reflection_log_4713_neg
  have he : Real.log (37628720553 / 31250000000) = -Real.log (31250000000 / 37628720553) := by
    rw [show ((37628720553 / 31250000000) : ℝ) = ((31250000000 / 37628720553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4714_neg : (371825459 / 1000000000) ≤ -Real.log (100000000000 / 145037980887) ∧
    -Real.log (100000000000 / 145037980887) ≤ (18591273 / 50000000) := by
  have h := checkLog_sound (w := (45037980887 / 245037980887)) (n := 12)
    (lo := (371825459 / 1000000000)) (hi := (18591273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145037980887 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145037980887 / 100000000000) = 1/(100000000000 / 145037980887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4714 : Bounds (371825459 / 1000000000) (18591273 / 50000000) (Real.log (145037980887 / 100000000000)) := by
  have h := reflection_log_4714_neg
  have he : Real.log (145037980887 / 100000000000) = -Real.log (100000000000 / 145037980887) := by
    rw [show ((145037980887 / 100000000000) : ℝ) = ((100000000000 / 145037980887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4715_neg : (74406491 / 200000000) ≤ -Real.log (500000000000 / 725340031859) ∧
    -Real.log (500000000000 / 725340031859) ≤ (46504057 / 125000000) := by
  have h := checkLog_sound (w := (225340031859 / 1225340031859)) (n := 12)
    (lo := (74406491 / 200000000)) (hi := (46504057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725340031859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725340031859 / 500000000000) = 1/(500000000000 / 725340031859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4715 : Bounds (74406491 / 200000000) (46504057 / 125000000) (Real.log (725340031859 / 500000000000)) := by
  have h := reflection_log_4715_neg
  have he : Real.log (725340031859 / 500000000000) = -Real.log (500000000000 / 725340031859) := by
    rw [show ((725340031859 / 500000000000) : ℝ) = ((500000000000 / 725340031859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4716_neg : (21112317 / 125000000) ≤ -Real.log (125 / 148) ∧
    -Real.log (125 / 148) ≤ (168898537 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 273)) (n := 12)
    (lo := (21112317 / 125000000)) (hi := (168898537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148 / 125) = 1/(125 / 148) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4716 : Bounds (21112317 / 125000000) (168898537 / 1000000000) (Real.log (148 / 125)) := by
  have h := reflection_log_4716_neg
  have he : Real.log (148 / 125) = -Real.log (125 / 148) := by
    rw [show ((148 / 125) : ℝ) = ((125 / 148) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4717_neg : (50835231 / 250000000) ≤ -Real.log (102 / 125) ∧
    -Real.log (102 / 125) ≤ (8133637 / 40000000) := by
  have h := checkLog_sound (w := (23 / 227)) (n := 12)
    (lo := (50835231 / 250000000)) (hi := (8133637 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 102) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 102) = 1/(102 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4717 : Bounds (-8133637 / 40000000) (-50835231 / 250000000) (Real.log (102 / 125)) := by
  have h := reflection_log_4717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4718_neg : (183983 / 1000000000) ≤ -Real.log (125000 / 125023) ∧
    -Real.log (125000 / 125023) ≤ (11499 / 62500000) := by
  have h := checkLog_sound (w := (23 / 250023)) (n := 12)
    (lo := (183983 / 1000000000)) (hi := (11499 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125023 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125023 / 125000) = 1/(125000 / 125023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4718 : Bounds (183983 / 1000000000) (11499 / 62500000) (Real.log (125023 / 125000)) := by
  have h := reflection_log_4718_neg
  have he : Real.log (125023 / 125000) = -Real.log (125000 / 125023) := by
    rw [show ((125023 / 125000) : ℝ) = ((125000 / 125023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4719_neg : (11501 / 62500000) ≤ -Real.log (124977 / 125000) ∧
    -Real.log (124977 / 125000) ≤ (184017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 249977)) (n := 12)
    (lo := (11501 / 62500000)) (hi := (184017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124977) = 1/(124977 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4719 : Bounds (-184017 / 1000000000) (-11501 / 62500000) (Real.log (124977 / 125000)) := by
  have h := reflection_log_4719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4720_neg : (17679999 / 200000000) ≤ -Real.log (40000 / 43697) ∧
    -Real.log (40000 / 43697) ≤ (22099999 / 250000000) := by
  have h := checkLog_sound (w := (3697 / 83697)) (n := 12)
    (lo := (17679999 / 200000000)) (hi := (22099999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43697 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43697 / 40000) = 1/(40000 / 43697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4720 : Bounds (17679999 / 200000000) (22099999 / 250000000) (Real.log (43697 / 40000)) := by
  have h := reflection_log_4720_neg
  have he : Real.log (43697 / 40000) = -Real.log (40000 / 43697) := by
    rw [show ((43697 / 40000) : ℝ) = ((40000 / 43697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4721_neg : (96979071 / 1000000000) ≤ -Real.log (36303 / 40000) ∧
    -Real.log (36303 / 40000) ≤ (757649 / 7812500) := by
  have h := checkLog_sound (w := (3697 / 76303)) (n := 12)
    (lo := (96979071 / 1000000000)) (hi := (757649 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36303) = 1/(36303 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4721 : Bounds (-757649 / 7812500) (-96979071 / 1000000000) (Real.log (36303 / 40000)) := by
  have h := reflection_log_4721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4722_neg : (3544567 / 40000000) ≤ -Real.log (1000000 / 1092659) ∧
    -Real.log (1000000 / 1092659) ≤ (2769193 / 31250000) := by
  have h := checkLog_sound (w := (92659 / 2092659)) (n := 12)
    (lo := (3544567 / 40000000)) (hi := (2769193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092659 / 1000000) = 1/(1000000 / 1092659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4722 : Bounds (3544567 / 40000000) (2769193 / 31250000) (Real.log (1092659 / 1000000)) := by
  have h := reflection_log_4722_neg
  have he : Real.log (1092659 / 1000000) = -Real.log (1000000 / 1092659) := by
    rw [show ((1092659 / 1000000) : ℝ) = ((1000000 / 1092659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4723_neg : (48618467 / 500000000) ≤ -Real.log (907341 / 1000000) ∧
    -Real.log (907341 / 1000000) ≤ (19447387 / 200000000) := by
  have h := checkLog_sound (w := (92659 / 1907341)) (n := 12)
    (lo := (48618467 / 500000000)) (hi := (19447387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907341) = 1/(907341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4723 : Bounds (-19447387 / 200000000) (-48618467 / 500000000) (Real.log (907341 / 1000000)) := by
  have h := reflection_log_4723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4724_neg : (8622759 / 1000000000) ≤ -Real.log (991414309719 / 1000000000000) ∧
    -Real.log (991414309719 / 1000000000000) ≤ (215569 / 25000000) := by
  have h := checkLog_sound (w := (8585690281 / 1991414309719)) (n := 12)
    (lo := (8622759 / 1000000000)) (hi := (215569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991414309719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991414309719) = 1/(991414309719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4724 : Bounds (-215569 / 25000000) (-8622759 / 1000000000) (Real.log (991414309719 / 1000000000000)) := by
  have h := reflection_log_4724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4725_neg : (343163 / 40000000) ≤ -Real.log (1586332191 / 1600000000) ∧
    -Real.log (1586332191 / 1600000000) ≤ (2144769 / 250000000) := by
  have h := checkLog_sound (w := (13667809 / 3186332191)) (n := 12)
    (lo := (343163 / 40000000)) (hi := (2144769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586332191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586332191) = 1/(1586332191 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4725 : Bounds (-2144769 / 250000000) (-343163 / 40000000) (Real.log (1586332191 / 1600000000)) := by
  have h := reflection_log_4725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4726_neg : (185379067 / 1000000000) ≤ -Real.log (12500000000 / 15045932843) ∧
    -Real.log (12500000000 / 15045932843) ≤ (46344767 / 250000000) := by
  have h := checkLog_sound (w := (2545932843 / 27545932843)) (n := 12)
    (lo := (185379067 / 1000000000)) (hi := (46344767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15045932843 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15045932843 / 12500000000) = 1/(12500000000 / 15045932843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4726 : Bounds (185379067 / 1000000000) (46344767 / 250000000) (Real.log (15045932843 / 12500000000)) := by
  have h := reflection_log_4726_neg
  have he : Real.log (15045932843 / 12500000000) = -Real.log (12500000000 / 15045932843) := by
    rw [show ((15045932843 / 12500000000) : ℝ) = ((12500000000 / 15045932843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4727_neg : (185851109 / 1000000000) ≤ -Real.log (4000000000 / 4816971789) ∧
    -Real.log (4000000000 / 4816971789) ≤ (18585111 / 100000000) := by
  have h := checkLog_sound (w := (816971789 / 8816971789)) (n := 12)
    (lo := (185851109 / 1000000000)) (hi := (18585111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4816971789 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4816971789 / 4000000000) = 1/(4000000000 / 4816971789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4727 : Bounds (185851109 / 1000000000) (18585111 / 100000000) (Real.log (4816971789 / 4000000000)) := by
  have h := reflection_log_4727_neg
  have he : Real.log (4816971789 / 4000000000) = -Real.log (4000000000 / 4816971789) := by
    rw [show ((4816971789 / 4000000000) : ℝ) = ((4000000000 / 4816971789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4728_neg : (74406491 / 200000000) ≤ -Real.log (250000000000 / 362670015929) ∧
    -Real.log (250000000000 / 362670015929) ≤ (46504057 / 125000000) := by
  have h := checkLog_sound (w := (112670015929 / 612670015929)) (n := 12)
    (lo := (74406491 / 200000000)) (hi := (46504057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362670015929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362670015929 / 250000000000) = 1/(250000000000 / 362670015929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4728 : Bounds (74406491 / 200000000) (46504057 / 125000000) (Real.log (362670015929 / 250000000000)) := by
  have h := reflection_log_4728_neg
  have he : Real.log (362670015929 / 250000000000) = -Real.log (250000000000 / 362670015929) := by
    rw [show ((362670015929 / 250000000000) : ℝ) = ((250000000000 / 362670015929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4729_neg : (18611973 / 50000000) ≤ -Real.log (500000000000 / 725490196079) ∧
    -Real.log (500000000000 / 725490196079) ≤ (372239461 / 1000000000) := by
  have h := checkLog_sound (w := (225490196079 / 1225490196079)) (n := 12)
    (lo := (18611973 / 50000000)) (hi := (372239461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725490196079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725490196079 / 500000000000) = 1/(500000000000 / 725490196079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4729 : Bounds (18611973 / 50000000) (372239461 / 1000000000) (Real.log (725490196079 / 500000000000)) := by
  have h := reflection_log_4729_neg
  have he : Real.log (725490196079 / 500000000000) = -Real.log (500000000000 / 725490196079) := by
    rw [show ((725490196079 / 500000000000) : ℝ) = ((500000000000 / 725490196079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4730_neg : (10561437 / 62500000) ≤ -Real.log (10000 / 11841) ∧
    -Real.log (10000 / 11841) ≤ (168982993 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 21841)) (n := 12)
    (lo := (10561437 / 62500000)) (hi := (168982993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 10000) = 1/(10000 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4730 : Bounds (10561437 / 62500000) (168982993 / 1000000000) (Real.log (11841 / 10000)) := by
  have h := reflection_log_4730_neg
  have he : Real.log (11841 / 10000) = -Real.log (10000 / 11841) := by
    rw [show ((11841 / 10000) : ℝ) = ((10000 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4731_neg : (5086587 / 25000000) ≤ -Real.log (8159 / 10000) ∧
    -Real.log (8159 / 10000) ≤ (203463481 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 18159)) (n := 12)
    (lo := (5086587 / 25000000)) (hi := (203463481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8159) = 1/(8159 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4731 : Bounds (-203463481 / 1000000000) (-5086587 / 25000000) (Real.log (8159 / 10000)) := by
  have h := reflection_log_4731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4732_neg : (184083 / 1000000000) ≤ -Real.log (10000000 / 10001841) ∧
    -Real.log (10000000 / 10001841) ≤ (46021 / 250000000) := by
  have h := checkLog_sound (w := (1841 / 20001841)) (n := 12)
    (lo := (184083 / 1000000000)) (hi := (46021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001841 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001841 / 10000000) = 1/(10000000 / 10001841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4732 : Bounds (184083 / 1000000000) (46021 / 250000000) (Real.log (10001841 / 10000000)) := by
  have h := reflection_log_4732_neg
  have he : Real.log (10001841 / 10000000) = -Real.log (10000000 / 10001841) := by
    rw [show ((10001841 / 10000000) : ℝ) = ((10000000 / 10001841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4733_neg : (46029 / 250000000) ≤ -Real.log (9998159 / 10000000) ∧
    -Real.log (9998159 / 10000000) ≤ (184117 / 1000000000) := by
  have h := checkLog_sound (w := (1841 / 19998159)) (n := 12)
    (lo := (46029 / 250000000)) (hi := (184117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998159) = 1/(9998159 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4733 : Bounds (-184117 / 1000000000) (-46029 / 250000000) (Real.log (9998159 / 10000000)) := by
  have h := reflection_log_4733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4734_neg : (22111441 / 250000000) ≤ -Real.log (40000 / 43699) ∧
    -Real.log (40000 / 43699) ≤ (17689153 / 200000000) := by
  have h := checkLog_sound (w := (3699 / 83699)) (n := 12)
    (lo := (22111441 / 250000000)) (hi := (17689153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43699 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43699 / 40000) = 1/(40000 / 43699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4734 : Bounds (22111441 / 250000000) (17689153 / 200000000) (Real.log (43699 / 40000)) := by
  have h := reflection_log_4734_neg
  have he : Real.log (43699 / 40000) = -Real.log (40000 / 43699) := by
    rw [show ((43699 / 40000) : ℝ) = ((40000 / 43699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4735_neg : (19406833 / 200000000) ≤ -Real.log (36301 / 40000) ∧
    -Real.log (36301 / 40000) ≤ (48517083 / 500000000) := by
  have h := checkLog_sound (w := (3699 / 76301)) (n := 12)
    (lo := (19406833 / 200000000)) (hi := (48517083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36301) = 1/(36301 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4735 : Bounds (-48517083 / 500000000) (-19406833 / 200000000) (Real.log (36301 / 40000)) := by
  have h := reflection_log_4735_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
