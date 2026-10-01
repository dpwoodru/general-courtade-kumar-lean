import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell250
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

theorem reflection_log_1_neg : (33437741 / 100000000) ≤ -Real.log (5120 / 7153) ∧
    -Real.log (5120 / 7153) ≤ (334377411 / 1000000000) := by
  have h := checkLog_sound (w := (2033 / 12273)) (n := 12)
    (lo := (33437741 / 100000000)) (hi := (334377411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7153 / 5120) = 1/(5120 / 7153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33437741 / 100000000) (334377411 / 1000000000) (Real.log (7153 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7153 / 5120) = -Real.log (5120 / 7153) := by
    rw [show ((7153 / 5120) : ℝ) = ((5120 / 7153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (505954693 / 1000000000) ≤ -Real.log (3087 / 5120) ∧
    -Real.log (3087 / 5120) ≤ (252977347 / 500000000) := by
  have h := checkLog_sound (w := (2033 / 8207)) (n := 12)
    (lo := (505954693 / 1000000000)) (hi := (252977347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3087) = 1/(3087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252977347 / 500000000) (-505954693 / 1000000000) (Real.log (3087 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (333957917 / 1000000000) ≤ -Real.log (512 / 715) ∧
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


theorem reflection_log_3 : Bounds (333957917 / 1000000000) (166978959 / 500000000) (Real.log (715 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (715 / 512) = -Real.log (512 / 715) := by
    rw [show ((715 / 512) : ℝ) = ((512 / 715) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126245837 / 250000000) ≤ -Real.log (309 / 512) ∧
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


theorem reflection_log_4 : Bounds (-504983349 / 1000000000) (-126245837 / 250000000) (Real.log (309 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62168319 / 250000000) ≤ -Real.log (1000000 / 1282323) ∧
    -Real.log (1000000 / 1282323) ≤ (248673277 / 1000000000) := by
  have h := checkLog_sound (w := (282323 / 2282323)) (n := 12)
    (lo := (62168319 / 250000000)) (hi := (248673277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282323 / 1000000) = 1/(1000000 / 1282323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62168319 / 250000000) (248673277 / 1000000000) (Real.log (1282323 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1282323 / 1000000) = -Real.log (1000000 / 1282323) := by
    rw [show ((1282323 / 1000000) : ℝ) = ((1000000 / 1282323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331735671 / 1000000000) ≤ -Real.log (717677 / 1000000) ∧
    -Real.log (717677 / 1000000) ≤ (41466959 / 125000000) := by
  have h := checkLog_sound (w := (282323 / 1717677)) (n := 12)
    (lo := (331735671 / 1000000000)) (hi := (41466959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717677) = 1/(717677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41466959 / 125000000) (-331735671 / 1000000000) (Real.log (717677 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (249004651 / 1000000000) ≤ -Real.log (250000 / 320687) ∧
    -Real.log (250000 / 320687) ≤ (62251163 / 250000000) := by
  have h := checkLog_sound (w := (70687 / 570687)) (n := 12)
    (lo := (249004651 / 1000000000)) (hi := (62251163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320687 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320687 / 250000) = 1/(250000 / 320687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (249004651 / 1000000000) (62251163 / 250000000) (Real.log (320687 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (320687 / 250000) = -Real.log (250000 / 320687) := by
    rw [show ((320687 / 250000) : ℝ) = ((250000 / 320687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66465607 / 200000000) ≤ -Real.log (179313 / 250000) ∧
    -Real.log (179313 / 250000) ≤ (83082009 / 250000000) := by
  have h := checkLog_sound (w := (70687 / 429313)) (n := 12)
    (lo := (66465607 / 200000000)) (hi := (83082009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 179313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 179313) = 1/(179313 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83082009 / 250000000) (-66465607 / 200000000) (Real.log (179313 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (46441197 / 250000000) ≤ -Real.log (1000000 / 1204139) ∧
    -Real.log (1000000 / 1204139) ≤ (185764789 / 1000000000) := by
  have h := checkLog_sound (w := (204139 / 2204139)) (n := 12)
    (lo := (46441197 / 250000000)) (hi := (185764789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204139 / 1000000) = 1/(1000000 / 1204139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (46441197 / 250000000) (185764789 / 1000000000) (Real.log (1204139 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204139 / 1000000) = -Real.log (1000000 / 1204139) := by
    rw [show ((1204139 / 1000000) : ℝ) = ((1000000 / 1204139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (228330731 / 1000000000) ≤ -Real.log (795861 / 1000000) ∧
    -Real.log (795861 / 1000000) ≤ (57082683 / 250000000) := by
  have h := checkLog_sound (w := (204139 / 1795861)) (n := 12)
    (lo := (228330731 / 1000000000)) (hi := (57082683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795861) = 1/(795861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-57082683 / 250000000) (-228330731 / 1000000000) (Real.log (795861 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186031333 / 1000000000) ≤ -Real.log (50000 / 60223) ∧
    -Real.log (50000 / 60223) ≤ (93015667 / 500000000) := by
  have h := checkLog_sound (w := (10223 / 110223)) (n := 12)
    (lo := (186031333 / 1000000000)) (hi := (93015667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60223 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60223 / 50000) = 1/(50000 / 60223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186031333 / 1000000000) (93015667 / 500000000) (Real.log (60223 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60223 / 50000) = -Real.log (50000 / 60223) := by
    rw [show ((60223 / 50000) : ℝ) = ((50000 / 60223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (228734149 / 1000000000) ≤ -Real.log (39777 / 50000) ∧
    -Real.log (39777 / 50000) ≤ (4574683 / 20000000) := by
  have h := checkLog_sound (w := (10223 / 89777)) (n := 12)
    (lo := (228734149 / 1000000000)) (hi := (4574683 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39777) = 1/(39777 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4574683 / 20000000) (-228734149 / 1000000000) (Real.log (39777 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167788253 / 200000000) ≤ -Real.log (250000000000 / 578478964401) ∧
    -Real.log (250000000000 / 578478964401) ≤ (838941267 / 1000000000) := by
  have h := checkLog_sound (w := (78478964401 / 1078478964401)) (n := 12)
    (lo := (29158817 / 200000000)) (hi := (72897043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578478964401 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578478964401 / 500000000000) = 1/(250000000000 / 578478964401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167788253 / 200000000) (838941267 / 1000000000) (Real.log (578478964401 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (578478964401 / 250000000000) = -Real.log (250000000000 / 578478964401) := by
    rw [show ((578478964401 / 250000000000) : ℝ) = ((250000000000 / 578478964401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (840332103 / 1000000000) ≤ -Real.log (500000000000 / 1158568189181) ∧
    -Real.log (500000000000 / 1158568189181) ≤ (168066421 / 200000000) := by
  have h := checkLog_sound (w := (158568189181 / 2158568189181)) (n := 12)
    (lo := (147184923 / 1000000000)) (hi := (36796231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158568189181 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158568189181 / 1000000000000) = 1/(500000000000 / 1158568189181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (840332103 / 1000000000) (168066421 / 200000000) (Real.log (1158568189181 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1158568189181 / 500000000000) = -Real.log (500000000000 / 1158568189181) := by
    rw [show ((1158568189181 / 500000000000) : ℝ) = ((500000000000 / 1158568189181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (145102237 / 250000000) ≤ -Real.log (250000000000 / 446692244561) ∧
    -Real.log (250000000000 / 446692244561) ≤ (580408949 / 1000000000) := by
  have h := checkLog_sound (w := (196692244561 / 696692244561)) (n := 12)
    (lo := (145102237 / 250000000)) (hi := (580408949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((446692244561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(446692244561 / 250000000000) = 1/(250000000000 / 446692244561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (145102237 / 250000000) (580408949 / 1000000000) (Real.log (446692244561 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (446692244561 / 250000000000) = -Real.log (250000000000 / 446692244561) := by
    rw [show ((446692244561 / 250000000000) : ℝ) = ((250000000000 / 446692244561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (581332687 / 1000000000) ≤ -Real.log (500000000000 / 894210124197) ∧
    -Real.log (500000000000 / 894210124197) ≤ (36333293 / 62500000) := by
  have h := checkLog_sound (w := (394210124197 / 1394210124197)) (n := 12)
    (lo := (581332687 / 1000000000)) (hi := (36333293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894210124197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894210124197 / 500000000000) = 1/(500000000000 / 894210124197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (581332687 / 1000000000) (36333293 / 62500000) (Real.log (894210124197 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (894210124197 / 500000000000) = -Real.log (500000000000 / 894210124197) := by
    rw [show ((894210124197 / 500000000000) : ℝ) = ((500000000000 / 894210124197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2588097 / 6250000) ≤ -Real.log (500000000000 / 756500821123) ∧
    -Real.log (500000000000 / 756500821123) ≤ (414095521 / 1000000000) := by
  have h := checkLog_sound (w := (256500821123 / 1256500821123)) (n := 12)
    (lo := (2588097 / 6250000)) (hi := (414095521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756500821123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756500821123 / 500000000000) = 1/(500000000000 / 756500821123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2588097 / 6250000) (414095521 / 1000000000) (Real.log (756500821123 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (756500821123 / 500000000000) = -Real.log (500000000000 / 756500821123) := by
    rw [show ((756500821123 / 500000000000) : ℝ) = ((500000000000 / 756500821123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (414765483 / 1000000000) ≤ -Real.log (500000000000 / 757007818589) ∧
    -Real.log (500000000000 / 757007818589) ≤ (103691371 / 250000000) := by
  have h := checkLog_sound (w := (257007818589 / 1257007818589)) (n := 12)
    (lo := (414765483 / 1000000000)) (hi := (103691371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757007818589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757007818589 / 500000000000) = 1/(500000000000 / 757007818589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (414765483 / 1000000000) (103691371 / 250000000) (Real.log (757007818589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (757007818589 / 500000000000) = -Real.log (500000000000 / 757007818589) := by
    rw [show ((757007818589 / 500000000000) : ℝ) = ((500000000000 / 757007818589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8540563 / 200000000) ≤ -Real.log (2395490271 / 2500000000) ∧
    -Real.log (2395490271 / 2500000000) ≤ (1334463 / 31250000) := by
  have h := checkLog_sound (w := (104509729 / 4895490271)) (n := 12)
    (lo := (8540563 / 200000000)) (hi := (1334463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395490271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395490271) = 1/(2395490271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1334463 / 31250000) (-8540563 / 200000000) (Real.log (2395490271 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21282971 / 500000000) ≤ -Real.log (958327268679 / 1000000000000) ∧
    -Real.log (958327268679 / 1000000000000) ≤ (42565943 / 1000000000) := by
  have h := checkLog_sound (w := (41672731321 / 1958327268679)) (n := 12)
    (lo := (21282971 / 500000000)) (hi := (42565943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958327268679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958327268679) = 1/(958327268679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-42565943 / 1000000000) (-21282971 / 500000000) (Real.log (958327268679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell250
