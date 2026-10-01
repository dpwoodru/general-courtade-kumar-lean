import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0009
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (204811559 / 500000000) ≤ -Real.log (160 / 241) ∧
    -Real.log (160 / 241) ≤ (409623119 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 401)) (n := 12)
    (lo := (204811559 / 500000000)) (hi := (409623119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 160) = 1/(160 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204811559 / 500000000) (409623119 / 1000000000) (Real.log (241 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (241 / 160) = -Real.log (160 / 241) := by
    rw [show ((241 / 160) : ℝ) = ((160 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352862981 / 500000000) ≤ -Real.log (79 / 160) ∧
    -Real.log (79 / 160) ≤ (176431491 / 250000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 79) = 1/(79 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176431491 / 250000000) (-352862981 / 500000000) (Real.log (79 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
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


theorem reflection_log_4 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12422519 / 1000000000) ≤ -Real.log (80 / 81) ∧
    -Real.log (80 / 81) ≤ (310563 / 25000000) := by
  have h := checkLog_sound (w := (1 / 161)) (n := 12)
    (lo := (12422519 / 1000000000)) (hi := (310563 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 80) = 1/(80 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12422519 / 1000000000) (310563 / 25000000) (Real.log (81 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (81 / 80) = -Real.log (80 / 81) := by
    rw [show ((81 / 80) : ℝ) = ((80 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6289391 / 500000000) ≤ -Real.log (79 / 80) ∧
    -Real.log (79 / 80) ≤ (12578783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 79) = 1/(79 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12578783 / 1000000000) (-6289391 / 500000000) (Real.log (79 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7 : Bounds 0 0 (Real.log 1) := by norm_num [Bounds]

theorem reflection_log_8_neg : (576581903 / 1000000000) ≤ -Real.log (125000 / 222493) ∧
    -Real.log (125000 / 222493) ≤ (36036369 / 62500000) := by
  have h := checkLog_sound (w := (97493 / 347493)) (n := 12)
    (lo := (576581903 / 1000000000)) (hi := (36036369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222493 / 125000) = 1/(125000 / 222493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (576581903 / 1000000000) (36036369 / 62500000) (Real.log (222493 / 125000)) := by
  have h := reflection_log_8_neg
  have he : Real.log (222493 / 125000) = -Real.log (125000 / 222493) := by
    rw [show ((222493 / 125000) : ℝ) = ((125000 / 222493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9_neg : (756936609 / 500000000) ≤ -Real.log (27507 / 125000) ∧
    -Real.log (27507 / 125000) ≤ (1513873221 / 1000000000) := by
  have h := checkLog_sound (w := (3743 / 58757)) (n := 12)
    (lo := (63789429 / 500000000)) (hi := (127578859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27507) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 27507) = 1/(27507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (-1513873221 / 1000000000) (-756936609 / 500000000) (Real.log (27507 / 125000)) := by
  have h := reflection_log_9_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10_neg : (576603251 / 1000000000) ≤ -Real.log (500000 / 889991) ∧
    -Real.log (500000 / 889991) ≤ (144150813 / 250000000) := by
  have h := checkLog_sound (w := (389991 / 1389991)) (n := 12)
    (lo := (576603251 / 1000000000)) (hi := (144150813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889991 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889991 / 500000) = 1/(500000 / 889991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (576603251 / 1000000000) (144150813 / 250000000) (Real.log (889991 / 500000)) := by
  have h := reflection_log_10_neg
  have he : Real.log (889991 / 500000) = -Real.log (500000 / 889991) := by
    rw [show ((889991 / 500000) : ℝ) = ((500000 / 889991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11_neg : (378511479 / 250000000) ≤ -Real.log (110009 / 500000) ∧
    -Real.log (110009 / 500000) ≤ (1514045919 / 1000000000) := by
  have h := checkLog_sound (w := (14991 / 235009)) (n := 12)
    (lo := (31937889 / 250000000)) (hi := (127751557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110009) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 110009) = 1/(110009 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (-1514045919 / 1000000000) (-378511479 / 250000000) (Real.log (110009 / 500000)) := by
  have h := reflection_log_11_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12_neg : (50617161 / 100000000) ≤ -Real.log (62500 / 103683) ∧
    -Real.log (62500 / 103683) ≤ (506171611 / 1000000000) := by
  have h := checkLog_sound (w := (41183 / 166183)) (n := 12)
    (lo := (50617161 / 100000000)) (hi := (506171611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103683 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103683 / 62500) = 1/(62500 / 103683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (50617161 / 100000000) (506171611 / 1000000000) (Real.log (103683 / 62500)) := by
  have h := reflection_log_12_neg
  have he : Real.log (103683 / 62500) = -Real.log (62500 / 103683) := by
    rw [show ((103683 / 62500) : ℝ) = ((62500 / 103683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13_neg : (1075661679 / 1000000000) ≤ -Real.log (21317 / 62500) ∧
    -Real.log (21317 / 62500) ≤ (1075661681 / 1000000000) := by
  have h := checkLog_sound (w := (9933 / 52567)) (n := 12)
    (lo := (382514499 / 1000000000)) (hi := (765029 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 21317) = 1/(21317 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (-1075661681 / 1000000000) (-1075661679 / 1000000000) (Real.log (21317 / 62500)) := by
  have h := reflection_log_13_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14_neg : (254244247 / 500000000) ≤ -Real.log (125000 / 207847) ∧
    -Real.log (125000 / 207847) ≤ (101697699 / 200000000) := by
  have h := checkLog_sound (w := (82847 / 332847)) (n := 12)
    (lo := (254244247 / 500000000)) (hi := (101697699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207847 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207847 / 125000) = 1/(125000 / 207847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (254244247 / 500000000) (101697699 / 200000000) (Real.log (207847 / 125000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (207847 / 125000) = -Real.log (125000 / 207847) := by
    rw [show ((207847 / 125000) : ℝ) = ((125000 / 207847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (27175197 / 25000000) ≤ -Real.log (42153 / 125000) ∧
    -Real.log (42153 / 125000) ≤ (543503941 / 500000000) := by
  have h := checkLog_sound (w := (20347 / 104653)) (n := 12)
    (lo := (3938607 / 10000000)) (hi := (393860701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 42153) = 1/(42153 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (-543503941 / 500000000) (-27175197 / 25000000) (Real.log (42153 / 125000)) := by
  have h := reflection_log_15_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_16_neg : (2090455121 / 1000000000) ≤ -Real.log (500000000000 / 4044297815101) ∧
    -Real.log (500000000000 / 4044297815101) ≤ (16723641 / 8000000) := by
  have h := checkLog_sound (w := (44297815101 / 8044297815101)) (n := 12)
    (lo := (11013581 / 1000000000)) (hi := (5506791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4044297815101 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4044297815101 / 4000000000000) = 1/(500000000000 / 4044297815101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (2090455121 / 1000000000) (16723641 / 8000000) (Real.log (4044297815101 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4044297815101 / 500000000000) = -Real.log (500000000000 / 4044297815101) := by
    rw [show ((4044297815101 / 500000000000) : ℝ) = ((500000000000 / 4044297815101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (130665573 / 62500000) ≤ -Real.log (250000000000 / 2022541337527) ∧
    -Real.log (250000000000 / 2022541337527) ≤ (522662293 / 250000000) := by
  have h := checkLog_sound (w := (22541337527 / 4022541337527)) (n := 12)
    (lo := (2801907 / 250000000)) (hi := (11207629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2022541337527 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2022541337527 / 2000000000000) = 1/(250000000000 / 2022541337527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (130665573 / 62500000) (522662293 / 250000000) (Real.log (2022541337527 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2022541337527 / 250000000000) = -Real.log (250000000000 / 2022541337527) := by
    rw [show ((2022541337527 / 250000000000) : ℝ) = ((250000000000 / 2022541337527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1581833289 / 1000000000) ≤ -Real.log (500000000000 / 2431932260637) ∧
    -Real.log (500000000000 / 2431932260637) ≤ (395458323 / 250000000) := by
  have h := checkLog_sound (w := (431932260637 / 4431932260637)) (n := 12)
    (lo := (195538929 / 1000000000)) (hi := (19553893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431932260637 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2431932260637 / 2000000000000) = 1/(500000000000 / 2431932260637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1581833289 / 1000000000) (395458323 / 250000000) (Real.log (2431932260637 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2431932260637 / 500000000000) = -Real.log (500000000000 / 2431932260637) := by
    rw [show ((2431932260637 / 500000000000) : ℝ) = ((500000000000 / 2431932260637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (797748187 / 500000000) ≤ -Real.log (100000000000 / 493077598273) ∧
    -Real.log (100000000000 / 493077598273) ≤ (1595496377 / 1000000000) := by
  have h := checkLog_sound (w := (93077598273 / 893077598273)) (n := 12)
    (lo := (104601007 / 500000000)) (hi := (41840403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493077598273 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(493077598273 / 400000000000) = 1/(100000000000 / 493077598273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (797748187 / 500000000) (1595496377 / 1000000000) (Real.log (493077598273 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (493077598273 / 100000000000) = -Real.log (100000000000 / 493077598273) := by
    rw [show ((493077598273 / 100000000000) : ℝ) = ((100000000000 / 493077598273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0009
