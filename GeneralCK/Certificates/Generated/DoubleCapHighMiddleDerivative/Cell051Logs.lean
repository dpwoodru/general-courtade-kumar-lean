import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell051
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

theorem reflection_log_1_neg : (247226221 / 1000000000) ≤ -Real.log (1280 / 1639) ∧
    -Real.log (1280 / 1639) ≤ (123613111 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2919)) (n := 12)
    (lo := (247226221 / 1000000000)) (hi := (123613111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639 / 1280) = 1/(1280 / 1639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247226221 / 1000000000) (123613111 / 500000000) (Real.log (1639 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1639 / 1280) = -Real.log (1280 / 1639) := by
    rw [show ((1639 / 1280) : ℝ) = ((1280 / 1639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8228883 / 25000000) ≤ -Real.log (921 / 1280) ∧
    -Real.log (921 / 1280) ≤ (329155321 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 921) = 1/(921 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-329155321 / 1000000000) (-8228883 / 25000000) (Real.log (921 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246768521 / 1000000000) ≤ -Real.log (5120 / 6553) ∧
    -Real.log (5120 / 6553) ≤ (123384261 / 500000000) := by
  have h := checkLog_sound (w := (1433 / 11673)) (n := 12)
    (lo := (246768521 / 1000000000)) (hi := (123384261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6553 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6553 / 5120) = 1/(5120 / 6553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246768521 / 1000000000) (123384261 / 500000000) (Real.log (6553 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6553 / 5120) = -Real.log (5120 / 6553) := by
    rw [show ((6553 / 5120) : ℝ) = ((5120 / 6553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328341319 / 1000000000) ≤ -Real.log (3687 / 5120) ∧
    -Real.log (3687 / 5120) ≤ (8208533 / 25000000) := by
  have h := checkLog_sound (w := (1433 / 8807)) (n := 12)
    (lo := (328341319 / 1000000000)) (hi := (8208533 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3687) = 1/(3687 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8208533 / 25000000) (-328341319 / 1000000000) (Real.log (3687 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45283129 / 250000000) ≤ -Real.log (500000 / 599287) ∧
    -Real.log (500000 / 599287) ≤ (181132517 / 1000000000) := by
  have h := checkLog_sound (w := (99287 / 1099287)) (n := 12)
    (lo := (45283129 / 250000000)) (hi := (181132517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599287 / 500000) = 1/(500000 / 599287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45283129 / 250000000) (181132517 / 1000000000) (Real.log (599287 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (599287 / 500000) = -Real.log (500000 / 599287) := by
    rw [show ((599287 / 500000) : ℝ) = ((500000 / 599287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110681319 / 500000000) ≤ -Real.log (400713 / 500000) ∧
    -Real.log (400713 / 500000) ≤ (221362639 / 1000000000) := by
  have h := checkLog_sound (w := (99287 / 900713)) (n := 12)
    (lo := (110681319 / 500000000)) (hi := (221362639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400713) = 1/(400713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-221362639 / 1000000000) (-110681319 / 500000000) (Real.log (400713 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181482871 / 1000000000) ≤ -Real.log (500000 / 599497) ∧
    -Real.log (500000 / 599497) ≤ (22685359 / 125000000) := by
  have h := checkLog_sound (w := (99497 / 1099497)) (n := 12)
    (lo := (181482871 / 1000000000)) (hi := (22685359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599497 / 500000) = 1/(500000 / 599497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181482871 / 1000000000) (22685359 / 125000000) (Real.log (599497 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (599497 / 500000) = -Real.log (500000 / 599497) := by
    rw [show ((599497 / 500000) : ℝ) = ((500000 / 599497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (221886841 / 1000000000) ≤ -Real.log (400503 / 500000) ∧
    -Real.log (400503 / 500000) ≤ (110943421 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 900503)) (n := 12)
    (lo := (221886841 / 1000000000)) (hi := (110943421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400503) = 1/(400503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110943421 / 500000000) (-221886841 / 1000000000) (Real.log (400503 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66375231 / 500000000) ≤ -Real.log (200000 / 228393) ∧
    -Real.log (200000 / 228393) ≤ (132750463 / 1000000000) := by
  have h := checkLog_sound (w := (28393 / 428393)) (n := 12)
    (lo := (66375231 / 500000000)) (hi := (132750463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228393 / 200000) = 1/(200000 / 228393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66375231 / 500000000) (132750463 / 1000000000) (Real.log (228393 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (228393 / 200000) = -Real.log (200000 / 228393) := by
    rw [show ((228393 / 200000) : ℝ) = ((200000 / 228393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (153110387 / 1000000000) ≤ -Real.log (171607 / 200000) ∧
    -Real.log (171607 / 200000) ≤ (38277597 / 250000000) := by
  have h := checkLog_sound (w := (28393 / 371607)) (n := 12)
    (lo := (153110387 / 1000000000)) (hi := (38277597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171607) = 1/(171607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38277597 / 250000000) (-153110387 / 1000000000) (Real.log (171607 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66509193 / 500000000) ≤ -Real.log (1000000 / 1142271) ∧
    -Real.log (1000000 / 1142271) ≤ (133018387 / 1000000000) := by
  have h := checkLog_sound (w := (142271 / 2142271)) (n := 12)
    (lo := (66509193 / 500000000)) (hi := (133018387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142271 / 1000000) = 1/(1000000 / 1142271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66509193 / 500000000) (133018387 / 1000000000) (Real.log (1142271 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142271 / 1000000) = -Real.log (1000000 / 1142271) := by
    rw [show ((1142271 / 1000000) : ℝ) = ((1000000 / 1142271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3836677 / 25000000) ≤ -Real.log (857729 / 1000000) ∧
    -Real.log (857729 / 1000000) ≤ (153467081 / 1000000000) := by
  have h := checkLog_sound (w := (142271 / 1857729)) (n := 12)
    (lo := (3836677 / 25000000)) (hi := (153467081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857729) = 1/(857729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-153467081 / 1000000000) (-3836677 / 25000000) (Real.log (857729 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7188873 / 12500000) ≤ -Real.log (500000000000 / 888662869541) ∧
    -Real.log (500000000000 / 888662869541) ≤ (575109841 / 1000000000) := by
  have h := checkLog_sound (w := (388662869541 / 1388662869541)) (n := 12)
    (lo := (7188873 / 12500000)) (hi := (575109841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((888662869541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(888662869541 / 500000000000) = 1/(500000000000 / 888662869541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7188873 / 12500000) (575109841 / 1000000000) (Real.log (888662869541 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (888662869541 / 500000000000) = -Real.log (500000000000 / 888662869541) := by
    rw [show ((888662869541 / 500000000000) : ℝ) = ((500000000000 / 888662869541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (288190771 / 500000000) ≤ -Real.log (250000000000 / 444896851249) ∧
    -Real.log (250000000000 / 444896851249) ≤ (576381543 / 1000000000) := by
  have h := checkLog_sound (w := (194896851249 / 694896851249)) (n := 12)
    (lo := (288190771 / 500000000)) (hi := (576381543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444896851249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444896851249 / 250000000000) = 1/(250000000000 / 444896851249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (288190771 / 500000000) (576381543 / 1000000000) (Real.log (444896851249 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (444896851249 / 250000000000) = -Real.log (250000000000 / 444896851249) := by
    rw [show ((444896851249 / 250000000000) : ℝ) = ((250000000000 / 444896851249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (201247577 / 500000000) ≤ -Real.log (100000000000 / 149555167913) ∧
    -Real.log (100000000000 / 149555167913) ≤ (80499031 / 200000000) := by
  have h := checkLog_sound (w := (49555167913 / 249555167913)) (n := 12)
    (lo := (201247577 / 500000000)) (hi := (80499031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149555167913 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149555167913 / 100000000000) = 1/(100000000000 / 149555167913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201247577 / 500000000) (80499031 / 200000000) (Real.log (149555167913 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149555167913 / 100000000000) = -Real.log (100000000000 / 149555167913) := by
    rw [show ((149555167913 / 100000000000) : ℝ) = ((100000000000 / 149555167913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (403369713 / 1000000000) ≤ -Real.log (500000000000 / 748430099151) ∧
    -Real.log (500000000000 / 748430099151) ≤ (201684857 / 500000000) := by
  have h := checkLog_sound (w := (248430099151 / 1248430099151)) (n := 12)
    (lo := (403369713 / 1000000000)) (hi := (201684857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748430099151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748430099151 / 500000000000) = 1/(500000000000 / 748430099151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (403369713 / 1000000000) (201684857 / 500000000) (Real.log (748430099151 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (748430099151 / 500000000000) = -Real.log (500000000000 / 748430099151) := by
    rw [show ((748430099151 / 500000000000) : ℝ) = ((500000000000 / 748430099151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (5717217 / 20000000) ≤ -Real.log (250000000000 / 332726811843) ∧
    -Real.log (250000000000 / 332726811843) ≤ (285860851 / 1000000000) := by
  have h := checkLog_sound (w := (82726811843 / 582726811843)) (n := 12)
    (lo := (5717217 / 20000000)) (hi := (285860851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332726811843 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332726811843 / 250000000000) = 1/(250000000000 / 332726811843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (5717217 / 20000000) (285860851 / 1000000000) (Real.log (332726811843 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (332726811843 / 250000000000) = -Real.log (250000000000 / 332726811843) := by
    rw [show ((332726811843 / 250000000000) : ℝ) = ((250000000000 / 332726811843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (143242733 / 500000000) ≤ -Real.log (100000000000 / 133173881261) ∧
    -Real.log (100000000000 / 133173881261) ≤ (286485467 / 1000000000) := by
  have h := checkLog_sound (w := (33173881261 / 233173881261)) (n := 12)
    (lo := (143242733 / 500000000)) (hi := (286485467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133173881261 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133173881261 / 100000000000) = 1/(100000000000 / 133173881261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (143242733 / 500000000) (286485467 / 1000000000) (Real.log (133173881261 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (133173881261 / 100000000000) = -Real.log (100000000000 / 133173881261) := by
    rw [show ((133173881261 / 100000000000) : ℝ) = ((100000000000 / 133173881261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10224347 / 500000000) ≤ -Real.log (979758962559 / 1000000000000) ∧
    -Real.log (979758962559 / 1000000000000) ≤ (4089739 / 200000000) := by
  have h := checkLog_sound (w := (20241037441 / 1979758962559)) (n := 12)
    (lo := (10224347 / 500000000)) (hi := (4089739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979758962559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979758962559) = 1/(979758962559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4089739 / 200000000) (-10224347 / 500000000) (Real.log (979758962559 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (814397 / 40000000) ≤ -Real.log (39193837551 / 40000000000) ∧
    -Real.log (39193837551 / 40000000000) ≤ (10179963 / 500000000) := by
  have h := checkLog_sound (w := (806162449 / 79193837551)) (n := 12)
    (lo := (814397 / 40000000)) (hi := (10179963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39193837551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39193837551) = 1/(39193837551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10179963 / 500000000) (-814397 / 40000000) (Real.log (39193837551 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell051
