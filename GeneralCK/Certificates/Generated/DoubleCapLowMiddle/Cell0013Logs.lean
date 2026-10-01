import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0013
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

theorem reflection_log_1_neg : (34124377 / 50000000) ≤ -Real.log (1000000000000 / 1978793945313) ∧
    -Real.log (1000000000000 / 1978793945313) ≤ (682487541 / 1000000000) := by
  have h := checkLog_sound (w := (978793945313 / 2978793945313)) (n := 12)
    (lo := (34124377 / 50000000)) (hi := (682487541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978793945313 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978793945313 / 1000000000000) = 1/(1000000000000 / 1978793945313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34124377 / 50000000) (682487541 / 1000000000) (Real.log (1978793945313 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1978793945313 / 1000000000000) = -Real.log (1000000000000 / 1978793945313) := by
    rw [show ((1978793945313 / 1000000000000) : ℝ) = ((1000000000000 / 1978793945313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (481683567 / 125000000) ≤ -Real.log (21206054687 / 1000000000000) ∧
    -Real.log (21206054687 / 1000000000000) ≤ (1926734271 / 500000000) := by
  have h := checkLog_sound (w := (10043945313 / 52456054687)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 21206054687) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 21206054687) = 1/(21206054687 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1926734271 / 500000000) (-481683567 / 125000000) (Real.log (21206054687 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136488131 / 200000000) ≤ -Real.log (102400 / 202619) ∧
    -Real.log (102400 / 202619) ≤ (42652541 / 62500000) := by
  have h := checkLog_sound (w := (100219 / 305019)) (n := 12)
    (lo := (136488131 / 200000000)) (hi := (42652541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202619 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202619 / 102400) = 1/(102400 / 202619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136488131 / 200000000) (42652541 / 62500000) (Real.log (202619 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202619 / 102400) = -Real.log (102400 / 202619) := by
    rw [show ((202619 / 102400) : ℝ) = ((102400 / 202619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1924551611 / 500000000) ≤ -Real.log (2181 / 102400) ∧
    -Real.log (2181 / 102400) ≤ (962275807 / 250000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2181) = 1/(2181 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-962275807 / 250000000) (-1924551611 / 500000000) (Real.log (2181 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671713047 / 1000000000) ≤ -Real.log (102400 / 200457) ∧
    -Real.log (102400 / 200457) ≤ (83964131 / 125000000) := by
  have h := checkLog_sound (w := (98057 / 302857)) (n := 12)
    (lo := (671713047 / 1000000000)) (hi := (83964131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200457 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200457 / 102400) = 1/(102400 / 200457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671713047 / 1000000000) (83964131 / 125000000) (Real.log (200457 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200457 / 102400) = -Real.log (102400 / 200457) := by
    rw [show ((200457 / 102400) : ℝ) = ((102400 / 200457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (790080339 / 250000000) ≤ -Real.log (4343 / 102400) ∧
    -Real.log (4343 / 102400) ≤ (3160321361 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 10743)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4343) = 1/(4343 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3160321361 / 1000000000) (-790080339 / 250000000) (Real.log (4343 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671618259 / 1000000000) ≤ -Real.log (51200 / 100219) ∧
    -Real.log (51200 / 100219) ≤ (33580913 / 50000000) := by
  have h := checkLog_sound (w := (49019 / 151419)) (n := 12)
    (lo := (671618259 / 1000000000)) (hi := (33580913 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100219 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100219 / 51200) = 1/(51200 / 100219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671618259 / 1000000000) (33580913 / 50000000) (Real.log (100219 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100219 / 51200) = -Real.log (51200 / 100219) := by
    rw [show ((100219 / 51200) : ℝ) = ((51200 / 100219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1577978021 / 500000000) ≤ -Real.log (2181 / 51200) ∧
    -Real.log (2181 / 51200) ≤ (3155956047 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2181) = 1/(2181 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3155956047 / 1000000000) (-1577978021 / 500000000) (Real.log (2181 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684069099 / 1000000000) ≤ -Real.log (500000 / 990963) ∧
    -Real.log (500000 / 990963) ≤ (6840691 / 10000000) := by
  have h := checkLog_sound (w := (490963 / 1490963)) (n := 12)
    (lo := (684069099 / 1000000000)) (hi := (6840691 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990963 / 500000) = 1/(500000 / 990963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684069099 / 1000000000) (6840691 / 10000000) (Real.log (990963 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990963 / 500000) = -Real.log (500000 / 990963) := by
    rw [show ((990963 / 500000) : ℝ) = ((500000 / 990963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2006640417 / 500000000) ≤ -Real.log (9037 / 500000) ∧
    -Real.log (9037 / 500000) ≤ (100332021 / 25000000) := by
  have h := checkLog_sound (w := (3294 / 12331)) (n := 12)
    (lo := (273772467 / 500000000)) (hi := (109508987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9037) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9037) = 1/(9037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-100332021 / 25000000) (-2006640417 / 500000000) (Real.log (9037 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684107949 / 1000000000) ≤ -Real.log (1000000 / 1982003) ∧
    -Real.log (1000000 / 1982003) ≤ (13682159 / 20000000) := by
  have h := checkLog_sound (w := (982003 / 2982003)) (n := 12)
    (lo := (684107949 / 1000000000)) (hi := (13682159 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982003 / 1000000) = 1/(1000000 / 1982003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684107949 / 1000000000) (13682159 / 20000000) (Real.log (1982003 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982003 / 1000000) = -Real.log (1000000 / 1982003) := by
    rw [show ((1982003 / 1000000) : ℝ) = ((1000000 / 1982003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2008775099 / 500000000) ≤ -Real.log (17997 / 1000000) ∧
    -Real.log (17997 / 1000000) ≤ (1004387551 / 250000000) := by
  have h := checkLog_sound (w := (13253 / 49247)) (n := 12)
    (lo := (275907149 / 500000000)) (hi := (551814299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17997) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17997) = 1/(17997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1004387551 / 250000000) (-2008775099 / 500000000) (Real.log (17997 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684033779 / 1000000000) ≤ -Real.log (31250 / 61933) ∧
    -Real.log (31250 / 61933) ≤ (34201689 / 50000000) := by
  have h := checkLog_sound (w := (30683 / 93183)) (n := 12)
    (lo := (684033779 / 1000000000)) (hi := (34201689 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61933 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61933 / 31250) = 1/(31250 / 61933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684033779 / 1000000000) (34201689 / 50000000) (Real.log (61933 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61933 / 31250) = -Real.log (31250 / 61933) := by
    rw [show ((61933 / 31250) : ℝ) = ((31250 / 61933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1002353837 / 250000000) ≤ -Real.log (567 / 31250) ∧
    -Real.log (567 / 31250) ≤ (2004707677 / 500000000) := by
  have h := checkLog_sound (w := (6553 / 24697)) (n := 12)
    (lo := (67959931 / 125000000)) (hi := (543679449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9072) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9072) = 1/(567 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2004707677 / 500000000) (-1002353837 / 250000000) (Real.log (567 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684072631 / 1000000000) ≤ -Real.log (1000000 / 1981933) ∧
    -Real.log (1000000 / 1981933) ≤ (85509079 / 125000000) := by
  have h := checkLog_sound (w := (981933 / 2981933)) (n := 12)
    (lo := (684072631 / 1000000000)) (hi := (85509079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981933 / 1000000) = 1/(1000000 / 1981933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684072631 / 1000000000) (85509079 / 125000000) (Real.log (1981933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981933 / 1000000) = -Real.log (1000000 / 1981933) := by
    rw [show ((1981933 / 1000000) : ℝ) = ((1000000 / 1981933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2006834103 / 500000000) ≤ -Real.log (18067 / 1000000) ∧
    -Real.log (18067 / 1000000) ≤ (1003417053 / 250000000) := by
  have h := checkLog_sound (w := (13183 / 49317)) (n := 12)
    (lo := (273966153 / 500000000)) (hi := (547932307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18067) = 1/(18067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1003417053 / 250000000) (-2006834103 / 500000000) (Real.log (18067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4697349933 / 1000000000) ≤ -Real.log (500000000000 / 54828095606949) ∧
    -Real.log (500000000000 / 54828095606949) ≤ (234867497 / 50000000) := by
  have h := checkLog_sound (w := (22828095606949 / 86828095606949)) (n := 12)
    (lo := (538466853 / 1000000000)) (hi := (269233427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54828095606949 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54828095606949 / 32000000000000) = 1/(500000000000 / 54828095606949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4697349933 / 1000000000) (234867497 / 50000000) (Real.log (54828095606949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (54828095606949 / 500000000000) = -Real.log (500000000000 / 54828095606949) := by
    rw [show ((54828095606949 / 500000000000) : ℝ) = ((500000000000 / 54828095606949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4701658147 / 1000000000) ≤ -Real.log (250000000000 / 27532408179141) ∧
    -Real.log (250000000000 / 27532408179141) ≤ (2350829077 / 500000000) := by
  have h := checkLog_sound (w := (11532408179141 / 43532408179141)) (n := 12)
    (lo := (542775067 / 1000000000)) (hi := (135693767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27532408179141 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27532408179141 / 16000000000000) = 1/(250000000000 / 27532408179141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4701658147 / 1000000000) (2350829077 / 500000000) (Real.log (27532408179141 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27532408179141 / 250000000000) = -Real.log (250000000000 / 27532408179141) := by
    rw [show ((27532408179141 / 250000000000) : ℝ) = ((250000000000 / 27532408179141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4693449127 / 1000000000) ≤ -Real.log (500000000000 / 54614638447971) ∧
    -Real.log (500000000000 / 54614638447971) ≤ (2346724567 / 500000000) := by
  have h := checkLog_sound (w := (22614638447971 / 86614638447971)) (n := 12)
    (lo := (534566047 / 1000000000)) (hi := (16705189 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54614638447971 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54614638447971 / 32000000000000) = 1/(500000000000 / 54614638447971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4693449127 / 1000000000) (2346724567 / 500000000) (Real.log (54614638447971 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (54614638447971 / 500000000000) = -Real.log (500000000000 / 54614638447971) := by
    rw [show ((54614638447971 / 500000000000) : ℝ) = ((500000000000 / 54614638447971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1174435209 / 250000000) ≤ -Real.log (500000000000 / 54849532296453) ∧
    -Real.log (500000000000 / 54849532296453) ≤ (4697740843 / 1000000000) := by
  have h := checkLog_sound (w := (22849532296453 / 86849532296453)) (n := 12)
    (lo := (134714439 / 250000000)) (hi := (538857757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54849532296453 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54849532296453 / 32000000000000) = 1/(500000000000 / 54849532296453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1174435209 / 250000000) (4697740843 / 1000000000) (Real.log (54849532296453 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (54849532296453 / 500000000000) = -Real.log (500000000000 / 54849532296453) := by
    rw [show ((54849532296453 / 500000000000) : ℝ) = ((500000000000 / 54849532296453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0013
