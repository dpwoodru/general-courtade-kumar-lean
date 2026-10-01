import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0033
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

theorem reflection_log_1_neg : (97032047 / 250000000) ≤ -Real.log (1280 / 1887) ∧
    -Real.log (1280 / 1887) ≤ (388128189 / 1000000000) := by
  have h := checkLog_sound (w := (607 / 3167)) (n := 12)
    (lo := (97032047 / 250000000)) (hi := (388128189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1280) = 1/(1280 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97032047 / 250000000) (388128189 / 1000000000) (Real.log (1887 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1887 / 1280) = -Real.log (1280 / 1887) := by
    rw [show ((1887 / 1280) : ℝ) = ((1280 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (642870027 / 1000000000) ≤ -Real.log (673 / 1280) ∧
    -Real.log (673 / 1280) ≤ (160717507 / 250000000) := by
  have h := checkLog_sound (w := (607 / 1953)) (n := 12)
    (lo := (642870027 / 1000000000)) (hi := (160717507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 673) = 1/(673 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-160717507 / 250000000) (-642870027 / 1000000000) (Real.log (673 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (387332959 / 1000000000) ≤ -Real.log (2560 / 3771) ∧
    -Real.log (2560 / 3771) ≤ (2420831 / 6250000) := by
  have h := checkLog_sound (w := (1211 / 6331)) (n := 12)
    (lo := (387332959 / 1000000000)) (hi := (2420831 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3771 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3771 / 2560) = 1/(2560 / 3771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (387332959 / 1000000000) (2420831 / 6250000) (Real.log (3771 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3771 / 2560) = -Real.log (2560 / 3771) := by
    rw [show ((3771 / 2560) : ℝ) = ((2560 / 3771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (640643681 / 1000000000) ≤ -Real.log (1349 / 2560) ∧
    -Real.log (1349 / 2560) ≤ (320321841 / 500000000) := by
  have h := checkLog_sound (w := (1211 / 3909)) (n := 12)
    (lo := (640643681 / 1000000000)) (hi := (320321841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1349) = 1/(1349 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-320321841 / 500000000) (-640643681 / 1000000000) (Real.log (1349 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667027769 / 1000000000) ≤ -Real.log (640 / 1247) ∧
    -Real.log (640 / 1247) ≤ (66702777 / 100000000) := by
  have h := checkLog_sound (w := (607 / 1887)) (n := 12)
    (lo := (667027769 / 1000000000)) (hi := (66702777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 640) = 1/(640 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667027769 / 1000000000) (66702777 / 100000000) (Real.log (1247 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1247 / 640) = -Real.log (640 / 1247) := by
    rw [show ((1247 / 640) : ℝ) = ((640 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (741240153 / 250000000) ≤ -Real.log (33 / 640) ∧
    -Real.log (33 / 640) ≤ (2964960617 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 33) = 1/(33 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2964960617 / 1000000000) (-741240153 / 250000000) (Real.log (33 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332912079 / 500000000) ≤ -Real.log (1280 / 2491) ∧
    -Real.log (1280 / 2491) ≤ (665824159 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3771)) (n := 12)
    (lo := (332912079 / 500000000)) (hi := (665824159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1280) = 1/(1280 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332912079 / 500000000) (665824159 / 1000000000) (Real.log (2491 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2491 / 1280) = -Real.log (1280 / 2491) := by
    rw [show ((2491 / 1280) : ℝ) = ((1280 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58410177 / 20000000) ≤ -Real.log (69 / 1280) ∧
    -Real.log (69 / 1280) ≤ (584101771 / 200000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 69) = 1/(69 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-584101771 / 200000000) (-58410177 / 20000000) (Real.log (69 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (270001497 / 500000000) ≤ -Real.log (250000 / 429003) ∧
    -Real.log (250000 / 429003) ≤ (108000599 / 200000000) := by
  have h := checkLog_sound (w := (179003 / 679003)) (n := 12)
    (lo := (270001497 / 500000000)) (hi := (108000599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429003 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429003 / 250000) = 1/(250000 / 429003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (270001497 / 500000000) (108000599 / 200000000) (Real.log (429003 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (429003 / 250000) = -Real.log (250000 / 429003) := by
    rw [show ((429003 / 250000) : ℝ) = ((250000 / 429003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (629411647 / 500000000) ≤ -Real.log (70997 / 250000) ∧
    -Real.log (70997 / 250000) ≤ (9834557 / 7812500) := by
  have h := checkLog_sound (w := (54003 / 195997)) (n := 12)
    (lo := (282838057 / 500000000)) (hi := (113135223 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70997) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 70997) = 1/(70997 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9834557 / 7812500) (-629411647 / 500000000) (Real.log (70997 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (541369183 / 1000000000) ≤ -Real.log (500000 / 859179) ∧
    -Real.log (500000 / 859179) ≤ (16917787 / 31250000) := by
  have h := checkLog_sound (w := (359179 / 1359179)) (n := 12)
    (lo := (541369183 / 1000000000)) (hi := (16917787 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859179 / 500000) = 1/(500000 / 859179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (541369183 / 1000000000) (16917787 / 31250000) (Real.log (859179 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (859179 / 500000) = -Real.log (500000 / 859179) := by
    rw [show ((859179 / 500000) : ℝ) = ((500000 / 859179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1267118517 / 1000000000) ≤ -Real.log (140821 / 500000) ∧
    -Real.log (140821 / 500000) ≤ (1267118519 / 1000000000) := by
  have h := checkLog_sound (w := (109179 / 390821)) (n := 12)
    (lo := (573971337 / 1000000000)) (hi := (286985669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 140821) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 140821) = 1/(140821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1267118519 / 1000000000) (-1267118517 / 1000000000) (Real.log (140821 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (231392569 / 500000000) ≤ -Real.log (250000 / 397123) ∧
    -Real.log (250000 / 397123) ≤ (462785139 / 1000000000) := by
  have h := checkLog_sound (w := (147123 / 647123)) (n := 12)
    (lo := (231392569 / 500000000)) (hi := (462785139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397123 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397123 / 250000) = 1/(250000 / 397123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (231392569 / 500000000) (462785139 / 1000000000) (Real.log (397123 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (397123 / 250000) = -Real.log (250000 / 397123) := by
    rw [show ((397123 / 250000) : ℝ) = ((250000 / 397123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (887926817 / 1000000000) ≤ -Real.log (102877 / 250000) ∧
    -Real.log (102877 / 250000) ≤ (887926819 / 1000000000) := by
  have h := checkLog_sound (w := (22123 / 227877)) (n := 12)
    (lo := (194779637 / 1000000000)) (hi := (97389819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102877) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 102877) = 1/(102877 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-887926819 / 1000000000) (-887926817 / 1000000000) (Real.log (102877 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (464376577 / 1000000000) ≤ -Real.log (500000 / 795511) ∧
    -Real.log (500000 / 795511) ≤ (232188289 / 500000000) := by
  have h := checkLog_sound (w := (295511 / 1295511)) (n := 12)
    (lo := (464376577 / 1000000000)) (hi := (232188289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795511 / 500000) = 1/(500000 / 795511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (464376577 / 1000000000) (232188289 / 500000000) (Real.log (795511 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (795511 / 500000) = -Real.log (500000 / 795511) := by
    rw [show ((795511 / 500000) : ℝ) = ((500000 / 795511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (894093913 / 1000000000) ≤ -Real.log (204489 / 500000) ∧
    -Real.log (204489 / 500000) ≤ (178818783 / 200000000) := by
  have h := checkLog_sound (w := (45511 / 454489)) (n := 12)
    (lo := (200946733 / 1000000000)) (hi := (100473367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 204489) = 1/(204489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-178818783 / 200000000) (-894093913 / 1000000000) (Real.log (204489 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (112426643 / 62500000) ≤ -Real.log (250000000000 / 1510637773427) ∧
    -Real.log (250000000000 / 1510637773427) ≤ (1798826291 / 1000000000) := by
  have h := checkLog_sound (w := (510637773427 / 2510637773427)) (n := 12)
    (lo := (51566491 / 125000000)) (hi := (412531929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510637773427 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1510637773427 / 1000000000000) = 1/(250000000000 / 1510637773427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (112426643 / 62500000) (1798826291 / 1000000000) (Real.log (1510637773427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1510637773427 / 250000000000) = -Real.log (250000000000 / 1510637773427) := by
    rw [show ((1510637773427 / 250000000000) : ℝ) = ((250000000000 / 1510637773427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18084877 / 10000000) ≤ -Real.log (250000000000 / 1525303399351) ∧
    -Real.log (250000000000 / 1525303399351) ≤ (1808487703 / 1000000000) := by
  have h := checkLog_sound (w := (525303399351 / 2525303399351)) (n := 12)
    (lo := (21109667 / 50000000)) (hi := (422193341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525303399351 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1525303399351 / 1000000000000) = 1/(250000000000 / 1525303399351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18084877 / 10000000) (1808487703 / 1000000000) (Real.log (1525303399351 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1525303399351 / 250000000000) = -Real.log (250000000000 / 1525303399351) := by
    rw [show ((1525303399351 / 250000000000) : ℝ) = ((250000000000 / 1525303399351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (270142391 / 200000000) ≤ -Real.log (31250000000 / 120630400867) ∧
    -Real.log (31250000000 / 120630400867) ≤ (1350711957 / 1000000000) := by
  have h := checkLog_sound (w := (58130400867 / 183130400867)) (n := 12)
    (lo := (26302591 / 40000000)) (hi := (82195597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120630400867 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(120630400867 / 62500000000) = 1/(31250000000 / 120630400867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (270142391 / 200000000) (1350711957 / 1000000000) (Real.log (120630400867 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (120630400867 / 31250000000) = -Real.log (31250000000 / 120630400867) := by
    rw [show ((120630400867 / 31250000000) : ℝ) = ((31250000000 / 120630400867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (135847049 / 100000000) ≤ -Real.log (500000000000 / 1945119297371) ∧
    -Real.log (500000000000 / 1945119297371) ≤ (339617623 / 250000000) := by
  have h := checkLog_sound (w := (945119297371 / 2945119297371)) (n := 12)
    (lo := (66532331 / 100000000)) (hi := (665323311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945119297371 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1945119297371 / 1000000000000) = 1/(500000000000 / 1945119297371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (135847049 / 100000000) (339617623 / 250000000) (Real.log (1945119297371 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1945119297371 / 500000000000) = -Real.log (500000000000 / 1945119297371) := by
    rw [show ((1945119297371 / 500000000000) : ℝ) = ((500000000000 / 1945119297371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0033
