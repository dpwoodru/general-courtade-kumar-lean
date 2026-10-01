import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0060
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

theorem reflection_log_1_neg : (366431877 / 1000000000) ≤ -Real.log (2560 / 3693) ∧
    -Real.log (2560 / 3693) ≤ (183215939 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 6253)) (n := 12)
    (lo := (366431877 / 1000000000)) (hi := (183215939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3693 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3693 / 2560) = 1/(2560 / 3693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (366431877 / 1000000000) (183215939 / 500000000) (Real.log (3693 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3693 / 2560) = -Real.log (2560 / 3693) := by
    rw [show ((3693 / 2560) : ℝ) = ((2560 / 3693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (584432919 / 1000000000) ≤ -Real.log (1427 / 2560) ∧
    -Real.log (1427 / 2560) ≤ (14610823 / 25000000) := by
  have h := checkLog_sound (w := (1133 / 3987)) (n := 12)
    (lo := (584432919 / 1000000000)) (hi := (14610823 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1427) = 1/(1427 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14610823 / 25000000) (-584432919 / 1000000000) (Real.log (1427 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291166407 / 500000000) ≤ -Real.log (143 / 256) ∧
    -Real.log (143 / 256) ≤ (116466563 / 200000000) := by
  have h := checkLog_sound (w := (113 / 399)) (n := 12)
    (lo := (291166407 / 500000000)) (hi := (116466563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 143) = 1/(143 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-116466563 / 200000000) (-291166407 / 500000000) (Real.log (143 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (158502677 / 250000000) ≤ -Real.log (1280 / 2413) ∧
    -Real.log (1280 / 2413) ≤ (634010709 / 1000000000) := by
  have h := checkLog_sound (w := (1133 / 3693)) (n := 12)
    (lo := (158502677 / 250000000)) (hi := (634010709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 1280) = 1/(1280 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (158502677 / 250000000) (634010709 / 1000000000) (Real.log (2413 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2413 / 1280) = -Real.log (1280 / 2413) := by
    rw [show ((2413 / 1280) : ℝ) = ((1280 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (135261423 / 62500000) ≤ -Real.log (147 / 1280) ∧
    -Real.log (147 / 1280) ≤ (541045693 / 250000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 147) = 1/(147 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-541045693 / 250000000) (-135261423 / 62500000) (Real.log (147 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252558983 / 500000000) ≤ -Real.log (1000000 / 1657181) ∧
    -Real.log (1000000 / 1657181) ≤ (505117967 / 1000000000) := by
  have h := checkLog_sound (w := (657181 / 2657181)) (n := 12)
    (lo := (252558983 / 500000000)) (hi := (505117967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657181 / 1000000) = 1/(1000000 / 1657181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252558983 / 500000000) (505117967 / 1000000000) (Real.log (1657181 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1657181 / 1000000) = -Real.log (1000000 / 1657181) := by
    rw [show ((1657181 / 1000000) : ℝ) = ((1000000 / 1657181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1070552667 / 1000000000) ≤ -Real.log (342819 / 1000000) ∧
    -Real.log (342819 / 1000000) ≤ (1070552669 / 1000000000) := by
  have h := checkLog_sound (w := (157181 / 842819)) (n := 12)
    (lo := (377405487 / 1000000000)) (hi := (23587843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342819) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 342819) = 1/(342819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1070552669 / 1000000000) (-1070552667 / 1000000000) (Real.log (342819 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (506365693 / 1000000000) ≤ -Real.log (4000 / 6637) ∧
    -Real.log (4000 / 6637) ≤ (253182847 / 500000000) := by
  have h := checkLog_sound (w := (2637 / 10637)) (n := 12)
    (lo := (506365693 / 1000000000)) (hi := (253182847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 4000) = 1/(4000 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (506365693 / 1000000000) (253182847 / 500000000) (Real.log (6637 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (6637 / 4000) = -Real.log (4000 / 6637) := by
    rw [show ((6637 / 4000) : ℝ) = ((4000 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1076606207 / 1000000000) ≤ -Real.log (1363 / 4000) ∧
    -Real.log (1363 / 4000) ≤ (1076606209 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3363)) (n := 12)
    (lo := (383459027 / 1000000000)) (hi := (95864757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2000 / 1363) = 1/(1363 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1076606209 / 1000000000) (-1076606207 / 1000000000) (Real.log (1363 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211665283 / 500000000) ≤ -Real.log (1000000 / 1527039) ∧
    -Real.log (1000000 / 1527039) ≤ (423330567 / 1000000000) := by
  have h := checkLog_sound (w := (527039 / 2527039)) (n := 12)
    (lo := (211665283 / 500000000)) (hi := (423330567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527039 / 1000000) = 1/(1000000 / 1527039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211665283 / 500000000) (423330567 / 1000000000) (Real.log (1527039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1527039 / 1000000) = -Real.log (1000000 / 1527039) := by
    rw [show ((1527039 / 1000000) : ℝ) = ((1000000 / 1527039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (149748469 / 200000000) ≤ -Real.log (472961 / 1000000) ∧
    -Real.log (472961 / 1000000) ≤ (748742347 / 1000000000) := by
  have h := checkLog_sound (w := (27039 / 972961)) (n := 12)
    (lo := (11119033 / 200000000)) (hi := (27797583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 472961) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 472961) = 1/(472961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-748742347 / 1000000000) (-149748469 / 200000000) (Real.log (472961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42470287 / 100000000) ≤ -Real.log (62500 / 95571) ∧
    -Real.log (62500 / 95571) ≤ (424702871 / 1000000000) := by
  have h := checkLog_sound (w := (33071 / 158071)) (n := 12)
    (lo := (42470287 / 100000000)) (hi := (424702871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95571 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95571 / 62500) = 1/(62500 / 95571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42470287 / 100000000) (424702871 / 1000000000) (Real.log (95571 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (95571 / 62500) = -Real.log (62500 / 95571) := by
    rw [show ((95571 / 62500) : ℝ) = ((62500 / 95571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (753185973 / 1000000000) ≤ -Real.log (29429 / 62500) ∧
    -Real.log (29429 / 62500) ≤ (30127439 / 40000000) := by
  have h := checkLog_sound (w := (1821 / 60679)) (n := 12)
    (lo := (60038793 / 1000000000)) (hi := (30019397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 29429) = 1/(29429 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30127439 / 40000000) (-753185973 / 1000000000) (Real.log (29429 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (196958829 / 125000000) ≤ -Real.log (100000000000 / 483398236387) ∧
    -Real.log (100000000000 / 483398236387) ≤ (315134127 / 200000000) := by
  have h := checkLog_sound (w := (83398236387 / 883398236387)) (n := 12)
    (lo := (11836017 / 62500000)) (hi := (189376273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483398236387 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(483398236387 / 400000000000) = 1/(100000000000 / 483398236387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (196958829 / 125000000) (315134127 / 200000000) (Real.log (483398236387 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (483398236387 / 100000000000) = -Real.log (100000000000 / 483398236387) := by
    rw [show ((483398236387 / 100000000000) : ℝ) = ((100000000000 / 483398236387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15829719 / 10000000) ≤ -Real.log (62500000000 / 304337857667) ∧
    -Real.log (62500000000 / 304337857667) ≤ (1582971903 / 1000000000) := by
  have h := checkLog_sound (w := (54337857667 / 554337857667)) (n := 12)
    (lo := (9833877 / 50000000)) (hi := (196677541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304337857667 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(304337857667 / 250000000000) = 1/(62500000000 / 304337857667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15829719 / 10000000) (1582971903 / 1000000000) (Real.log (304337857667 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (304337857667 / 62500000000) = -Real.log (62500000000 / 304337857667) := by
    rw [show ((304337857667 / 62500000000) : ℝ) = ((62500000000 / 304337857667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1172072911 / 1000000000) ≤ -Real.log (500000000000 / 1614339237273) ∧
    -Real.log (500000000000 / 1614339237273) ≤ (1172072913 / 1000000000) := by
  have h := checkLog_sound (w := (614339237273 / 2614339237273)) (n := 12)
    (lo := (478925731 / 1000000000)) (hi := (119731433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614339237273 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1614339237273 / 1000000000000) = 1/(500000000000 / 1614339237273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1172072911 / 1000000000) (1172072913 / 1000000000) (Real.log (1614339237273 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1614339237273 / 500000000000) = -Real.log (500000000000 / 1614339237273) := by
    rw [show ((1614339237273 / 500000000000) : ℝ) = ((500000000000 / 1614339237273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1177888843 / 1000000000) ≤ -Real.log (50000000000 / 162375547929) ∧
    -Real.log (50000000000 / 162375547929) ≤ (235577769 / 200000000) := by
  have h := checkLog_sound (w := (62375547929 / 262375547929)) (n := 12)
    (lo := (484741663 / 1000000000)) (hi := (15148177 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162375547929 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(162375547929 / 100000000000) = 1/(50000000000 / 162375547929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1177888843 / 1000000000) (235577769 / 200000000) (Real.log (162375547929 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (162375547929 / 50000000000) = -Real.log (50000000000 / 162375547929) := by
    rw [show ((162375547929 / 50000000000) : ℝ) = ((50000000000 / 162375547929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0060
