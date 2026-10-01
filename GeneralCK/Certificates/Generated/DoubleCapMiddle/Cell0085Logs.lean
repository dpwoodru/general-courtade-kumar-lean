import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0085
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

theorem reflection_log_1_neg : (21619633 / 62500000) ≤ -Real.log (1280 / 1809) ∧
    -Real.log (1280 / 1809) ≤ (345914129 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3089)) (n := 12)
    (lo := (21619633 / 62500000)) (hi := (345914129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1809 / 1280) = 1/(1280 / 1809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21619633 / 62500000) (345914129 / 1000000000) (Real.log (1809 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1809 / 1280) = -Real.log (1280 / 1809) := by
    rw [show ((1809 / 1280) : ℝ) = ((1280 / 1809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (106641941 / 200000000) ≤ -Real.log (751 / 1280) ∧
    -Real.log (751 / 1280) ≤ (266604853 / 500000000) := by
  have h := checkLog_sound (w := (529 / 2031)) (n := 12)
    (lo := (106641941 / 200000000)) (hi := (266604853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 751) = 1/(751 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266604853 / 500000000) (-106641941 / 200000000) (Real.log (751 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (345084597 / 1000000000) ≤ -Real.log (512 / 723) ∧
    -Real.log (512 / 723) ≤ (172542299 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1235)) (n := 12)
    (lo := (345084597 / 1000000000)) (hi := (172542299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 512) = 1/(512 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (345084597 / 1000000000) (172542299 / 500000000) (Real.log (723 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (723 / 512) = -Real.log (512 / 723) := by
    rw [show ((723 / 512) : ℝ) = ((512 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13280359 / 25000000) ≤ -Real.log (301 / 512) ∧
    -Real.log (301 / 512) ≤ (531214361 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 813)) (n := 12)
    (lo := (13280359 / 25000000)) (hi := (531214361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 301) = 1/(301 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-531214361 / 1000000000) (-13280359 / 25000000) (Real.log (301 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (120487157 / 200000000) ≤ -Real.log (640 / 1169) ∧
    -Real.log (640 / 1169) ≤ (301217893 / 500000000) := by
  have h := checkLog_sound (w := (529 / 1809)) (n := 12)
    (lo := (120487157 / 200000000)) (hi := (301217893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 640) = 1/(640 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (120487157 / 200000000) (301217893 / 500000000) (Real.log (1169 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1169 / 640) = -Real.log (640 / 1169) := by
    rw [show ((1169 / 640) : ℝ) = ((640 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1751937973 / 1000000000) ≤ -Real.log (111 / 640) ∧
    -Real.log (111 / 640) ≤ (218992247 / 125000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 111) = 1/(111 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-218992247 / 125000000) (-1751937973 / 1000000000) (Real.log (111 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (601151813 / 1000000000) ≤ -Real.log (256 / 467) ∧
    -Real.log (256 / 467) ≤ (300575907 / 500000000) := by
  have h := checkLog_sound (w := (211 / 723)) (n := 12)
    (lo := (601151813 / 1000000000)) (hi := (300575907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 256) = 1/(256 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (601151813 / 1000000000) (300575907 / 500000000) (Real.log (467 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (467 / 256) = -Real.log (256 / 467) := by
    rw [show ((467 / 256) : ℝ) = ((256 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1738514953 / 1000000000) ≤ -Real.log (45 / 256) ∧
    -Real.log (45 / 256) ≤ (434628739 / 250000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 45) = 1/(45 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-434628739 / 250000000) (-1738514953 / 1000000000) (Real.log (45 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (474477979 / 1000000000) ≤ -Real.log (40000 / 64287) ∧
    -Real.log (40000 / 64287) ≤ (23723899 / 50000000) := by
  have h := checkLog_sound (w := (24287 / 104287)) (n := 12)
    (lo := (474477979 / 1000000000)) (hi := (23723899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64287 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64287 / 40000) = 1/(40000 / 64287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (474477979 / 1000000000) (23723899 / 50000000) (Real.log (64287 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (64287 / 40000) = -Real.log (40000 / 64287) := by
    rw [show ((64287 / 40000) : ℝ) = ((40000 / 64287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (467195529 / 500000000) ≤ -Real.log (15713 / 40000) ∧
    -Real.log (15713 / 40000) ≤ (46719553 / 50000000) := by
  have h := checkLog_sound (w := (4287 / 35713)) (n := 12)
    (lo := (120621939 / 500000000)) (hi := (241243879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 15713) = 1/(15713 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-46719553 / 50000000) (-467195529 / 500000000) (Real.log (15713 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (47568931 / 100000000) ≤ -Real.log (1000000 / 1609123) ∧
    -Real.log (1000000 / 1609123) ≤ (475689311 / 1000000000) := by
  have h := checkLog_sound (w := (609123 / 2609123)) (n := 12)
    (lo := (47568931 / 100000000)) (hi := (475689311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609123 / 1000000) = 1/(1000000 / 1609123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (47568931 / 100000000) (475689311 / 1000000000) (Real.log (1609123 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1609123 / 1000000) = -Real.log (1000000 / 1609123) := by
    rw [show ((1609123 / 1000000) : ℝ) = ((1000000 / 1609123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (187872469 / 200000000) ≤ -Real.log (390877 / 1000000) ∧
    -Real.log (390877 / 1000000) ≤ (939362347 / 1000000000) := by
  have h := checkLog_sound (w := (109123 / 890877)) (n := 12)
    (lo := (49243033 / 200000000)) (hi := (123107583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390877) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 390877) = 1/(390877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-939362347 / 1000000000) (-187872469 / 200000000) (Real.log (390877 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78098989 / 200000000) ≤ -Real.log (62500 / 92357) ∧
    -Real.log (62500 / 92357) ≤ (195247473 / 500000000) := by
  have h := checkLog_sound (w := (29857 / 154857)) (n := 12)
    (lo := (78098989 / 200000000)) (hi := (195247473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92357 / 62500) = 1/(62500 / 92357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78098989 / 200000000) (195247473 / 500000000) (Real.log (92357 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (92357 / 62500) = -Real.log (62500 / 92357) := by
    rw [show ((92357 / 62500) : ℝ) = ((62500 / 92357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (649536119 / 1000000000) ≤ -Real.log (32643 / 62500) ∧
    -Real.log (32643 / 62500) ≤ (16238403 / 25000000) := by
  have h := checkLog_sound (w := (29857 / 95143)) (n := 12)
    (lo := (649536119 / 1000000000)) (hi := (16238403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 32643) = 1/(32643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-16238403 / 25000000) (-649536119 / 1000000000) (Real.log (32643 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39176367 / 100000000) ≤ -Real.log (250000 / 369897) ∧
    -Real.log (250000 / 369897) ≤ (391763671 / 1000000000) := by
  have h := checkLog_sound (w := (119897 / 619897)) (n := 12)
    (lo := (39176367 / 100000000)) (hi := (391763671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369897 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369897 / 250000) = 1/(250000 / 369897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39176367 / 100000000) (391763671 / 1000000000) (Real.log (369897 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (369897 / 250000) = -Real.log (250000 / 369897) := by
    rw [show ((369897 / 250000) : ℝ) = ((250000 / 369897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (653134473 / 1000000000) ≤ -Real.log (130103 / 250000) ∧
    -Real.log (130103 / 250000) ≤ (326567237 / 500000000) := by
  have h := checkLog_sound (w := (119897 / 380103)) (n := 12)
    (lo := (653134473 / 1000000000)) (hi := (326567237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130103) = 1/(130103 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-326567237 / 500000000) (-653134473 / 1000000000) (Real.log (130103 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1408869037 / 1000000000) ≤ -Real.log (250000000000 / 1022831413479) ∧
    -Real.log (250000000000 / 1022831413479) ≤ (17610863 / 12500000) := by
  have h := checkLog_sound (w := (22831413479 / 2022831413479)) (n := 12)
    (lo := (22574677 / 1000000000)) (hi := (11287339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022831413479 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1022831413479 / 1000000000000) = 1/(250000000000 / 1022831413479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1408869037 / 1000000000) (17610863 / 12500000) (Real.log (1022831413479 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1022831413479 / 250000000000) = -Real.log (250000000000 / 1022831413479) := by
    rw [show ((1022831413479 / 250000000000) : ℝ) = ((250000000000 / 1022831413479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (283010331 / 200000000) ≤ -Real.log (250000000000 / 1029174778767) ∧
    -Real.log (250000000000 / 1029174778767) ≤ (707525829 / 500000000) := by
  have h := checkLog_sound (w := (29174778767 / 2029174778767)) (n := 12)
    (lo := (5751459 / 200000000)) (hi := (1797331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029174778767 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1029174778767 / 1000000000000) = 1/(250000000000 / 1029174778767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (283010331 / 200000000) (707525829 / 500000000) (Real.log (1029174778767 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1029174778767 / 250000000000) = -Real.log (250000000000 / 1029174778767) := by
    rw [show ((1029174778767 / 250000000000) : ℝ) = ((250000000000 / 1029174778767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (130003883 / 125000000) ≤ -Real.log (250000000000 / 707326226143) ∧
    -Real.log (250000000000 / 707326226143) ≤ (520015533 / 500000000) := by
  have h := checkLog_sound (w := (207326226143 / 1207326226143)) (n := 12)
    (lo := (86720971 / 250000000)) (hi := (69376777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707326226143 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(707326226143 / 500000000000) = 1/(250000000000 / 707326226143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (130003883 / 125000000) (520015533 / 500000000) (Real.log (707326226143 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (707326226143 / 250000000000) = -Real.log (250000000000 / 707326226143) := by
    rw [show ((707326226143 / 250000000000) : ℝ) = ((250000000000 / 707326226143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1044898143 / 1000000000) ≤ -Real.log (500000000000 / 1421554460697) ∧
    -Real.log (500000000000 / 1421554460697) ≤ (208979629 / 200000000) := by
  have h := checkLog_sound (w := (421554460697 / 2421554460697)) (n := 12)
    (lo := (351750963 / 1000000000)) (hi := (87937741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421554460697 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1421554460697 / 1000000000000) = 1/(500000000000 / 1421554460697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1044898143 / 1000000000) (208979629 / 200000000) (Real.log (1421554460697 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1421554460697 / 500000000000) = -Real.log (500000000000 / 1421554460697) := by
    rw [show ((1421554460697 / 500000000000) : ℝ) = ((500000000000 / 1421554460697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0085
