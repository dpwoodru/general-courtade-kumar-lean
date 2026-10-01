import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0208
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

theorem reflection_log_1_neg : (11309827 / 20000000) ≤ -Real.log (3200 / 5633) ∧
    -Real.log (3200 / 5633) ≤ (565491351 / 1000000000) := by
  have h := checkLog_sound (w := (2433 / 8833)) (n := 12)
    (lo := (11309827 / 20000000)) (hi := (565491351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5633 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5633 / 3200) = 1/(3200 / 5633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11309827 / 20000000) (565491351 / 1000000000) (Real.log (5633 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5633 / 3200) = -Real.log (3200 / 5633) := by
    rw [show ((5633 / 3200) : ℝ) = ((3200 / 5633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (714209643 / 500000000) ≤ -Real.log (767 / 3200) ∧
    -Real.log (767 / 3200) ≤ (1428419289 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 767) = 1/(767 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1428419289 / 1000000000) (-714209643 / 500000000) (Real.log (767 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140528167 / 250000000) ≤ -Real.log (1600 / 2807) ∧
    -Real.log (1600 / 2807) ≤ (562112669 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 4407)) (n := 12)
    (lo := (140528167 / 250000000)) (hi := (562112669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2807 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2807 / 1600) = 1/(1600 / 2807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140528167 / 250000000) (562112669 / 1000000000) (Real.log (2807 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2807 / 1600) = -Real.log (1600 / 2807) := by
    rw [show ((2807 / 1600) : ℝ) = ((1600 / 2807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280789859 / 200000000) ≤ -Real.log (393 / 1600) ∧
    -Real.log (393 / 1600) ≤ (701974649 / 500000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 393) = 1/(393 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-701974649 / 500000000) (-280789859 / 200000000) (Real.log (393 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (209560717 / 500000000) ≤ -Real.log (1600 / 2433) ∧
    -Real.log (1600 / 2433) ≤ (83824287 / 200000000) := by
  have h := checkLog_sound (w := (833 / 4033)) (n := 12)
    (lo := (209560717 / 500000000)) (hi := (83824287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2433 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2433 / 1600) = 1/(1600 / 2433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (209560717 / 500000000) (83824287 / 200000000) (Real.log (2433 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2433 / 1600) = -Real.log (1600 / 2433) := by
    rw [show ((2433 / 1600) : ℝ) = ((1600 / 2433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (367636053 / 500000000) ≤ -Real.log (767 / 1600) ∧
    -Real.log (767 / 1600) ≤ (183818027 / 250000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 767) = 1/(767 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-183818027 / 250000000) (-367636053 / 500000000) (Real.log (767 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (411281493 / 1000000000) ≤ -Real.log (800 / 1207) ∧
    -Real.log (800 / 1207) ≤ (205640747 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2007)) (n := 12)
    (lo := (411281493 / 1000000000)) (hi := (205640747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 800) = 1/(800 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (411281493 / 1000000000) (205640747 / 500000000) (Real.log (1207 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1207 / 800) = -Real.log (800 / 1207) := by
    rw [show ((1207 / 800) : ℝ) = ((800 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142160423 / 200000000) ≤ -Real.log (393 / 800) ∧
    -Real.log (393 / 800) ≤ (710802117 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 393) = 1/(393 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-710802117 / 1000000000) (-142160423 / 200000000) (Real.log (393 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (304889579 / 500000000) ≤ -Real.log (40000 / 73601) ∧
    -Real.log (40000 / 73601) ≤ (609779159 / 1000000000) := by
  have h := checkLog_sound (w := (33601 / 113601)) (n := 12)
    (lo := (304889579 / 500000000)) (hi := (609779159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73601 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73601 / 40000) = 1/(40000 / 73601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (304889579 / 500000000) (609779159 / 1000000000) (Real.log (73601 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73601 / 40000) = -Real.log (40000 / 73601) := by
    rw [show ((73601 / 40000) : ℝ) = ((40000 / 73601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (458184431 / 250000000) ≤ -Real.log (6399 / 40000) ∧
    -Real.log (6399 / 40000) ≤ (1832737727 / 1000000000) := by
  have h := checkLog_sound (w := (3601 / 16399)) (n := 12)
    (lo := (111610841 / 250000000)) (hi := (89288673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6399) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 6399) = 1/(6399 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1832737727 / 1000000000) (-458184431 / 250000000) (Real.log (6399 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (305638193 / 500000000) ≤ -Real.log (500000 / 921391) ∧
    -Real.log (500000 / 921391) ≤ (611276387 / 1000000000) := by
  have h := checkLog_sound (w := (421391 / 1421391)) (n := 12)
    (lo := (305638193 / 500000000)) (hi := (611276387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921391 / 500000) = 1/(500000 / 921391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (305638193 / 500000000) (611276387 / 1000000000) (Real.log (921391 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (921391 / 500000) = -Real.log (500000 / 921391) := by
    rw [show ((921391 / 500000) : ℝ) = ((500000 / 921391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18501219 / 10000000) ≤ -Real.log (78609 / 500000) ∧
    -Real.log (78609 / 500000) ≤ (1850121903 / 1000000000) := by
  have h := checkLog_sound (w := (46391 / 203609)) (n := 12)
    (lo := (23191377 / 50000000)) (hi := (463827541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78609) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 78609) = 1/(78609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1850121903 / 1000000000) (-18501219 / 10000000) (Real.log (78609 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (748343 / 1250000) ≤ -Real.log (200000 / 363941) ∧
    -Real.log (200000 / 363941) ≤ (598674401 / 1000000000) := by
  have h := checkLog_sound (w := (163941 / 563941)) (n := 12)
    (lo := (748343 / 1250000)) (hi := (598674401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363941 / 200000) = 1/(200000 / 363941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (748343 / 1250000) (598674401 / 1000000000) (Real.log (363941 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (363941 / 200000) = -Real.log (200000 / 363941) := by
    rw [show ((363941 / 200000) : ℝ) = ((200000 / 363941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1713160879 / 1000000000) ≤ -Real.log (36059 / 200000) ∧
    -Real.log (36059 / 200000) ≤ (856580441 / 500000000) := by
  have h := checkLog_sound (w := (13941 / 86059)) (n := 12)
    (lo := (326866519 / 1000000000)) (hi := (8171663 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36059) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 36059) = 1/(36059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-856580441 / 500000000) (-1713160879 / 1000000000) (Real.log (36059 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (60083889 / 100000000) ≤ -Real.log (31250 / 56989) ∧
    -Real.log (31250 / 56989) ≤ (600838891 / 1000000000) := by
  have h := checkLog_sound (w := (25739 / 88239)) (n := 12)
    (lo := (60083889 / 100000000)) (hi := (600838891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56989 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56989 / 31250) = 1/(31250 / 56989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (60083889 / 100000000) (600838891 / 1000000000) (Real.log (56989 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (56989 / 31250) = -Real.log (31250 / 56989) := by
    rw [show ((56989 / 31250) : ℝ) = ((31250 / 56989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5422729 / 3125000) ≤ -Real.log (5511 / 31250) ∧
    -Real.log (5511 / 31250) ≤ (1735273283 / 1000000000) := by
  have h := checkLog_sound (w := (4603 / 26647)) (n := 12)
    (lo := (8724473 / 25000000)) (hi := (348978921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11022) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11022) = 1/(5511 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1735273283 / 1000000000) (-5422729 / 3125000) (Real.log (5511 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1221258441 / 500000000) ≤ -Real.log (500000000000 / 5750976715111) ∧
    -Real.log (500000000000 / 5750976715111) ≤ (1221258443 / 500000000) := by
  have h := checkLog_sound (w := (1750976715111 / 9750976715111)) (n := 12)
    (lo := (181537671 / 500000000)) (hi := (363075343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5750976715111 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5750976715111 / 4000000000000) = 1/(500000000000 / 5750976715111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1221258441 / 500000000) (1221258443 / 500000000) (Real.log (5750976715111 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5750976715111 / 500000000000) = -Real.log (500000000000 / 5750976715111) := by
    rw [show ((5750976715111 / 500000000000) : ℝ) = ((500000000000 / 5750976715111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1230699143 / 500000000) ≤ -Real.log (50000000000 / 586059484283) ∧
    -Real.log (50000000000 / 586059484283) ≤ (246139829 / 100000000) := by
  have h := checkLog_sound (w := (186059484283 / 986059484283)) (n := 12)
    (lo := (190978373 / 500000000)) (hi := (381956747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586059484283 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(586059484283 / 400000000000) = 1/(50000000000 / 586059484283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1230699143 / 500000000) (246139829 / 100000000) (Real.log (586059484283 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (586059484283 / 50000000000) = -Real.log (50000000000 / 586059484283) := by
    rw [show ((586059484283 / 50000000000) : ℝ) = ((50000000000 / 586059484283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2311835279 / 1000000000) ≤ -Real.log (10000000000 / 100929310297) ∧
    -Real.log (10000000000 / 100929310297) ≤ (2311835283 / 1000000000) := by
  have h := checkLog_sound (w := (20929310297 / 180929310297)) (n := 12)
    (lo := (232393739 / 1000000000)) (hi := (11619687 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100929310297 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100929310297 / 80000000000) = 1/(10000000000 / 100929310297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2311835279 / 1000000000) (2311835283 / 1000000000) (Real.log (100929310297 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (100929310297 / 10000000000) = -Real.log (10000000000 / 100929310297) := by
    rw [show ((100929310297 / 10000000000) : ℝ) = ((10000000000 / 100929310297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (233611217 / 100000000) ≤ -Real.log (125000000000 / 1292619306841) ∧
    -Real.log (125000000000 / 1292619306841) ≤ (1168056087 / 500000000) := by
  have h := checkLog_sound (w := (292619306841 / 2292619306841)) (n := 12)
    (lo := (25667063 / 100000000)) (hi := (256670631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292619306841 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1292619306841 / 1000000000000) = 1/(125000000000 / 1292619306841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (233611217 / 100000000) (1168056087 / 500000000) (Real.log (1292619306841 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1292619306841 / 125000000000) = -Real.log (125000000000 / 1292619306841) := by
    rw [show ((1292619306841 / 125000000000) : ℝ) = ((125000000000 / 1292619306841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0208
