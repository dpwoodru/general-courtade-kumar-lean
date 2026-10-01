import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0095
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

theorem reflection_log_1_neg : (67517537 / 200000000) ≤ -Real.log (640 / 897) ∧
    -Real.log (640 / 897) ≤ (168793843 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1537)) (n := 12)
    (lo := (67517537 / 200000000)) (hi := (168793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897 / 640) = 1/(640 / 897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67517537 / 200000000) (168793843 / 500000000) (Real.log (897 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (897 / 640) = -Real.log (640 / 897) := by
    rw [show ((897 / 640) : ℝ) = ((640 / 897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (513433187 / 1000000000) ≤ -Real.log (383 / 640) ∧
    -Real.log (383 / 640) ≤ (128358297 / 250000000) := by
  have h := checkLog_sound (w := (257 / 1023)) (n := 12)
    (lo := (513433187 / 1000000000)) (hi := (128358297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 383) = 1/(383 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-128358297 / 250000000) (-513433187 / 1000000000) (Real.log (383 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67350243 / 200000000) ≤ -Real.log (512 / 717) ∧
    -Real.log (512 / 717) ≤ (21046951 / 62500000) := by
  have h := checkLog_sound (w := (205 / 1229)) (n := 12)
    (lo := (67350243 / 200000000)) (hi := (21046951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 512) = 1/(512 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67350243 / 200000000) (21046951 / 62500000) (Real.log (717 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (717 / 512) = -Real.log (512 / 717) := by
    rw [show ((717 / 512) : ℝ) = ((512 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (511476877 / 1000000000) ≤ -Real.log (307 / 512) ∧
    -Real.log (307 / 512) ≤ (255738439 / 500000000) := by
  have h := checkLog_sound (w := (205 / 819)) (n := 12)
    (lo := (511476877 / 1000000000)) (hi := (255738439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 307) = 1/(307 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-255738439 / 500000000) (-511476877 / 1000000000) (Real.log (307 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (58952127 / 100000000) ≤ -Real.log (320 / 577) ∧
    -Real.log (320 / 577) ≤ (589521271 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 897)) (n := 12)
    (lo := (58952127 / 100000000)) (hi := (589521271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 320) = 1/(320 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (58952127 / 100000000) (589521271 / 1000000000) (Real.log (577 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (577 / 320) = -Real.log (320 / 577) := by
    rw [show ((577 / 320) : ℝ) = ((320 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (406296567 / 250000000) ≤ -Real.log (63 / 320) ∧
    -Real.log (63 / 320) ≤ (1625186271 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 63) = 1/(63 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1625186271 / 1000000000) (-406296567 / 250000000) (Real.log (63 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (294110299 / 500000000) ≤ -Real.log (256 / 461) ∧
    -Real.log (256 / 461) ≤ (588220599 / 1000000000) := by
  have h := checkLog_sound (w := (205 / 717)) (n := 12)
    (lo := (294110299 / 500000000)) (hi := (588220599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 256) = 1/(256 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (294110299 / 500000000) (588220599 / 1000000000) (Real.log (461 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (461 / 256) = -Real.log (256 / 461) := by
    rw [show ((461 / 256) : ℝ) = ((256 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (161335181 / 100000000) ≤ -Real.log (51 / 256) ∧
    -Real.log (51 / 256) ≤ (1613351813 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 51) = 1/(51 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1613351813 / 1000000000) (-161335181 / 100000000) (Real.log (51 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (231201471 / 500000000) ≤ -Real.log (200000 / 317577) ∧
    -Real.log (200000 / 317577) ≤ (462402943 / 1000000000) := by
  have h := checkLog_sound (w := (117577 / 517577)) (n := 12)
    (lo := (231201471 / 500000000)) (hi := (462402943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317577 / 200000) = 1/(200000 / 317577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (231201471 / 500000000) (462402943 / 1000000000) (Real.log (317577 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (317577 / 200000) = -Real.log (200000 / 317577) := by
    rw [show ((317577 / 200000) : ℝ) = ((200000 / 317577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (886452841 / 1000000000) ≤ -Real.log (82423 / 200000) ∧
    -Real.log (82423 / 200000) ≤ (886452843 / 1000000000) := by
  have h := checkLog_sound (w := (17577 / 182423)) (n := 12)
    (lo := (193305661 / 1000000000)) (hi := (96652831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 82423) = 1/(82423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-886452843 / 1000000000) (-886452841 / 1000000000) (Real.log (82423 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (463608851 / 1000000000) ≤ -Real.log (1000000 / 1589801) ∧
    -Real.log (1000000 / 1589801) ≤ (115902213 / 250000000) := by
  have h := checkLog_sound (w := (589801 / 2589801)) (n := 12)
    (lo := (463608851 / 1000000000)) (hi := (115902213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1589801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1589801 / 1000000) = 1/(1000000 / 1589801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (463608851 / 1000000000) (115902213 / 250000000) (Real.log (1589801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1589801 / 1000000) = -Real.log (1000000 / 1589801) := by
    rw [show ((1589801 / 1000000) : ℝ) = ((1000000 / 1589801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89111287 / 100000000) ≤ -Real.log (410199 / 1000000) ∧
    -Real.log (410199 / 1000000) ≤ (111389109 / 125000000) := by
  have h := checkLog_sound (w := (89801 / 910199)) (n := 12)
    (lo := (19796569 / 100000000)) (hi := (197965691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 410199) = 1/(410199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111389109 / 125000000) (-89111287 / 100000000) (Real.log (410199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (377987019 / 1000000000) ≤ -Real.log (62500 / 91209) ∧
    -Real.log (62500 / 91209) ≤ (18899351 / 50000000) := by
  have h := checkLog_sound (w := (28709 / 153709)) (n := 12)
    (lo := (377987019 / 1000000000)) (hi := (18899351 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91209 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91209 / 62500) = 1/(62500 / 91209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (377987019 / 1000000000) (18899351 / 50000000) (Real.log (91209 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (91209 / 62500) = -Real.log (62500 / 91209) := by
    rw [show ((91209 / 62500) : ℝ) = ((62500 / 91209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (614972061 / 1000000000) ≤ -Real.log (33791 / 62500) ∧
    -Real.log (33791 / 62500) ≤ (307486031 / 500000000) := by
  have h := checkLog_sound (w := (28709 / 96291)) (n := 12)
    (lo := (614972061 / 1000000000)) (hi := (307486031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33791) = 1/(33791 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-307486031 / 500000000) (-614972061 / 1000000000) (Real.log (33791 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (75845033 / 200000000) ≤ -Real.log (31250 / 45661) ∧
    -Real.log (31250 / 45661) ≤ (189612583 / 500000000) := by
  have h := checkLog_sound (w := (14411 / 76911)) (n := 12)
    (lo := (75845033 / 200000000)) (hi := (189612583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45661 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45661 / 31250) = 1/(31250 / 45661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75845033 / 200000000) (189612583 / 500000000) (Real.log (45661 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (45661 / 31250) = -Real.log (31250 / 45661) := by
    rw [show ((45661 / 31250) : ℝ) = ((31250 / 45661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (618321751 / 1000000000) ≤ -Real.log (16839 / 31250) ∧
    -Real.log (16839 / 31250) ≤ (77290219 / 125000000) := by
  have h := checkLog_sound (w := (14411 / 48089)) (n := 12)
    (lo := (618321751 / 1000000000)) (hi := (77290219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 16839) = 1/(16839 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77290219 / 125000000) (-618321751 / 1000000000) (Real.log (16839 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1348855783 / 1000000000) ≤ -Real.log (250000000000 / 963253582131) ∧
    -Real.log (250000000000 / 963253582131) ≤ (269771157 / 200000000) := by
  have h := checkLog_sound (w := (463253582131 / 1463253582131)) (n := 12)
    (lo := (655708603 / 1000000000)) (hi := (163927151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963253582131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(963253582131 / 500000000000) = 1/(250000000000 / 963253582131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1348855783 / 1000000000) (269771157 / 200000000) (Real.log (963253582131 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (963253582131 / 250000000000) = -Real.log (250000000000 / 963253582131) := by
    rw [show ((963253582131 / 250000000000) : ℝ) = ((250000000000 / 963253582131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1354721721 / 1000000000) ≤ -Real.log (125000000000 / 484460286349) ∧
    -Real.log (125000000000 / 484460286349) ≤ (1354721723 / 1000000000) := by
  have h := checkLog_sound (w := (234460286349 / 734460286349)) (n := 12)
    (lo := (661574541 / 1000000000)) (hi := (330787271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484460286349 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(484460286349 / 250000000000) = 1/(125000000000 / 484460286349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1354721721 / 1000000000) (1354721723 / 1000000000) (Real.log (484460286349 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (484460286349 / 125000000000) = -Real.log (125000000000 / 484460286349) := by
    rw [show ((484460286349 / 125000000000) : ℝ) = ((125000000000 / 484460286349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (992959081 / 1000000000) ≤ -Real.log (125000000000 / 337401231097) ∧
    -Real.log (125000000000 / 337401231097) ≤ (992959083 / 1000000000) := by
  have h := checkLog_sound (w := (87401231097 / 587401231097)) (n := 12)
    (lo := (299811901 / 1000000000)) (hi := (149905951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337401231097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(337401231097 / 250000000000) = 1/(125000000000 / 337401231097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (992959081 / 1000000000) (992959083 / 1000000000) (Real.log (337401231097 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (337401231097 / 125000000000) = -Real.log (125000000000 / 337401231097) := by
    rw [show ((337401231097 / 125000000000) : ℝ) = ((125000000000 / 337401231097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (249386729 / 250000000) ≤ -Real.log (250000000000 / 677905457569) ∧
    -Real.log (250000000000 / 677905457569) ≤ (498773459 / 500000000) := by
  have h := checkLog_sound (w := (177905457569 / 1177905457569)) (n := 12)
    (lo := (38049967 / 125000000)) (hi := (304399737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677905457569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(677905457569 / 500000000000) = 1/(250000000000 / 677905457569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (249386729 / 250000000) (498773459 / 500000000) (Real.log (677905457569 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (677905457569 / 250000000000) = -Real.log (250000000000 / 677905457569) := by
    rw [show ((677905457569 / 250000000000) : ℝ) = ((250000000000 / 677905457569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0095
