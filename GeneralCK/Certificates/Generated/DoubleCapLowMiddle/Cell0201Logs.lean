import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0201
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

theorem reflection_log_1_neg : (588827789 / 1000000000) ≤ -Real.log (1600 / 2883) ∧
    -Real.log (1600 / 2883) ≤ (58882779 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 4483)) (n := 12)
    (lo := (588827789 / 1000000000)) (hi := (58882779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 1600) = 1/(1600 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (588827789 / 1000000000) (58882779 / 100000000) (Real.log (2883 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2883 / 1600) = -Real.log (1600 / 2883) := by
    rw [show ((2883 / 1600) : ℝ) = ((1600 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1618857133 / 1000000000) ≤ -Real.log (317 / 1600) ∧
    -Real.log (317 / 1600) ≤ (101178571 / 62500000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 317) = 1/(317 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-101178571 / 62500000) (-1618857133 / 1000000000) (Real.log (317 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (585527169 / 1000000000) ≤ -Real.log (3200 / 5747) ∧
    -Real.log (3200 / 5747) ≤ (58552717 / 100000000) := by
  have h := checkLog_sound (w := (2547 / 8947)) (n := 12)
    (lo := (585527169 / 1000000000)) (hi := (58552717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5747 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5747 / 3200) = 1/(3200 / 5747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (585527169 / 1000000000) (58552717 / 100000000) (Real.log (5747 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5747 / 3200) = -Real.log (3200 / 5747) := by
    rw [show ((5747 / 3200) : ℝ) = ((3200 / 5747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (794664479 / 500000000) ≤ -Real.log (653 / 3200) ∧
    -Real.log (653 / 3200) ≤ (1589328961 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 653) = 1/(653 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1589328961 / 1000000000) (-794664479 / 500000000) (Real.log (653 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118086159 / 250000000) ≤ -Real.log (800 / 1283) ∧
    -Real.log (800 / 1283) ≤ (472344637 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 2083)) (n := 12)
    (lo := (118086159 / 250000000)) (hi := (472344637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 800) = 1/(800 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118086159 / 250000000) (472344637 / 1000000000) (Real.log (1283 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1283 / 800) = -Real.log (800 / 1283) := by
    rw [show ((1283 / 800) : ℝ) = ((800 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (925709953 / 1000000000) ≤ -Real.log (317 / 800) ∧
    -Real.log (317 / 800) ≤ (185141991 / 200000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 317) = 1/(317 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-185141991 / 200000000) (-925709953 / 1000000000) (Real.log (317 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232456283 / 500000000) ≤ -Real.log (1600 / 2547) ∧
    -Real.log (1600 / 2547) ≤ (464912567 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 4147)) (n := 12)
    (lo := (232456283 / 500000000)) (hi := (464912567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 1600) = 1/(1600 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232456283 / 500000000) (464912567 / 1000000000) (Real.log (2547 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2547 / 1600) = -Real.log (1600 / 2547) := by
    rw [show ((2547 / 1600) : ℝ) = ((1600 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (448090889 / 500000000) ≤ -Real.log (653 / 1600) ∧
    -Real.log (653 / 1600) ≤ (44809089 / 50000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 653) = 1/(653 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-44809089 / 50000000) (-448090889 / 500000000) (Real.log (653 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155211317 / 250000000) ≤ -Real.log (2000 / 3721) ∧
    -Real.log (2000 / 3721) ≤ (620845269 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 5721)) (n := 12)
    (lo := (155211317 / 250000000)) (hi := (620845269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3721 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3721 / 2000) = 1/(2000 / 3721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155211317 / 250000000) (620845269 / 1000000000) (Real.log (3721 / 2000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (3721 / 2000) = -Real.log (2000 / 3721) := by
    rw [show ((3721 / 2000) : ℝ) = ((2000 / 3721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (492422669 / 250000000) ≤ -Real.log (279 / 2000) ∧
    -Real.log (279 / 2000) ≤ (1969690679 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 779)) (n := 12)
    (lo := (145849079 / 250000000)) (hi := (583396317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(500 / 279) = 1/(279 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1969690679 / 1000000000) (-492422669 / 250000000) (Real.log (279 / 2000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (622535857 / 1000000000) ≤ -Real.log (31250 / 58239) ∧
    -Real.log (31250 / 58239) ≤ (311267929 / 500000000) := by
  have h := checkLog_sound (w := (26989 / 89489)) (n := 12)
    (lo := (622535857 / 1000000000)) (hi := (311267929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58239 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58239 / 31250) = 1/(31250 / 58239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (622535857 / 1000000000) (311267929 / 500000000) (Real.log (58239 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58239 / 31250) = -Real.log (31250 / 58239) := by
    rw [show ((58239 / 31250) : ℝ) = ((31250 / 58239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3985031 / 2000000) ≤ -Real.log (4261 / 31250) ∧
    -Real.log (4261 / 31250) ≤ (1992515503 / 1000000000) := by
  have h := checkLog_sound (w := (7103 / 24147)) (n := 12)
    (lo := (30311057 / 50000000)) (hi := (606221141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8522) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8522) = 1/(4261 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1992515503 / 1000000000) (-3985031 / 2000000) (Real.log (4261 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (613878839 / 1000000000) ≤ -Real.log (31250 / 57737) ∧
    -Real.log (31250 / 57737) ≤ (15346971 / 25000000) := by
  have h := checkLog_sound (w := (26487 / 88987)) (n := 12)
    (lo := (613878839 / 1000000000)) (hi := (15346971 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57737 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57737 / 31250) = 1/(31250 / 57737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (613878839 / 1000000000) (15346971 / 25000000) (Real.log (57737 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57737 / 31250) = -Real.log (31250 / 57737) := by
    rw [show ((57737 / 31250) : ℝ) = ((31250 / 57737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1881141653 / 1000000000) ≤ -Real.log (4763 / 31250) ∧
    -Real.log (4763 / 31250) ≤ (235142707 / 125000000) := by
  have h := checkLog_sound (w := (6099 / 25151)) (n := 12)
    (lo := (494847293 / 1000000000)) (hi := (247423647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9526) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 9526) = 1/(4763 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-235142707 / 125000000) (-1881141653 / 1000000000) (Real.log (4763 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (616064171 / 1000000000) ≤ -Real.log (500000 / 925813) ∧
    -Real.log (500000 / 925813) ≤ (154016043 / 250000000) := by
  have h := checkLog_sound (w := (425813 / 1425813)) (n := 12)
    (lo := (616064171 / 1000000000)) (hi := (154016043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925813 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925813 / 500000) = 1/(500000 / 925813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (616064171 / 1000000000) (154016043 / 250000000) (Real.log (925813 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (925813 / 500000) = -Real.log (500000 / 925813) := by
    rw [show ((925813 / 500000) : ℝ) = ((500000 / 925813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (477004791 / 250000000) ≤ -Real.log (74187 / 500000) ∧
    -Real.log (74187 / 500000) ≤ (1908019167 / 1000000000) := by
  have h := checkLog_sound (w := (50813 / 199187)) (n := 12)
    (lo := (130431201 / 250000000)) (hi := (104344961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 74187) = 1/(74187 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1908019167 / 1000000000) (-477004791 / 250000000) (Real.log (74187 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (323816993 / 125000000) ≤ -Real.log (250000000000 / 3334229390681) ∧
    -Real.log (250000000000 / 3334229390681) ≤ (647633987 / 250000000) := by
  have h := checkLog_sound (w := (1334229390681 / 5334229390681)) (n := 12)
    (lo := (127773601 / 250000000)) (hi := (102218881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3334229390681 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3334229390681 / 2000000000000) = 1/(250000000000 / 3334229390681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (323816993 / 125000000) (647633987 / 250000000) (Real.log (3334229390681 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3334229390681 / 250000000000) = -Real.log (250000000000 / 3334229390681) := by
    rw [show ((3334229390681 / 250000000000) : ℝ) = ((250000000000 / 3334229390681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2615051357 / 1000000000) ≤ -Real.log (125000000000 / 1708489791129) ∧
    -Real.log (125000000000 / 1708489791129) ≤ (2615051361 / 1000000000) := by
  have h := checkLog_sound (w := (708489791129 / 2708489791129)) (n := 12)
    (lo := (535609817 / 1000000000)) (hi := (267804909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1708489791129 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1708489791129 / 1000000000000) = 1/(125000000000 / 1708489791129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2615051357 / 1000000000) (2615051361 / 1000000000) (Real.log (1708489791129 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1708489791129 / 125000000000) = -Real.log (125000000000 / 1708489791129) := by
    rw [show ((1708489791129 / 125000000000) : ℝ) = ((125000000000 / 1708489791129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (623755123 / 250000000) ≤ -Real.log (125000000000 / 1515247743019) ∧
    -Real.log (125000000000 / 1515247743019) ≤ (155938781 / 62500000) := by
  have h := checkLog_sound (w := (515247743019 / 2515247743019)) (n := 12)
    (lo := (51947369 / 125000000)) (hi := (415578953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515247743019 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1515247743019 / 1000000000000) = 1/(125000000000 / 1515247743019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (623755123 / 250000000) (155938781 / 62500000) (Real.log (1515247743019 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1515247743019 / 125000000000) = -Real.log (125000000000 / 1515247743019) := by
    rw [show ((1515247743019 / 125000000000) : ℝ) = ((125000000000 / 1515247743019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (315510417 / 125000000) ≤ -Real.log (250000000000 / 3119862644399) ∧
    -Real.log (250000000000 / 3119862644399) ≤ (126204167 / 50000000) := by
  have h := checkLog_sound (w := (1119862644399 / 5119862644399)) (n := 12)
    (lo := (111160449 / 250000000)) (hi := (444641797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3119862644399 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3119862644399 / 2000000000000) = 1/(250000000000 / 3119862644399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (315510417 / 125000000) (126204167 / 50000000) (Real.log (3119862644399 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3119862644399 / 250000000000) = -Real.log (250000000000 / 3119862644399) := by
    rw [show ((3119862644399 / 250000000000) : ℝ) = ((250000000000 / 3119862644399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0201
