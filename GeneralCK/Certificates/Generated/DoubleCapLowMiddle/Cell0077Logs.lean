import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0077
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

theorem reflection_log_1_neg : (675760577 / 1000000000) ≤ -Real.log (10240 / 20127) ∧
    -Real.log (10240 / 20127) ≤ (337880289 / 500000000) := by
  have h := checkLog_sound (w := (9887 / 30367)) (n := 12)
    (lo := (675760577 / 1000000000)) (hi := (337880289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20127 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20127 / 10240) = 1/(10240 / 20127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675760577 / 1000000000) (337880289 / 500000000) (Real.log (20127 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20127 / 10240) = -Real.log (10240 / 20127) := by
    rw [show ((20127 / 10240) : ℝ) = ((10240 / 20127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3367588839 / 1000000000) ≤ -Real.log (353 / 10240) ∧
    -Real.log (353 / 10240) ≤ (841897211 / 250000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 353) = 1/(353 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-841897211 / 250000000) (-3367588839 / 1000000000) (Real.log (353 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337785879 / 500000000) ≤ -Real.log (6400 / 12577) ∧
    -Real.log (6400 / 12577) ≤ (675571759 / 1000000000) := by
  have h := checkLog_sound (w := (6177 / 18977)) (n := 12)
    (lo := (337785879 / 500000000)) (hi := (675571759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12577 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12577 / 6400) = 1/(6400 / 12577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337785879 / 500000000) (675571759 / 1000000000) (Real.log (12577 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12577 / 6400) = -Real.log (6400 / 12577) := by
    rw [show ((12577 / 6400) : ℝ) = ((6400 / 12577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (671376299 / 200000000) ≤ -Real.log (223 / 6400) ∧
    -Real.log (223 / 6400) ≤ (6713763 / 2000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 223) = 1/(223 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6713763 / 2000000) (-671376299 / 200000000) (Real.log (223 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (658066323 / 1000000000) ≤ -Real.log (5120 / 9887) ∧
    -Real.log (5120 / 9887) ≤ (164516581 / 250000000) := by
  have h := checkLog_sound (w := (4767 / 15007)) (n := 12)
    (lo := (658066323 / 1000000000)) (hi := (164516581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9887 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9887 / 5120) = 1/(5120 / 9887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (658066323 / 1000000000) (164516581 / 250000000) (Real.log (9887 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9887 / 5120) = -Real.log (5120 / 9887) := by
    rw [show ((9887 / 5120) : ℝ) = ((5120 / 9887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2674441659 / 1000000000) ≤ -Real.log (353 / 5120) ∧
    -Real.log (353 / 5120) ≤ (2674441663 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 353) = 1/(353 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2674441663 / 1000000000) (-2674441659 / 1000000000) (Real.log (353 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (328840953 / 500000000) ≤ -Real.log (3200 / 6177) ∧
    -Real.log (3200 / 6177) ≤ (657681907 / 1000000000) := by
  have h := checkLog_sound (w := (2977 / 9377)) (n := 12)
    (lo := (328840953 / 500000000)) (hi := (657681907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 3200) = 1/(3200 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (328840953 / 500000000) (657681907 / 1000000000) (Real.log (6177 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6177 / 3200) = -Real.log (3200 / 6177) := by
    rw [show ((6177 / 3200) : ℝ) = ((3200 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (532746863 / 200000000) ≤ -Real.log (223 / 3200) ∧
    -Real.log (223 / 3200) ≤ (2663734319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 623)) (n := 12)
    (lo := (23371711 / 40000000)) (hi := (73036597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 223) = 1/(223 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2663734319 / 1000000000) (-532746863 / 200000000) (Real.log (223 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678585167 / 1000000000) ≤ -Real.log (1000000 / 1971087) ∧
    -Real.log (1000000 / 1971087) ≤ (42411573 / 62500000) := by
  have h := checkLog_sound (w := (971087 / 2971087)) (n := 12)
    (lo := (678585167 / 1000000000)) (hi := (42411573 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971087 / 1000000) = 1/(1000000 / 1971087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678585167 / 1000000000) (42411573 / 62500000) (Real.log (1971087 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971087 / 1000000) = -Real.log (1000000 / 1971087) := by
    rw [show ((1971087 / 1000000) : ℝ) = ((1000000 / 1971087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (708692791 / 200000000) ≤ -Real.log (28913 / 1000000) ∧
    -Real.log (28913 / 1000000) ≤ (3543463961 / 1000000000) := by
  have h := checkLog_sound (w := (2337 / 60163)) (n := 12)
    (lo := (15545611 / 200000000)) (hi := (9716007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28913) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28913) = 1/(28913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3543463961 / 1000000000) (-708692791 / 200000000) (Real.log (28913 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135746761 / 200000000) ≤ -Real.log (50000 / 98569) ∧
    -Real.log (50000 / 98569) ≤ (339366903 / 500000000) := by
  have h := checkLog_sound (w := (48569 / 148569)) (n := 12)
    (lo := (135746761 / 200000000)) (hi := (339366903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98569 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98569 / 50000) = 1/(50000 / 98569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135746761 / 200000000) (339366903 / 500000000) (Real.log (98569 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98569 / 50000) = -Real.log (50000 / 98569) := by
    rw [show ((98569 / 50000) : ℝ) = ((50000 / 98569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1776824751 / 500000000) ≤ -Real.log (1431 / 50000) ∧
    -Real.log (1431 / 50000) ≤ (888412377 / 250000000) := by
  have h := checkLog_sound (w := (263 / 5987)) (n := 12)
    (lo := (43956801 / 500000000)) (hi := (87913603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2862) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2862) = 1/(1431 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-888412377 / 250000000) (-1776824751 / 500000000) (Real.log (1431 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (678477099 / 1000000000) ≤ -Real.log (500000 / 985437) ∧
    -Real.log (500000 / 985437) ≤ (6784771 / 10000000) := by
  have h := checkLog_sound (w := (485437 / 1485437)) (n := 12)
    (lo := (678477099 / 1000000000)) (hi := (6784771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985437 / 500000) = 1/(500000 / 985437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (678477099 / 1000000000) (6784771 / 10000000) (Real.log (985437 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (985437 / 500000) = -Real.log (500000 / 985437) := by
    rw [show ((985437 / 500000) : ℝ) = ((500000 / 985437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353612403 / 100000000) ≤ -Real.log (14563 / 500000) ∧
    -Real.log (14563 / 500000) ≤ (884031009 / 250000000) := by
  have h := checkLog_sound (w := (531 / 15094)) (n := 12)
    (lo := (7038813 / 100000000)) (hi := (70388131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14563) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14563) = 1/(14563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-884031009 / 250000000) (-353612403 / 100000000) (Real.log (14563 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678628289 / 1000000000) ≤ -Real.log (250000 / 492793) ∧
    -Real.log (250000 / 492793) ≤ (67862829 / 100000000) := by
  have h := checkLog_sound (w := (242793 / 742793)) (n := 12)
    (lo := (678628289 / 1000000000)) (hi := (67862829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492793 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492793 / 250000) = 1/(250000 / 492793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678628289 / 1000000000) (67862829 / 100000000) (Real.log (492793 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (492793 / 250000) = -Real.log (250000 / 492793) := by
    rw [show ((492793 / 250000) : ℝ) = ((250000 / 492793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3546408139 / 1000000000) ≤ -Real.log (7207 / 250000) ∧
    -Real.log (7207 / 250000) ≤ (709281629 / 200000000) := by
  have h := checkLog_sound (w := (1211 / 30039)) (n := 12)
    (lo := (80672239 / 1000000000)) (hi := (1008403 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14414) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14414) = 1/(7207 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-709281629 / 200000000) (-3546408139 / 1000000000) (Real.log (7207 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4222049121 / 1000000000) ≤ -Real.log (100000000000 / 6817303635043) ∧
    -Real.log (100000000000 / 6817303635043) ≤ (527756141 / 125000000) := by
  have h := checkLog_sound (w := (417303635043 / 13217303635043)) (n := 12)
    (lo := (63166041 / 1000000000)) (hi := (31583021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817303635043 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6817303635043 / 6400000000000) = 1/(100000000000 / 6817303635043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4222049121 / 1000000000) (527756141 / 125000000) (Real.log (6817303635043 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6817303635043 / 100000000000) = -Real.log (100000000000 / 6817303635043) := by
    rw [show ((6817303635043 / 100000000000) : ℝ) = ((100000000000 / 6817303635043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2116191653 / 500000000) ≤ -Real.log (500000000000 / 34440600978337) ∧
    -Real.log (500000000000 / 34440600978337) ≤ (4232383313 / 1000000000) := by
  have h := checkLog_sound (w := (2440600978337 / 66440600978337)) (n := 12)
    (lo := (36750113 / 500000000)) (hi := (73500227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34440600978337 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34440600978337 / 32000000000000) = 1/(500000000000 / 34440600978337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2116191653 / 500000000) (4232383313 / 1000000000) (Real.log (34440600978337 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34440600978337 / 500000000000) = -Real.log (500000000000 / 34440600978337) := by
    rw [show ((34440600978337 / 500000000000) : ℝ) = ((500000000000 / 34440600978337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (526825141 / 125000000) ≤ -Real.log (500000000000 / 33833585112957) ∧
    -Real.log (500000000000 / 33833585112957) ≤ (842920227 / 200000000) := by
  have h := checkLog_sound (w := (1833585112957 / 65833585112957)) (n := 12)
    (lo := (1741189 / 31250000)) (hi := (55718049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33833585112957 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33833585112957 / 32000000000000) = 1/(500000000000 / 33833585112957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (526825141 / 125000000) (842920227 / 200000000) (Real.log (33833585112957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (33833585112957 / 500000000000) = -Real.log (500000000000 / 33833585112957) := by
    rw [show ((33833585112957 / 500000000000) : ℝ) = ((500000000000 / 33833585112957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1056259107 / 250000000) ≤ -Real.log (250000000000 / 17094248647149) ∧
    -Real.log (250000000000 / 17094248647149) ≤ (845007287 / 200000000) := by
  have h := checkLog_sound (w := (1094248647149 / 33094248647149)) (n := 12)
    (lo := (16538337 / 250000000)) (hi := (66153349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17094248647149 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17094248647149 / 16000000000000) = 1/(250000000000 / 17094248647149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1056259107 / 250000000) (845007287 / 200000000) (Real.log (17094248647149 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17094248647149 / 250000000000) = -Real.log (250000000000 / 17094248647149) := by
    rw [show ((17094248647149 / 250000000000) : ℝ) = ((250000000000 / 17094248647149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0077
