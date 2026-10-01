import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0469
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

theorem reflection_log_1_neg : (183663429 / 1000000000) ≤ -Real.log (20480 / 24609) ∧
    -Real.log (20480 / 24609) ≤ (18366343 / 100000000) := by
  have h := checkLog_sound (w := (4129 / 45089)) (n := 12)
    (lo := (183663429 / 1000000000)) (hi := (18366343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24609 / 20480) = 1/(20480 / 24609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (183663429 / 1000000000) (18366343 / 100000000) (Real.log (24609 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24609 / 20480) = -Real.log (20480 / 24609) := by
    rw [show ((24609 / 20480) : ℝ) = ((20480 / 24609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112579871 / 500000000) ≤ -Real.log (16351 / 20480) ∧
    -Real.log (16351 / 20480) ≤ (225159743 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 36831)) (n := 12)
    (lo := (112579871 / 500000000)) (hi := (225159743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16351) = 1/(16351 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-225159743 / 1000000000) (-112579871 / 500000000) (Real.log (16351 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (36708303 / 200000000) ≤ -Real.log (10240 / 12303) ∧
    -Real.log (10240 / 12303) ≤ (45885379 / 250000000) := by
  have h := checkLog_sound (w := (2063 / 22543)) (n := 12)
    (lo := (36708303 / 200000000)) (hi := (45885379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12303 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12303 / 10240) = 1/(10240 / 12303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (36708303 / 200000000) (45885379 / 250000000) (Real.log (12303 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12303 / 10240) = -Real.log (10240 / 12303) := by
    rw [show ((12303 / 10240) : ℝ) = ((10240 / 12303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56244071 / 250000000) ≤ -Real.log (8177 / 10240) ∧
    -Real.log (8177 / 10240) ≤ (44995257 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 18417)) (n := 12)
    (lo := (56244071 / 250000000)) (hi := (44995257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8177) = 1/(8177 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44995257 / 200000000) (-56244071 / 250000000) (Real.log (8177 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10586609 / 31250000) ≤ -Real.log (10240 / 14369) ∧
    -Real.log (10240 / 14369) ≤ (338771489 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 24609)) (n := 12)
    (lo := (10586609 / 31250000)) (hi := (338771489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14369 / 10240) = 1/(10240 / 14369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10586609 / 31250000) (338771489 / 1000000000) (Real.log (14369 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14369 / 10240) = -Real.log (10240 / 14369) := by
    rw [show ((14369 / 10240) : ℝ) = ((10240 / 14369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (516211193 / 1000000000) ≤ -Real.log (6111 / 10240) ∧
    -Real.log (6111 / 10240) ≤ (258105597 / 500000000) := by
  have h := checkLog_sound (w := (4129 / 16351)) (n := 12)
    (lo := (516211193 / 1000000000)) (hi := (258105597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6111) = 1/(6111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258105597 / 500000000) (-516211193 / 1000000000) (Real.log (6111 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84640671 / 250000000) ≤ -Real.log (5120 / 7183) ∧
    -Real.log (5120 / 7183) ≤ (67712537 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 12303)) (n := 12)
    (lo := (84640671 / 250000000)) (hi := (67712537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7183 / 5120) = 1/(5120 / 7183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84640671 / 250000000) (67712537 / 200000000) (Real.log (7183 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7183 / 5120) = -Real.log (5120 / 7183) := by
    rw [show ((7183 / 5120) : ℝ) = ((5120 / 7183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128930099 / 250000000) ≤ -Real.log (3057 / 5120) ∧
    -Real.log (3057 / 5120) ≤ (515720397 / 1000000000) := by
  have h := checkLog_sound (w := (2063 / 8177)) (n := 12)
    (lo := (128930099 / 250000000)) (hi := (515720397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3057) = 1/(3057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-515720397 / 1000000000) (-128930099 / 250000000) (Real.log (3057 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252300719 / 1000000000) ≤ -Real.log (1000000 / 1286983) ∧
    -Real.log (1000000 / 1286983) ≤ (3153759 / 12500000) := by
  have h := checkLog_sound (w := (286983 / 2286983)) (n := 12)
    (lo := (252300719 / 1000000000)) (hi := (3153759 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286983 / 1000000) = 1/(1000000 / 1286983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252300719 / 1000000000) (3153759 / 12500000) (Real.log (1286983 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286983 / 1000000) = -Real.log (1000000 / 1286983) := by
    rw [show ((1286983 / 1000000) : ℝ) = ((1000000 / 1286983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67650003 / 200000000) ≤ -Real.log (713017 / 1000000) ∧
    -Real.log (713017 / 1000000) ≤ (10570313 / 31250000) := by
  have h := checkLog_sound (w := (286983 / 1713017)) (n := 12)
    (lo := (67650003 / 200000000)) (hi := (10570313 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713017) = 1/(713017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10570313 / 31250000) (-67650003 / 200000000) (Real.log (713017 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (252466209 / 1000000000) ≤ -Real.log (250000 / 321799) ∧
    -Real.log (250000 / 321799) ≤ (25246621 / 100000000) := by
  have h := checkLog_sound (w := (71799 / 571799)) (n := 12)
    (lo := (252466209 / 1000000000)) (hi := (25246621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321799 / 250000) = 1/(250000 / 321799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (252466209 / 1000000000) (25246621 / 100000000) (Real.log (321799 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (321799 / 250000) = -Real.log (250000 / 321799) := by
    rw [show ((321799 / 250000) : ℝ) = ((250000 / 321799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (338548791 / 1000000000) ≤ -Real.log (178201 / 250000) ∧
    -Real.log (178201 / 250000) ≤ (42318599 / 125000000) := by
  have h := checkLog_sound (w := (71799 / 428201)) (n := 12)
    (lo := (338548791 / 1000000000)) (hi := (42318599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178201) = 1/(178201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42318599 / 125000000) (-338548791 / 1000000000) (Real.log (178201 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37737583 / 200000000) ≤ -Real.log (62500 / 75479) ∧
    -Real.log (62500 / 75479) ≤ (47171979 / 250000000) := by
  have h := checkLog_sound (w := (12979 / 137979)) (n := 12)
    (lo := (37737583 / 200000000)) (hi := (47171979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75479 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75479 / 62500) = 1/(62500 / 75479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37737583 / 200000000) (47171979 / 250000000) (Real.log (75479 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75479 / 62500) = -Real.log (62500 / 75479) := by
    rw [show ((75479 / 62500) : ℝ) = ((62500 / 75479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (116384867 / 500000000) ≤ -Real.log (49521 / 62500) ∧
    -Real.log (49521 / 62500) ≤ (46553947 / 200000000) := by
  have h := checkLog_sound (w := (12979 / 112021)) (n := 12)
    (lo := (116384867 / 500000000)) (hi := (46553947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49521) = 1/(49521 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46553947 / 200000000) (-116384867 / 500000000) (Real.log (49521 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188821221 / 1000000000) ≤ -Real.log (40000 / 48313) ∧
    -Real.log (40000 / 48313) ≤ (94410611 / 500000000) := by
  have h := checkLog_sound (w := (8313 / 88313)) (n := 12)
    (lo := (188821221 / 1000000000)) (hi := (94410611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48313 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48313 / 40000) = 1/(40000 / 48313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188821221 / 1000000000) (94410611 / 500000000) (Real.log (48313 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48313 / 40000) = -Real.log (40000 / 48313) := by
    rw [show ((48313 / 40000) : ℝ) = ((40000 / 48313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (232972951 / 1000000000) ≤ -Real.log (31687 / 40000) ∧
    -Real.log (31687 / 40000) ≤ (29121619 / 125000000) := by
  have h := checkLog_sound (w := (8313 / 71687)) (n := 12)
    (lo := (232972951 / 1000000000)) (hi := (29121619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31687) = 1/(31687 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-29121619 / 125000000) (-232972951 / 1000000000) (Real.log (31687 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118110147 / 200000000) ≤ -Real.log (5000000000 / 9024911047) ∧
    -Real.log (5000000000 / 9024911047) ≤ (36909421 / 62500000) := by
  have h := checkLog_sound (w := (4024911047 / 14024911047)) (n := 12)
    (lo := (118110147 / 200000000)) (hi := (36909421 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9024911047 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9024911047 / 5000000000) = 1/(5000000000 / 9024911047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118110147 / 200000000) (36909421 / 62500000) (Real.log (9024911047 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9024911047 / 5000000000) = -Real.log (5000000000 / 9024911047) := by
    rw [show ((9024911047 / 5000000000) : ℝ) = ((5000000000 / 9024911047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (118203 / 200000) ≤ -Real.log (500000000000 / 902910196913) ∧
    -Real.log (500000000000 / 902910196913) ≤ (591015001 / 1000000000) := by
  have h := checkLog_sound (w := (402910196913 / 1402910196913)) (n := 12)
    (lo := (118203 / 200000)) (hi := (591015001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902910196913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902910196913 / 500000000000) = 1/(500000000000 / 902910196913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (118203 / 200000) (591015001 / 1000000000) (Real.log (902910196913 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (902910196913 / 500000000000) = -Real.log (500000000000 / 902910196913) := by
    rw [show ((902910196913 / 500000000000) : ℝ) = ((500000000000 / 902910196913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421457649 / 1000000000) ≤ -Real.log (62500000000 / 95261353769) ∧
    -Real.log (62500000000 / 95261353769) ≤ (8429153 / 20000000) := by
  have h := checkLog_sound (w := (32761353769 / 157761353769)) (n := 12)
    (lo := (421457649 / 1000000000)) (hi := (8429153 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95261353769 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95261353769 / 62500000000) = 1/(62500000000 / 95261353769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421457649 / 1000000000) (8429153 / 20000000) (Real.log (95261353769 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (95261353769 / 62500000000) = -Real.log (62500000000 / 95261353769) := by
    rw [show ((95261353769 / 62500000000) : ℝ) = ((62500000000 / 95261353769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421794173 / 1000000000) ≤ -Real.log (50000000000 / 76234733487) ∧
    -Real.log (50000000000 / 76234733487) ≤ (210897087 / 500000000) := by
  have h := checkLog_sound (w := (26234733487 / 126234733487)) (n := 12)
    (lo := (421794173 / 1000000000)) (hi := (210897087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76234733487 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76234733487 / 50000000000) = 1/(50000000000 / 76234733487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421794173 / 1000000000) (210897087 / 500000000) (Real.log (76234733487 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76234733487 / 50000000000) = -Real.log (50000000000 / 76234733487) := by
    rw [show ((76234733487 / 50000000000) : ℝ) = ((50000000000 / 76234733487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0469
