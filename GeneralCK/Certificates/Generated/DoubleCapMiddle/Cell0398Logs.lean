import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0398
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

theorem reflection_log_1_neg : (100353103 / 500000000) ≤ -Real.log (2560 / 3129) ∧
    -Real.log (2560 / 3129) ≤ (200706207 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 5689)) (n := 12)
    (lo := (100353103 / 500000000)) (hi := (200706207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3129 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3129 / 2560) = 1/(2560 / 3129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (100353103 / 500000000) (200706207 / 1000000000) (Real.log (3129 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3129 / 2560) = -Real.log (2560 / 3129) := by
    rw [show ((3129 / 2560) : ℝ) = ((2560 / 3129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (251370233 / 1000000000) ≤ -Real.log (1991 / 2560) ∧
    -Real.log (1991 / 2560) ≤ (125685117 / 500000000) := by
  have h := checkLog_sound (w := (569 / 4551)) (n := 12)
    (lo := (251370233 / 1000000000)) (hi := (125685117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1991) = 1/(1991 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125685117 / 500000000) (-251370233 / 1000000000) (Real.log (1991 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50116621 / 250000000) ≤ -Real.log (10240 / 12513) ∧
    -Real.log (10240 / 12513) ≤ (40093297 / 200000000) := by
  have h := checkLog_sound (w := (2273 / 22753)) (n := 12)
    (lo := (50116621 / 250000000)) (hi := (40093297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12513 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12513 / 10240) = 1/(10240 / 12513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50116621 / 250000000) (40093297 / 200000000) (Real.log (12513 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12513 / 10240) = -Real.log (10240 / 12513) := by
    rw [show ((12513 / 10240) : ℝ) = ((10240 / 12513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (250993609 / 1000000000) ≤ -Real.log (7967 / 10240) ∧
    -Real.log (7967 / 10240) ≤ (25099361 / 100000000) := by
  have h := checkLog_sound (w := (2273 / 18207)) (n := 12)
    (lo := (250993609 / 1000000000)) (hi := (25099361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7967) = 1/(7967 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-25099361 / 100000000) (-250993609 / 1000000000) (Real.log (7967 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183892437 / 500000000) ≤ -Real.log (1280 / 1849) ∧
    -Real.log (1280 / 1849) ≤ (2942279 / 8000000) := by
  have h := checkLog_sound (w := (569 / 3129)) (n := 12)
    (lo := (183892437 / 500000000)) (hi := (2942279 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1849 / 1280) = 1/(1280 / 1849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183892437 / 500000000) (2942279 / 8000000) (Real.log (1849 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1849 / 1280) = -Real.log (1280 / 1849) := by
    rw [show ((1849 / 1280) : ℝ) = ((1280 / 1849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (587942927 / 1000000000) ≤ -Real.log (711 / 1280) ∧
    -Real.log (711 / 1280) ≤ (36746433 / 62500000) := by
  have h := checkLog_sound (w := (569 / 1991)) (n := 12)
    (lo := (587942927 / 1000000000)) (hi := (36746433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 711) = 1/(711 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-36746433 / 62500000) (-587942927 / 1000000000) (Real.log (711 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (367379167 / 1000000000) ≤ -Real.log (5120 / 7393) ∧
    -Real.log (5120 / 7393) ≤ (11480599 / 31250000) := by
  have h := checkLog_sound (w := (2273 / 12513)) (n := 12)
    (lo := (367379167 / 1000000000)) (hi := (11480599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7393 / 5120) = 1/(5120 / 7393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (367379167 / 1000000000) (11480599 / 31250000) (Real.log (7393 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7393 / 5120) = -Real.log (5120 / 7393) := by
    rw [show ((7393 / 5120) : ℝ) = ((5120 / 7393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58688863 / 100000000) ≤ -Real.log (2847 / 5120) ∧
    -Real.log (2847 / 5120) ≤ (586888631 / 1000000000) := by
  have h := checkLog_sound (w := (2273 / 7967)) (n := 12)
    (lo := (58688863 / 100000000)) (hi := (586888631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2847) = 1/(2847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-586888631 / 1000000000) (-58688863 / 100000000) (Real.log (2847 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27515139 / 100000000) ≤ -Real.log (100000 / 131673) ∧
    -Real.log (100000 / 131673) ≤ (275151391 / 1000000000) := by
  have h := checkLog_sound (w := (31673 / 231673)) (n := 12)
    (lo := (27515139 / 100000000)) (hi := (275151391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131673 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131673 / 100000) = 1/(100000 / 131673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27515139 / 100000000) (275151391 / 1000000000) (Real.log (131673 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (131673 / 100000) = -Real.log (100000 / 131673) := by
    rw [show ((131673 / 100000) : ℝ) = ((100000 / 131673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190432591 / 500000000) ≤ -Real.log (68327 / 100000) ∧
    -Real.log (68327 / 100000) ≤ (380865183 / 1000000000) := by
  have h := checkLog_sound (w := (31673 / 168327)) (n := 12)
    (lo := (190432591 / 500000000)) (hi := (380865183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68327) = 1/(68327 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-380865183 / 1000000000) (-190432591 / 500000000) (Real.log (68327 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (440761 / 1600000) ≤ -Real.log (1000000 / 1317157) ∧
    -Real.log (1000000 / 1317157) ≤ (137737813 / 500000000) := by
  have h := checkLog_sound (w := (317157 / 2317157)) (n := 12)
    (lo := (440761 / 1600000)) (hi := (137737813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317157 / 1000000) = 1/(1000000 / 1317157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (440761 / 1600000) (137737813 / 500000000) (Real.log (1317157 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1317157 / 1000000) = -Real.log (1000000 / 1317157) := by
    rw [show ((1317157 / 1000000) : ℝ) = ((1000000 / 1317157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (190745157 / 500000000) ≤ -Real.log (682843 / 1000000) ∧
    -Real.log (682843 / 1000000) ≤ (76298063 / 200000000) := by
  have h := checkLog_sound (w := (317157 / 1682843)) (n := 12)
    (lo := (190745157 / 500000000)) (hi := (76298063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682843) = 1/(682843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76298063 / 200000000) (-190745157 / 500000000) (Real.log (682843 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51826499 / 250000000) ≤ -Real.log (1000000 / 1230359) ∧
    -Real.log (1000000 / 1230359) ≤ (207305997 / 1000000000) := by
  have h := checkLog_sound (w := (230359 / 2230359)) (n := 12)
    (lo := (51826499 / 250000000)) (hi := (207305997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230359 / 1000000) = 1/(1000000 / 1230359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51826499 / 250000000) (207305997 / 1000000000) (Real.log (1230359 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1230359 / 1000000) = -Real.log (1000000 / 1230359) := by
    rw [show ((1230359 / 1000000) : ℝ) = ((1000000 / 1230359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (130915553 / 500000000) ≤ -Real.log (769641 / 1000000) ∧
    -Real.log (769641 / 1000000) ≤ (261831107 / 1000000000) := by
  have h := checkLog_sound (w := (230359 / 1769641)) (n := 12)
    (lo := (130915553 / 500000000)) (hi := (261831107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769641) = 1/(769641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-261831107 / 1000000000) (-130915553 / 500000000) (Real.log (769641 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103786681 / 500000000) ≤ -Real.log (31250 / 38459) ∧
    -Real.log (31250 / 38459) ≤ (207573363 / 1000000000) := by
  have h := checkLog_sound (w := (7209 / 69709)) (n := 12)
    (lo := (103786681 / 500000000)) (hi := (207573363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38459 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38459 / 31250) = 1/(31250 / 38459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103786681 / 500000000) (207573363 / 1000000000) (Real.log (38459 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38459 / 31250) = -Real.log (31250 / 38459) := by
    rw [show ((38459 / 31250) : ℝ) = ((31250 / 38459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26225867 / 100000000) ≤ -Real.log (24041 / 31250) ∧
    -Real.log (24041 / 31250) ≤ (262258671 / 1000000000) := by
  have h := checkLog_sound (w := (7209 / 55291)) (n := 12)
    (lo := (26225867 / 100000000)) (hi := (262258671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24041) = 1/(24041 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-262258671 / 1000000000) (-26225867 / 100000000) (Real.log (24041 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (656016573 / 1000000000) ≤ -Real.log (500000000000 / 963550280269) ∧
    -Real.log (500000000000 / 963550280269) ≤ (328008287 / 500000000) := by
  have h := checkLog_sound (w := (463550280269 / 1463550280269)) (n := 12)
    (lo := (656016573 / 1000000000)) (hi := (328008287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963550280269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963550280269 / 500000000000) = 1/(500000000000 / 963550280269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (656016573 / 1000000000) (328008287 / 500000000) (Real.log (963550280269 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (963550280269 / 500000000000) = -Real.log (500000000000 / 963550280269) := by
    rw [show ((963550280269 / 500000000000) : ℝ) = ((500000000000 / 963550280269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32848297 / 50000000) ≤ -Real.log (31250000000 / 60279092339) ∧
    -Real.log (31250000000 / 60279092339) ≤ (656965941 / 1000000000) := by
  have h := checkLog_sound (w := (29029092339 / 91529092339)) (n := 12)
    (lo := (32848297 / 50000000)) (hi := (656965941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60279092339 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60279092339 / 31250000000) = 1/(31250000000 / 60279092339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32848297 / 50000000) (656965941 / 1000000000) (Real.log (60279092339 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (60279092339 / 31250000000) = -Real.log (31250000000 / 60279092339) := by
    rw [show ((60279092339 / 31250000000) : ℝ) = ((31250000000 / 60279092339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (469137103 / 1000000000) ≤ -Real.log (250000000000 / 399653539767) ∧
    -Real.log (250000000000 / 399653539767) ≤ (29321069 / 62500000) := by
  have h := checkLog_sound (w := (149653539767 / 649653539767)) (n := 12)
    (lo := (469137103 / 1000000000)) (hi := (29321069 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399653539767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399653539767 / 250000000000) = 1/(250000000000 / 399653539767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (469137103 / 1000000000) (29321069 / 62500000) (Real.log (399653539767 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (399653539767 / 250000000000) = -Real.log (250000000000 / 399653539767) := by
    rw [show ((399653539767 / 250000000000) : ℝ) = ((250000000000 / 399653539767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14682251 / 31250000) ≤ -Real.log (15625000000 / 24995710453) ∧
    -Real.log (15625000000 / 24995710453) ≤ (469832033 / 1000000000) := by
  have h := checkLog_sound (w := (9370710453 / 40620710453)) (n := 12)
    (lo := (14682251 / 31250000)) (hi := (469832033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24995710453 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24995710453 / 15625000000) = 1/(15625000000 / 24995710453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14682251 / 31250000) (469832033 / 1000000000) (Real.log (24995710453 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24995710453 / 15625000000) = -Real.log (15625000000 / 24995710453) := by
    rw [show ((24995710453 / 15625000000) : ℝ) = ((15625000000 / 24995710453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0398
