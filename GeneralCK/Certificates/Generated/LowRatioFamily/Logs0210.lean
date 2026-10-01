import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13440_neg : (480582589 / 1000000000) ≤ -Real.log (618423 / 1000000) ∧
    -Real.log (618423 / 1000000) ≤ (48058259 / 100000000) := by
  have h := checkLog_sound (w := (381577 / 1618423)) (n := 12)
    (lo := (480582589 / 1000000000)) (hi := (48058259 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618423) = 1/(618423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13440 : Bounds (-48058259 / 100000000) (-480582589 / 1000000000) (Real.log (618423 / 1000000)) := by
  have h := reflection_log_13440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13441_neg : (157356989 / 1000000000) ≤ -Real.log (854398993071 / 1000000000000) ∧
    -Real.log (854398993071 / 1000000000000) ≤ (15735699 / 100000000) := by
  have h := checkLog_sound (w := (145601006929 / 1854398993071)) (n := 12)
    (lo := (157356989 / 1000000000)) (hi := (15735699 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 854398993071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 854398993071) = 1/(854398993071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13441 : Bounds (-15735699 / 100000000) (-157356989 / 1000000000) (Real.log (854398993071 / 1000000000000)) := by
  have h := reflection_log_13441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13442_neg : (6200783 / 40000000) ≤ -Real.log (53524900831 / 62500000000) ∧
    -Real.log (53524900831 / 62500000000) ≤ (19377447 / 125000000) := by
  have h := checkLog_sound (w := (8975099169 / 116024900831)) (n := 12)
    (lo := (6200783 / 40000000)) (hi := (19377447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53524900831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53524900831) = 1/(53524900831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13442 : Bounds (-19377447 / 125000000) (-6200783 / 40000000) (Real.log (53524900831 / 62500000000)) := by
  have h := reflection_log_13442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13443_neg : (797661353 / 1000000000) ≤ -Real.log (500000000000 / 1110171128987) ∧
    -Real.log (500000000000 / 1110171128987) ≤ (159532271 / 200000000) := by
  have h := checkLog_sound (w := (110171128987 / 2110171128987)) (n := 12)
    (lo := (104514173 / 1000000000)) (hi := (52257087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110171128987 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110171128987 / 1000000000000) = 1/(500000000000 / 1110171128987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13443 : Bounds (797661353 / 1000000000) (159532271 / 200000000) (Real.log (1110171128987 / 500000000000)) := by
  have h := reflection_log_13443_neg
  have he : Real.log (1110171128987 / 500000000000) = -Real.log (500000000000 / 1110171128987) := by
    rw [show ((1110171128987 / 500000000000) : ℝ) = ((500000000000 / 1110171128987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13444_neg : (803808189 / 1000000000) ≤ -Real.log (100000000000 / 223403236943) ∧
    -Real.log (100000000000 / 223403236943) ≤ (803808191 / 1000000000) := by
  have h := checkLog_sound (w := (23403236943 / 423403236943)) (n := 12)
    (lo := (110661009 / 1000000000)) (hi := (11066101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223403236943 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(223403236943 / 200000000000) = 1/(100000000000 / 223403236943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13444 : Bounds (803808189 / 1000000000) (803808191 / 1000000000) (Real.log (223403236943 / 100000000000)) := by
  have h := reflection_log_13444_neg
  have he : Real.log (223403236943 / 100000000000) = -Real.log (100000000000 / 223403236943) := by
    rw [show ((223403236943 / 100000000000) : ℝ) = ((100000000000 / 223403236943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13445_neg : (1692099003 / 1000000000) ≤ -Real.log (500000000000 / 2715434083601) ∧
    -Real.log (500000000000 / 2715434083601) ≤ (846049503 / 500000000) := by
  have h := checkLog_sound (w := (715434083601 / 4715434083601)) (n := 12)
    (lo := (305804643 / 1000000000)) (hi := (76451161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2715434083601 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2715434083601 / 2000000000000) = 1/(500000000000 / 2715434083601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13445 : Bounds (1692099003 / 1000000000) (846049503 / 500000000) (Real.log (2715434083601 / 500000000000)) := by
  have h := reflection_log_13445_neg
  have he : Real.log (2715434083601 / 500000000000) = -Real.log (500000000000 / 2715434083601) := by
    rw [show ((2715434083601 / 500000000000) : ℝ) = ((500000000000 / 2715434083601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13446_neg : (425891689 / 250000000) ≤ -Real.log (250000000000 / 1373376623377) ∧
    -Real.log (250000000000 / 1373376623377) ≤ (1703566759 / 1000000000) := by
  have h := checkLog_sound (w := (373376623377 / 2373376623377)) (n := 12)
    (lo := (79318099 / 250000000)) (hi := (317272397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373376623377 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1373376623377 / 1000000000000) = 1/(250000000000 / 1373376623377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13446 : Bounds (425891689 / 250000000) (1703566759 / 1000000000) (Real.log (1373376623377 / 250000000000)) := by
  have h := reflection_log_13446_neg
  have he : Real.log (1373376623377 / 250000000000) = -Real.log (250000000000 / 1373376623377) := by
    rw [show ((1373376623377 / 250000000000) : ℝ) = ((250000000000 / 1373376623377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13447_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13447 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_13447_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13448_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13448 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_13448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13449_neg : (347379 / 500000000) ≤ -Real.log (200000 / 200139) ∧
    -Real.log (200000 / 200139) ≤ (694759 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 400139)) (n := 12)
    (lo := (347379 / 500000000)) (hi := (694759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200139 / 200000) = 1/(200000 / 200139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13449 : Bounds (347379 / 500000000) (694759 / 1000000000) (Real.log (200139 / 200000)) := by
  have h := reflection_log_13449_neg
  have he : Real.log (200139 / 200000) = -Real.log (200000 / 200139) := by
    rw [show ((200139 / 200000) : ℝ) = ((200000 / 200139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13450_neg : (695241 / 1000000000) ≤ -Real.log (199861 / 200000) ∧
    -Real.log (199861 / 200000) ≤ (347621 / 500000000) := by
  have h := checkLog_sound (w := (139 / 399861)) (n := 12)
    (lo := (695241 / 1000000000)) (hi := (347621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199861) = 1/(199861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13450 : Bounds (-347621 / 500000000) (-695241 / 1000000000) (Real.log (199861 / 200000)) := by
  have h := reflection_log_13450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13451_neg : (32278253 / 100000000) ≤ -Real.log (200000 / 276193) ∧
    -Real.log (200000 / 276193) ≤ (322782531 / 1000000000) := by
  have h := checkLog_sound (w := (76193 / 476193)) (n := 12)
    (lo := (32278253 / 100000000)) (hi := (322782531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276193 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(276193 / 200000) = 1/(200000 / 276193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13451 : Bounds (32278253 / 100000000) (322782531 / 1000000000) (Real.log (276193 / 200000)) := by
  have h := reflection_log_13451_neg
  have he : Real.log (276193 / 200000) = -Real.log (200000 / 276193) := by
    rw [show ((276193 / 200000) : ℝ) = ((200000 / 276193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13452_neg : (95918693 / 200000000) ≤ -Real.log (123807 / 200000) ∧
    -Real.log (123807 / 200000) ≤ (239796733 / 500000000) := by
  have h := checkLog_sound (w := (76193 / 323807)) (n := 12)
    (lo := (95918693 / 200000000)) (hi := (239796733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 123807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 123807) = 1/(123807 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13452 : Bounds (-239796733 / 500000000) (-95918693 / 200000000) (Real.log (123807 / 200000)) := by
  have h := reflection_log_13452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13453_neg : (324690243 / 1000000000) ≤ -Real.log (500000 / 691801) ∧
    -Real.log (500000 / 691801) ≤ (81172561 / 250000000) := by
  have h := checkLog_sound (w := (191801 / 1191801)) (n := 12)
    (lo := (324690243 / 1000000000)) (hi := (81172561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691801 / 500000) = 1/(500000 / 691801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13453 : Bounds (324690243 / 1000000000) (81172561 / 250000000) (Real.log (691801 / 500000)) := by
  have h := reflection_log_13453_neg
  have he : Real.log (691801 / 500000) = -Real.log (500000 / 691801) := by
    rw [show ((691801 / 500000) : ℝ) = ((500000 / 691801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13454_neg : (24193121 / 50000000) ≤ -Real.log (308199 / 500000) ∧
    -Real.log (308199 / 500000) ≤ (483862421 / 1000000000) := by
  have h := checkLog_sound (w := (191801 / 808199)) (n := 12)
    (lo := (24193121 / 50000000)) (hi := (483862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308199) = 1/(308199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13454 : Bounds (-483862421 / 1000000000) (-24193121 / 50000000) (Real.log (308199 / 500000)) := by
  have h := reflection_log_13454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13455_neg : (9948261 / 62500000) ≤ -Real.log (213212376399 / 250000000000) ∧
    -Real.log (213212376399 / 250000000000) ≤ (159172177 / 1000000000) := by
  have h := checkLog_sound (w := (36787623601 / 463212376399)) (n := 12)
    (lo := (9948261 / 62500000)) (hi := (159172177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 213212376399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 213212376399) = 1/(213212376399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13455 : Bounds (-159172177 / 1000000000) (-9948261 / 62500000) (Real.log (213212376399 / 250000000000)) := by
  have h := reflection_log_13455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13456_neg : (78405467 / 500000000) ≤ -Real.log (34194626751 / 40000000000) ∧
    -Real.log (34194626751 / 40000000000) ≤ (31362187 / 200000000) := by
  have h := checkLog_sound (w := (5805373249 / 74194626751)) (n := 12)
    (lo := (78405467 / 500000000)) (hi := (31362187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34194626751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34194626751) = 1/(34194626751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13456 : Bounds (-31362187 / 200000000) (-78405467 / 500000000) (Real.log (34194626751 / 40000000000)) := by
  have h := reflection_log_13456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13457_neg : (401187997 / 500000000) ≤ -Real.log (500000000000 / 1115417545049) ∧
    -Real.log (500000000000 / 1115417545049) ≤ (200593999 / 250000000) := by
  have h := checkLog_sound (w := (115417545049 / 2115417545049)) (n := 12)
    (lo := (54614407 / 500000000)) (hi := (21845763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115417545049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1115417545049 / 1000000000000) = 1/(500000000000 / 1115417545049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13457 : Bounds (401187997 / 500000000) (200593999 / 250000000) (Real.log (1115417545049 / 500000000000)) := by
  have h := reflection_log_13457_neg
  have he : Real.log (1115417545049 / 500000000000) = -Real.log (500000000000 / 1115417545049) := by
    rw [show ((1115417545049 / 500000000000) : ℝ) = ((500000000000 / 1115417545049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13458_neg : (808552663 / 1000000000) ≤ -Real.log (500000000000 / 1122328430657) ∧
    -Real.log (500000000000 / 1122328430657) ≤ (161710533 / 200000000) := by
  have h := checkLog_sound (w := (122328430657 / 2122328430657)) (n := 12)
    (lo := (115405483 / 1000000000)) (hi := (28851371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122328430657 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122328430657 / 1000000000000) = 1/(500000000000 / 1122328430657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13458 : Bounds (808552663 / 1000000000) (161710533 / 200000000) (Real.log (1122328430657 / 500000000000)) := by
  have h := reflection_log_13458_neg
  have he : Real.log (1122328430657 / 500000000000) = -Real.log (500000000000 / 1122328430657) := by
    rw [show ((1122328430657 / 500000000000) : ℝ) = ((500000000000 / 1122328430657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13459_neg : (425891689 / 250000000) ≤ -Real.log (500000000000 / 2746753246753) ∧
    -Real.log (500000000000 / 2746753246753) ≤ (1703566759 / 1000000000) := by
  have h := checkLog_sound (w := (746753246753 / 4746753246753)) (n := 12)
    (lo := (79318099 / 250000000)) (hi := (317272397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2746753246753 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2746753246753 / 2000000000000) = 1/(500000000000 / 2746753246753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13459 : Bounds (425891689 / 250000000) (1703566759 / 1000000000) (Real.log (2746753246753 / 500000000000)) := by
  have h := reflection_log_13459_neg
  have he : Real.log (2746753246753 / 500000000000) = -Real.log (500000000000 / 2746753246753) := by
    rw [show ((2746753246753 / 500000000000) : ℝ) = ((500000000000 / 2746753246753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13460_neg : (857563121 / 500000000) ≤ -Real.log (500000000000 / 2778688524591) ∧
    -Real.log (500000000000 / 2778688524591) ≤ (343025249 / 200000000) := by
  have h := checkLog_sound (w := (778688524591 / 4778688524591)) (n := 12)
    (lo := (164415941 / 500000000)) (hi := (328831883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2778688524591 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2778688524591 / 2000000000000) = 1/(500000000000 / 2778688524591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13460 : Bounds (857563121 / 500000000) (343025249 / 200000000) (Real.log (2778688524591 / 500000000000)) := by
  have h := reflection_log_13460_neg
  have he : Real.log (2778688524591 / 500000000000) = -Real.log (500000000000 / 2778688524591) := by
    rw [show ((2778688524591 / 500000000000) : ℝ) = ((500000000000 / 2778688524591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13461_neg : (529451087 / 1000000000) ≤ -Real.log (500 / 849) ∧
    -Real.log (500 / 849) ≤ (33090693 / 62500000) := by
  have h := checkLog_sound (w := (349 / 1349)) (n := 12)
    (lo := (529451087 / 1000000000)) (hi := (33090693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 500) = 1/(500 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13461 : Bounds (529451087 / 1000000000) (33090693 / 62500000) (Real.log (849 / 500)) := by
  have h := reflection_log_13461_neg
  have he : Real.log (849 / 500) = -Real.log (500 / 849) := by
    rw [show ((849 / 500) : ℝ) = ((500 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13462_neg : (1197328261 / 1000000000) ≤ -Real.log (151 / 500) ∧
    -Real.log (151 / 500) ≤ (1197328263 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 401)) (n := 12)
    (lo := (504181081 / 1000000000)) (hi := (252090541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 151) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 151) = 1/(151 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13462 : Bounds (-1197328263 / 1000000000) (-1197328261 / 1000000000) (Real.log (151 / 500)) := by
  have h := reflection_log_13462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13463_neg : (174439 / 250000000) ≤ -Real.log (500000 / 500349) ∧
    -Real.log (500000 / 500349) ≤ (697757 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1000349)) (n := 12)
    (lo := (174439 / 250000000)) (hi := (697757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500349 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500349 / 500000) = 1/(500000 / 500349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13463 : Bounds (174439 / 250000000) (697757 / 1000000000) (Real.log (500349 / 500000)) := by
  have h := reflection_log_13463_neg
  have he : Real.log (500349 / 500000) = -Real.log (500000 / 500349) := by
    rw [show ((500349 / 500000) : ℝ) = ((500000 / 500349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13464_neg : (698243 / 1000000000) ≤ -Real.log (499651 / 500000) ∧
    -Real.log (499651 / 500000) ≤ (174561 / 250000000) := by
  have h := checkLog_sound (w := (349 / 999651)) (n := 12)
    (lo := (698243 / 1000000000)) (hi := (174561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499651) = 1/(499651 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13464 : Bounds (-174561 / 250000000) (-698243 / 1000000000) (Real.log (499651 / 500000)) := by
  have h := reflection_log_13464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13465_neg : (2593971 / 8000000) ≤ -Real.log (250000 / 345747) ∧
    -Real.log (250000 / 345747) ≤ (40530797 / 125000000) := by
  have h := checkLog_sound (w := (95747 / 595747)) (n := 12)
    (lo := (2593971 / 8000000)) (hi := (40530797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345747 / 250000) = 1/(250000 / 345747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13465 : Bounds (2593971 / 8000000) (40530797 / 125000000) (Real.log (345747 / 250000)) := by
  have h := reflection_log_13465_neg
  have he : Real.log (345747 / 250000) = -Real.log (250000 / 345747) := by
    rw [show ((345747 / 250000) : ℝ) = ((250000 / 345747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13466_neg : (241433403 / 500000000) ≤ -Real.log (154253 / 250000) ∧
    -Real.log (154253 / 250000) ≤ (482866807 / 1000000000) := by
  have h := checkLog_sound (w := (95747 / 404253)) (n := 12)
    (lo := (241433403 / 500000000)) (hi := (482866807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154253) = 1/(154253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13466 : Bounds (-482866807 / 1000000000) (-241433403 / 500000000) (Real.log (154253 / 250000)) := by
  have h := reflection_log_13466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13467_neg : (326156353 / 1000000000) ≤ -Real.log (31250 / 43301) ∧
    -Real.log (31250 / 43301) ≤ (163078177 / 500000000) := by
  have h := checkLog_sound (w := (12051 / 74551)) (n := 12)
    (lo := (326156353 / 1000000000)) (hi := (163078177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43301 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43301 / 31250) = 1/(31250 / 43301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13467 : Bounds (326156353 / 1000000000) (163078177 / 500000000) (Real.log (43301 / 31250)) := by
  have h := reflection_log_13467_neg
  have he : Real.log (43301 / 31250) = -Real.log (31250 / 43301) := by
    rw [show ((43301 / 31250) : ℝ) = ((31250 / 43301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13468_neg : (487161181 / 1000000000) ≤ -Real.log (19199 / 31250) ∧
    -Real.log (19199 / 31250) ≤ (243580591 / 500000000) := by
  have h := checkLog_sound (w := (12051 / 50449)) (n := 12)
    (lo := (487161181 / 1000000000)) (hi := (243580591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 19199) = 1/(19199 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13468 : Bounds (-243580591 / 500000000) (-487161181 / 1000000000) (Real.log (19199 / 31250)) := by
  have h := reflection_log_13468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13469_neg : (40251207 / 250000000) ≤ -Real.log (831335899 / 976562500) ∧
    -Real.log (831335899 / 976562500) ≤ (161004829 / 1000000000) := by
  have h := checkLog_sound (w := (145226601 / 1807898399)) (n := 12)
    (lo := (40251207 / 250000000)) (hi := (161004829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 831335899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 831335899) = 1/(831335899 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13469 : Bounds (-161004829 / 1000000000) (-40251207 / 250000000) (Real.log (831335899 / 976562500)) := by
  have h := reflection_log_13469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13470_neg : (15862043 / 100000000) ≤ -Real.log (53332511991 / 62500000000) ∧
    -Real.log (53332511991 / 62500000000) ≤ (158620431 / 1000000000) := by
  have h := checkLog_sound (w := (9167488009 / 115832511991)) (n := 12)
    (lo := (15862043 / 100000000)) (hi := (158620431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53332511991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53332511991) = 1/(53332511991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13470 : Bounds (-158620431 / 1000000000) (-15862043 / 100000000) (Real.log (53332511991 / 62500000000)) := by
  have h := reflection_log_13470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13471_neg : (807113181 / 1000000000) ≤ -Real.log (500000000000 / 1120714021769) ∧
    -Real.log (500000000000 / 1120714021769) ≤ (807113183 / 1000000000) := by
  have h := checkLog_sound (w := (120714021769 / 2120714021769)) (n := 12)
    (lo := (113966001 / 1000000000)) (hi := (56983001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120714021769 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120714021769 / 1000000000000) = 1/(500000000000 / 1120714021769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13471 : Bounds (807113181 / 1000000000) (807113183 / 1000000000) (Real.log (1120714021769 / 500000000000)) := by
  have h := reflection_log_13471_neg
  have he : Real.log (1120714021769 / 500000000000) = -Real.log (500000000000 / 1120714021769) := by
    rw [show ((1120714021769 / 500000000000) : ℝ) = ((500000000000 / 1120714021769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13472_neg : (406658767 / 500000000) ≤ -Real.log (500000000000 / 1127688942133) ∧
    -Real.log (500000000000 / 1127688942133) ≤ (25416173 / 31250000) := by
  have h := checkLog_sound (w := (127688942133 / 2127688942133)) (n := 12)
    (lo := (60085177 / 500000000)) (hi := (24034071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127688942133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1127688942133 / 1000000000000) = 1/(500000000000 / 1127688942133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13472 : Bounds (406658767 / 500000000) (25416173 / 31250000) (Real.log (1127688942133 / 500000000000)) := by
  have h := reflection_log_13472_neg
  have he : Real.log (1127688942133 / 500000000000) = -Real.log (500000000000 / 1127688942133) := by
    rw [show ((1127688942133 / 500000000000) : ℝ) = ((500000000000 / 1127688942133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13473_neg : (857563121 / 500000000) ≤ -Real.log (50000000000 / 277868852459) ∧
    -Real.log (50000000000 / 277868852459) ≤ (343025249 / 200000000) := by
  have h := checkLog_sound (w := (77868852459 / 477868852459)) (n := 12)
    (lo := (164415941 / 500000000)) (hi := (328831883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277868852459 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(277868852459 / 200000000000) = 1/(50000000000 / 277868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13473 : Bounds (857563121 / 500000000) (343025249 / 200000000) (Real.log (277868852459 / 50000000000)) := by
  have h := reflection_log_13473_neg
  have he : Real.log (277868852459 / 50000000000) = -Real.log (50000000000 / 277868852459) := by
    rw [show ((277868852459 / 50000000000) : ℝ) = ((50000000000 / 277868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13474_neg : (431694837 / 250000000) ≤ -Real.log (250000000000 / 1405629139073) ∧
    -Real.log (250000000000 / 1405629139073) ≤ (1726779351 / 1000000000) := by
  have h := checkLog_sound (w := (405629139073 / 2405629139073)) (n := 12)
    (lo := (85121247 / 250000000)) (hi := (340484989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1405629139073 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1405629139073 / 1000000000000) = 1/(250000000000 / 1405629139073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13474 : Bounds (431694837 / 250000000) (1726779351 / 1000000000) (Real.log (1405629139073 / 250000000000)) := by
  have h := reflection_log_13474_neg
  have he : Real.log (1405629139073 / 250000000000) = -Real.log (250000000000 / 1405629139073) := by
    rw [show ((1405629139073 / 250000000000) : ℝ) = ((250000000000 / 1405629139073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13475_neg : (531216313 / 1000000000) ≤ -Real.log (1000 / 1701) ∧
    -Real.log (1000 / 1701) ≤ (265608157 / 500000000) := by
  have h := checkLog_sound (w := (701 / 2701)) (n := 12)
    (lo := (531216313 / 1000000000)) (hi := (265608157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1000) = 1/(1000 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13475 : Bounds (531216313 / 1000000000) (265608157 / 500000000) (Real.log (1701 / 1000)) := by
  have h := reflection_log_13475_neg
  have he : Real.log (1701 / 1000) = -Real.log (1000 / 1701) := by
    rw [show ((1701 / 1000) : ℝ) = ((1000 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13476_neg : (241462341 / 200000000) ≤ -Real.log (299 / 1000) ∧
    -Real.log (299 / 1000) ≤ (1207311707 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 799)) (n := 12)
    (lo := (20566581 / 40000000)) (hi := (257082263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 299) = 1/(299 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13476 : Bounds (-1207311707 / 1000000000) (-241462341 / 200000000) (Real.log (299 / 1000)) := by
  have h := reflection_log_13476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13477_neg : (350377 / 500000000) ≤ -Real.log (1000000 / 1000701) ∧
    -Real.log (1000000 / 1000701) ≤ (140151 / 200000000) := by
  have h := checkLog_sound (w := (701 / 2000701)) (n := 12)
    (lo := (350377 / 500000000)) (hi := (140151 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000701 / 1000000) = 1/(1000000 / 1000701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13477 : Bounds (350377 / 500000000) (140151 / 200000000) (Real.log (1000701 / 1000000)) := by
  have h := reflection_log_13477_neg
  have he : Real.log (1000701 / 1000000) = -Real.log (1000000 / 1000701) := by
    rw [show ((1000701 / 1000000) : ℝ) = ((1000000 / 1000701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13478_neg : (140249 / 200000000) ≤ -Real.log (999299 / 1000000) ∧
    -Real.log (999299 / 1000000) ≤ (350623 / 500000000) := by
  have h := checkLog_sound (w := (701 / 1999299)) (n := 12)
    (lo := (140249 / 200000000)) (hi := (350623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999299) = 1/(999299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13478 : Bounds (-350623 / 500000000) (-140249 / 200000000) (Real.log (999299 / 1000000)) := by
  have h := reflection_log_13478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13479_neg : (325712413 / 1000000000) ≤ -Real.log (1000000 / 1385017) ∧
    -Real.log (1000000 / 1385017) ≤ (162856207 / 500000000) := by
  have h := checkLog_sound (w := (385017 / 2385017)) (n := 12)
    (lo := (325712413 / 1000000000)) (hi := (162856207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385017 / 1000000) = 1/(1000000 / 1385017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13479 : Bounds (325712413 / 1000000000) (162856207 / 500000000) (Real.log (1385017 / 1000000)) := by
  have h := reflection_log_13479_neg
  have he : Real.log (1385017 / 1000000) = -Real.log (1000000 / 1385017) := by
    rw [show ((1385017 / 1000000) : ℝ) = ((1000000 / 1385017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13480_neg : (486160653 / 1000000000) ≤ -Real.log (614983 / 1000000) ∧
    -Real.log (614983 / 1000000) ≤ (243080327 / 500000000) := by
  have h := checkLog_sound (w := (385017 / 1614983)) (n := 12)
    (lo := (486160653 / 1000000000)) (hi := (243080327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614983) = 1/(614983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13480 : Bounds (-243080327 / 500000000) (-486160653 / 1000000000) (Real.log (614983 / 1000000)) := by
  have h := reflection_log_13480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13481_neg : (327626081 / 1000000000) ≤ -Real.log (100000 / 138767) ∧
    -Real.log (100000 / 138767) ≤ (163813041 / 500000000) := by
  have h := checkLog_sound (w := (38767 / 238767)) (n := 12)
    (lo := (327626081 / 1000000000)) (hi := (163813041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138767 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138767 / 100000) = 1/(100000 / 138767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13481 : Bounds (327626081 / 1000000000) (163813041 / 500000000) (Real.log (138767 / 100000)) := by
  have h := reflection_log_13481_neg
  have he : Real.log (138767 / 100000) = -Real.log (100000 / 138767) := by
    rw [show ((138767 / 100000) : ℝ) = ((100000 / 138767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13482_neg : (245241963 / 500000000) ≤ -Real.log (61233 / 100000) ∧
    -Real.log (61233 / 100000) ≤ (490483927 / 1000000000) := by
  have h := checkLog_sound (w := (38767 / 161233)) (n := 12)
    (lo := (245241963 / 500000000)) (hi := (490483927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 61233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 61233) = 1/(61233 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13482 : Bounds (-490483927 / 1000000000) (-245241963 / 500000000) (Real.log (61233 / 100000)) := by
  have h := reflection_log_13482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13483_neg : (40714461 / 250000000) ≤ -Real.log (8497119711 / 10000000000) ∧
    -Real.log (8497119711 / 10000000000) ≤ (32571569 / 200000000) := by
  have h := checkLog_sound (w := (1502880289 / 18497119711)) (n := 12)
    (lo := (40714461 / 250000000)) (hi := (32571569 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8497119711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8497119711) = 1/(8497119711 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13483 : Bounds (-32571569 / 200000000) (-40714461 / 250000000) (Real.log (8497119711 / 10000000000)) := by
  have h := reflection_log_13483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13484_neg : (160448239 / 1000000000) ≤ -Real.log (851761909711 / 1000000000000) ∧
    -Real.log (851761909711 / 1000000000000) ≤ (2005603 / 12500000) := by
  have h := checkLog_sound (w := (148238090289 / 1851761909711)) (n := 12)
    (lo := (160448239 / 1000000000)) (hi := (2005603 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 851761909711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 851761909711) = 1/(851761909711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13484 : Bounds (-2005603 / 12500000) (-160448239 / 1000000000) (Real.log (851761909711 / 1000000000000)) := by
  have h := reflection_log_13484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13485_neg : (811873067 / 1000000000) ≤ -Real.log (100000000000 / 225212241639) ∧
    -Real.log (100000000000 / 225212241639) ≤ (811873069 / 1000000000) := by
  have h := checkLog_sound (w := (25212241639 / 425212241639)) (n := 12)
    (lo := (118725887 / 1000000000)) (hi := (463773 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225212241639 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225212241639 / 200000000000) = 1/(100000000000 / 225212241639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13485 : Bounds (811873067 / 1000000000) (811873069 / 1000000000) (Real.log (225212241639 / 100000000000)) := by
  have h := reflection_log_13485_neg
  have he : Real.log (225212241639 / 100000000000) = -Real.log (100000000000 / 225212241639) := by
    rw [show ((225212241639 / 100000000000) : ℝ) = ((100000000000 / 225212241639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13486_neg : (818110007 / 1000000000) ≤ -Real.log (250000000000 / 566553165777) ∧
    -Real.log (250000000000 / 566553165777) ≤ (818110009 / 1000000000) := by
  have h := checkLog_sound (w := (66553165777 / 1066553165777)) (n := 12)
    (lo := (124962827 / 1000000000)) (hi := (31240707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566553165777 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(566553165777 / 500000000000) = 1/(250000000000 / 566553165777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13486 : Bounds (818110007 / 1000000000) (818110009 / 1000000000) (Real.log (566553165777 / 250000000000)) := by
  have h := reflection_log_13486_neg
  have he : Real.log (566553165777 / 250000000000) = -Real.log (250000000000 / 566553165777) := by
    rw [show ((566553165777 / 250000000000) : ℝ) = ((250000000000 / 566553165777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13487_neg : (431694837 / 250000000) ≤ -Real.log (100000000000 / 562251655629) ∧
    -Real.log (100000000000 / 562251655629) ≤ (1726779351 / 1000000000) := by
  have h := checkLog_sound (w := (162251655629 / 962251655629)) (n := 12)
    (lo := (85121247 / 250000000)) (hi := (340484989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((562251655629 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(562251655629 / 400000000000) = 1/(100000000000 / 562251655629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13487 : Bounds (431694837 / 250000000) (1726779351 / 1000000000) (Real.log (562251655629 / 100000000000)) := by
  have h := reflection_log_13487_neg
  have he : Real.log (562251655629 / 100000000000) = -Real.log (100000000000 / 562251655629) := by
    rw [show ((562251655629 / 100000000000) : ℝ) = ((100000000000 / 562251655629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13488_neg : (1738528017 / 1000000000) ≤ -Real.log (62500000000 / 355560200669) ∧
    -Real.log (62500000000 / 355560200669) ≤ (86926401 / 50000000) := by
  have h := checkLog_sound (w := (105560200669 / 605560200669)) (n := 12)
    (lo := (352233657 / 1000000000)) (hi := (176116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355560200669 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(355560200669 / 250000000000) = 1/(62500000000 / 355560200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13488 : Bounds (1738528017 / 1000000000) (86926401 / 50000000) (Real.log (355560200669 / 62500000000)) := by
  have h := reflection_log_13488_neg
  have he : Real.log (355560200669 / 62500000000) = -Real.log (62500000000 / 355560200669) := by
    rw [show ((355560200669 / 62500000000) : ℝ) = ((62500000000 / 355560200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13489_neg : (133244607 / 250000000) ≤ -Real.log (125 / 213) ∧
    -Real.log (125 / 213) ≤ (532978429 / 1000000000) := by
  have h := checkLog_sound (w := (44 / 169)) (n := 12)
    (lo := (133244607 / 250000000)) (hi := (532978429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 125) = 1/(125 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13489 : Bounds (133244607 / 250000000) (532978429 / 1000000000) (Real.log (213 / 125)) := by
  have h := reflection_log_13489_neg
  have he : Real.log (213 / 125) = -Real.log (125 / 213) := by
    rw [show ((213 / 125) : ℝ) = ((125 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13490_neg : (76087239 / 62500000) ≤ -Real.log (37 / 125) ∧
    -Real.log (37 / 125) ≤ (608697913 / 500000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 74) = 1/(37 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13490 : Bounds (-608697913 / 500000000) (-76087239 / 62500000) (Real.log (37 / 125)) := by
  have h := reflection_log_13490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13491_neg : (87969 / 125000000) ≤ -Real.log (15625 / 15636) ∧
    -Real.log (15625 / 15636) ≤ (703753 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 31261)) (n := 12)
    (lo := (87969 / 125000000)) (hi := (703753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15636 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15636 / 15625) = 1/(15625 / 15636) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13491 : Bounds (87969 / 125000000) (703753 / 1000000000) (Real.log (15636 / 15625)) := by
  have h := reflection_log_13491_neg
  have he : Real.log (15636 / 15625) = -Real.log (15625 / 15636) := by
    rw [show ((15636 / 15625) : ℝ) = ((15625 / 15636) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13492_neg : (704247 / 1000000000) ≤ -Real.log (15614 / 15625) ∧
    -Real.log (15614 / 15625) ≤ (88031 / 125000000) := by
  have h := checkLog_sound (w := (11 / 31239)) (n := 12)
    (lo := (704247 / 1000000000)) (hi := (88031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15614) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15614) = 1/(15614 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13492 : Bounds (-88031 / 125000000) (-704247 / 1000000000) (Real.log (15614 / 15625)) := by
  have h := reflection_log_13492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13493_neg : (327180631 / 1000000000) ≤ -Real.log (250000 / 346763) ∧
    -Real.log (250000 / 346763) ≤ (40897579 / 125000000) := by
  have h := checkLog_sound (w := (96763 / 596763)) (n := 12)
    (lo := (327180631 / 1000000000)) (hi := (40897579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346763 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346763 / 250000) = 1/(250000 / 346763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13493 : Bounds (327180631 / 1000000000) (40897579 / 125000000) (Real.log (346763 / 250000)) := by
  have h := reflection_log_13493_neg
  have he : Real.log (346763 / 250000) = -Real.log (250000 / 346763) := by
    rw [show ((346763 / 250000) : ℝ) = ((250000 / 346763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13494_neg : (19579007 / 40000000) ≤ -Real.log (153237 / 250000) ∧
    -Real.log (153237 / 250000) ≤ (61184397 / 125000000) := by
  have h := checkLog_sound (w := (96763 / 403237)) (n := 12)
    (lo := (19579007 / 40000000)) (hi := (61184397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153237) = 1/(153237 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13494 : Bounds (-61184397 / 125000000) (-19579007 / 40000000) (Real.log (153237 / 250000)) := by
  have h := reflection_log_13494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13495_neg : (329097251 / 1000000000) ≤ -Real.log (1000000 / 1389713) ∧
    -Real.log (1000000 / 1389713) ≤ (82274313 / 250000000) := by
  have h := checkLog_sound (w := (389713 / 2389713)) (n := 12)
    (lo := (329097251 / 1000000000)) (hi := (82274313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389713 / 1000000) = 1/(1000000 / 1389713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13495 : Bounds (329097251 / 1000000000) (82274313 / 250000000) (Real.log (1389713 / 1000000)) := by
  have h := reflection_log_13495_neg
  have he : Real.log (1389713 / 1000000) = -Real.log (1000000 / 1389713) := by
    rw [show ((1389713 / 1000000) : ℝ) = ((1000000 / 1389713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13496_neg : (24691297 / 50000000) ≤ -Real.log (610287 / 1000000) ∧
    -Real.log (610287 / 1000000) ≤ (493825941 / 1000000000) := by
  have h := checkLog_sound (w := (389713 / 1610287)) (n := 12)
    (lo := (24691297 / 50000000)) (hi := (493825941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610287) = 1/(610287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13496 : Bounds (-493825941 / 1000000000) (-24691297 / 50000000) (Real.log (610287 / 1000000)) := by
  have h := reflection_log_13496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13497_neg : (164728689 / 1000000000) ≤ -Real.log (848123777631 / 1000000000000) ∧
    -Real.log (848123777631 / 1000000000000) ≤ (16472869 / 100000000) := by
  have h := checkLog_sound (w := (151876222369 / 1848123777631)) (n := 12)
    (lo := (164728689 / 1000000000)) (hi := (16472869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 848123777631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 848123777631) = 1/(848123777631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13497 : Bounds (-16472869 / 100000000) (-164728689 / 1000000000) (Real.log (848123777631 / 1000000000000)) := by
  have h := reflection_log_13497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13498_neg : (162294543 / 1000000000) ≤ -Real.log (53136921831 / 62500000000) ∧
    -Real.log (53136921831 / 62500000000) ≤ (10143409 / 62500000) := by
  have h := checkLog_sound (w := (9363078169 / 115636921831)) (n := 12)
    (lo := (162294543 / 1000000000)) (hi := (10143409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53136921831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53136921831) = 1/(53136921831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13498 : Bounds (-10143409 / 62500000) (-162294543 / 1000000000) (Real.log (53136921831 / 62500000000)) := by
  have h := reflection_log_13498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13499_neg : (408327903 / 500000000) ≤ -Real.log (500000000000 / 1131459764939) ∧
    -Real.log (500000000000 / 1131459764939) ≤ (12760247 / 15625000) := by
  have h := checkLog_sound (w := (131459764939 / 2131459764939)) (n := 12)
    (lo := (61754313 / 500000000)) (hi := (123508627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131459764939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131459764939 / 1000000000000) = 1/(500000000000 / 1131459764939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13499 : Bounds (408327903 / 500000000) (12760247 / 15625000) (Real.log (1131459764939 / 500000000000)) := by
  have h := reflection_log_13499_neg
  have he : Real.log (1131459764939 / 500000000000) = -Real.log (500000000000 / 1131459764939) := by
    rw [show ((1131459764939 / 500000000000) : ℝ) = ((500000000000 / 1131459764939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13500_neg : (822923191 / 1000000000) ≤ -Real.log (3906250000 / 8895104117) ∧
    -Real.log (3906250000 / 8895104117) ≤ (822923193 / 1000000000) := by
  have h := checkLog_sound (w := (1082604117 / 16707604117)) (n := 12)
    (lo := (129776011 / 1000000000)) (hi := (32444003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8895104117 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8895104117 / 7812500000) = 1/(3906250000 / 8895104117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13500 : Bounds (822923191 / 1000000000) (822923193 / 1000000000) (Real.log (8895104117 / 3906250000)) := by
  have h := reflection_log_13500_neg
  have he : Real.log (8895104117 / 3906250000) = -Real.log (3906250000 / 8895104117) := by
    rw [show ((8895104117 / 3906250000) : ℝ) = ((3906250000 / 8895104117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13501_neg : (1738528017 / 1000000000) ≤ -Real.log (500000000000 / 2844481605351) ∧
    -Real.log (500000000000 / 2844481605351) ≤ (86926401 / 50000000) := by
  have h := checkLog_sound (w := (844481605351 / 4844481605351)) (n := 12)
    (lo := (352233657 / 1000000000)) (hi := (176116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2844481605351 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2844481605351 / 2000000000000) = 1/(500000000000 / 2844481605351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13501 : Bounds (1738528017 / 1000000000) (86926401 / 50000000) (Real.log (2844481605351 / 500000000000)) := by
  have h := reflection_log_13501_neg
  have he : Real.log (2844481605351 / 500000000000) = -Real.log (500000000000 / 2844481605351) := by
    rw [show ((2844481605351 / 500000000000) : ℝ) = ((500000000000 / 2844481605351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13502_neg : (1750374251 / 1000000000) ≤ -Real.log (500000000000 / 2878378378379) ∧
    -Real.log (500000000000 / 2878378378379) ≤ (875187127 / 500000000) := by
  have h := checkLog_sound (w := (878378378379 / 4878378378379)) (n := 12)
    (lo := (364079891 / 1000000000)) (hi := (91019973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2878378378379 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2878378378379 / 2000000000000) = 1/(500000000000 / 2878378378379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13502 : Bounds (1750374251 / 1000000000) (875187127 / 500000000) (Real.log (2878378378379 / 500000000000)) := by
  have h := reflection_log_13502_neg
  have he : Real.log (2878378378379 / 500000000000) = -Real.log (500000000000 / 2878378378379) := by
    rw [show ((2878378378379 / 500000000000) : ℝ) = ((500000000000 / 2878378378379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13503_neg : (534737443 / 1000000000) ≤ -Real.log (1000 / 1707) ∧
    -Real.log (1000 / 1707) ≤ (133684361 / 250000000) := by
  have h := checkLog_sound (w := (707 / 2707)) (n := 12)
    (lo := (534737443 / 1000000000)) (hi := (133684361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1000) = 1/(1000 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13503 : Bounds (534737443 / 1000000000) (133684361 / 250000000) (Real.log (1707 / 1000)) := by
  have h := reflection_log_13503_neg
  have he : Real.log (1707 / 1000) = -Real.log (1000 / 1707) := by
    rw [show ((1707 / 1000) : ℝ) = ((1000 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
