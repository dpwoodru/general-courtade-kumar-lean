import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_256_neg : (30535981 / 200000000) ≤ -Real.log (500000000000 / 582476012331) ∧
    -Real.log (500000000000 / 582476012331) ≤ (76339953 / 500000000) := by
  have h := checkLog_sound (w := (82476012331 / 1082476012331)) (n := 12)
    (lo := (30535981 / 200000000)) (hi := (76339953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582476012331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582476012331 / 500000000000) = 1/(500000000000 / 582476012331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_256 : Bounds (30535981 / 200000000) (76339953 / 500000000) (Real.log (582476012331 / 500000000000)) := by
  have h := reflection_log_256_neg
  have he : Real.log (582476012331 / 500000000000) = -Real.log (500000000000 / 582476012331) := by
    rw [show ((582476012331 / 500000000000) : ℝ) = ((500000000000 / 582476012331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_257_neg : (76544141 / 500000000) ≤ -Real.log (500000000000 / 582713930739) ∧
    -Real.log (500000000000 / 582713930739) ≤ (153088283 / 1000000000) := by
  have h := checkLog_sound (w := (82713930739 / 1082713930739)) (n := 12)
    (lo := (76544141 / 500000000)) (hi := (153088283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582713930739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582713930739 / 500000000000) = 1/(500000000000 / 582713930739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_257 : Bounds (76544141 / 500000000) (153088283 / 1000000000) (Real.log (582713930739 / 500000000000)) := by
  have h := reflection_log_257_neg
  have he : Real.log (582713930739 / 500000000000) = -Real.log (500000000000 / 582713930739) := by
    rw [show ((582713930739 / 500000000000) : ℝ) = ((500000000000 / 582713930739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_258_neg : (153084739 / 500000000) ≤ -Real.log (500000000000 / 679106237471) ∧
    -Real.log (500000000000 / 679106237471) ≤ (306169479 / 1000000000) := by
  have h := checkLog_sound (w := (179106237471 / 1179106237471)) (n := 12)
    (lo := (153084739 / 500000000)) (hi := (306169479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679106237471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679106237471 / 500000000000) = 1/(500000000000 / 679106237471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_258 : Bounds (153084739 / 500000000) (306169479 / 1000000000) (Real.log (679106237471 / 500000000000)) := by
  have h := reflection_log_258_neg
  have he : Real.log (679106237471 / 500000000000) = -Real.log (500000000000 / 679106237471) := by
    rw [show ((679106237471 / 500000000000) : ℝ) = ((500000000000 / 679106237471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_259_neg : (61274841 / 200000000) ≤ -Real.log (500000000000 / 679245283019) ∧
    -Real.log (500000000000 / 679245283019) ≤ (153187103 / 500000000) := by
  have h := checkLog_sound (w := (179245283019 / 1179245283019)) (n := 12)
    (lo := (61274841 / 200000000)) (hi := (153187103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679245283019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679245283019 / 500000000000) = 1/(500000000000 / 679245283019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_259 : Bounds (61274841 / 200000000) (153187103 / 500000000) (Real.log (679245283019 / 500000000000)) := by
  have h := reflection_log_259_neg
  have he : Real.log (679245283019 / 500000000000) = -Real.log (500000000000 / 679245283019) := by
    rw [show ((679245283019 / 500000000000) : ℝ) = ((500000000000 / 679245283019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_260_neg : (35396591 / 250000000) ≤ -Real.log (10000 / 11521) ∧
    -Real.log (10000 / 11521) ≤ (28317273 / 200000000) := by
  have h := checkLog_sound (w := (1521 / 21521)) (n := 12)
    (lo := (35396591 / 250000000)) (hi := (28317273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11521 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11521 / 10000) = 1/(10000 / 11521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_260 : Bounds (35396591 / 250000000) (28317273 / 200000000) (Real.log (11521 / 10000)) := by
  have h := reflection_log_260_neg
  have he : Real.log (11521 / 10000) = -Real.log (10000 / 11521) := by
    rw [show ((11521 / 10000) : ℝ) = ((10000 / 11521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_261_neg : (82496287 / 500000000) ≤ -Real.log (8479 / 10000) ∧
    -Real.log (8479 / 10000) ≤ (6599703 / 40000000) := by
  have h := checkLog_sound (w := (1521 / 18479)) (n := 12)
    (lo := (82496287 / 500000000)) (hi := (6599703 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8479) = 1/(8479 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_261 : Bounds (-6599703 / 40000000) (-82496287 / 500000000) (Real.log (8479 / 10000)) := by
  have h := reflection_log_261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_262_neg : (19011 / 125000000) ≤ -Real.log (10000000 / 10001521) ∧
    -Real.log (10000000 / 10001521) ≤ (152089 / 1000000000) := by
  have h := checkLog_sound (w := (1521 / 20001521)) (n := 12)
    (lo := (19011 / 125000000)) (hi := (152089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001521 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001521 / 10000000) = 1/(10000000 / 10001521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_262 : Bounds (19011 / 125000000) (152089 / 1000000000) (Real.log (10001521 / 10000000)) := by
  have h := reflection_log_262_neg
  have he : Real.log (10001521 / 10000000) = -Real.log (10000000 / 10001521) := by
    rw [show ((10001521 / 10000000) : ℝ) = ((10000000 / 10001521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_263_neg : (152111 / 1000000000) ≤ -Real.log (9998479 / 10000000) ∧
    -Real.log (9998479 / 10000000) ≤ (9507 / 62500000) := by
  have h := checkLog_sound (w := (1521 / 19998479)) (n := 12)
    (lo := (152111 / 1000000000)) (hi := (9507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998479) = 1/(9998479 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_263 : Bounds (-9507 / 62500000) (-152111 / 1000000000) (Real.log (9998479 / 10000000)) := by
  have h := reflection_log_263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_264_neg : (36832437 / 500000000) ≤ -Real.log (500000 / 538223) ∧
    -Real.log (500000 / 538223) ≤ (589319 / 8000000) := by
  have h := checkLog_sound (w := (38223 / 1038223)) (n := 12)
    (lo := (36832437 / 500000000)) (hi := (589319 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538223 / 500000) = 1/(500000 / 538223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_264 : Bounds (36832437 / 500000000) (589319 / 8000000) (Real.log (538223 / 500000)) := by
  have h := reflection_log_264_neg
  have he : Real.log (538223 / 500000) = -Real.log (500000 / 538223) := by
    rw [show ((538223 / 500000) : ℝ) = ((500000 / 538223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_265_neg : (79526007 / 1000000000) ≤ -Real.log (461777 / 500000) ∧
    -Real.log (461777 / 500000) ≤ (9940751 / 125000000) := by
  have h := checkLog_sound (w := (38223 / 961777)) (n := 12)
    (lo := (79526007 / 1000000000)) (hi := (9940751 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461777) = 1/(461777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_265 : Bounds (-9940751 / 125000000) (-79526007 / 1000000000) (Real.log (461777 / 500000)) := by
  have h := reflection_log_265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_266_neg : (5861133 / 1000000000) ≤ -Real.log (248539002271 / 250000000000) ∧
    -Real.log (248539002271 / 250000000000) ≤ (2930567 / 500000000) := by
  have h := checkLog_sound (w := (1460997729 / 498539002271)) (n := 12)
    (lo := (5861133 / 1000000000)) (hi := (2930567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248539002271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248539002271) = 1/(248539002271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_266 : Bounds (-2930567 / 500000000) (-5861133 / 1000000000) (Real.log (248539002271 / 250000000000)) := by
  have h := reflection_log_266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_267_neg : (152782501 / 1000000000) ≤ -Real.log (500000000000 / 582535775101) ∧
    -Real.log (500000000000 / 582535775101) ≤ (76391251 / 500000000) := by
  have h := checkLog_sound (w := (82535775101 / 1082535775101)) (n := 12)
    (lo := (152782501 / 1000000000)) (hi := (76391251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582535775101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582535775101 / 500000000000) = 1/(500000000000 / 582535775101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_267 : Bounds (152782501 / 1000000000) (76391251 / 500000000) (Real.log (582535775101 / 500000000000)) := by
  have h := reflection_log_267_neg
  have he : Real.log (582535775101 / 500000000000) = -Real.log (500000000000 / 582535775101) := by
    rw [show ((582535775101 / 500000000000) : ℝ) = ((500000000000 / 582535775101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_268_neg : (153190881 / 1000000000) ≤ -Real.log (500000000000 / 582773719783) ∧
    -Real.log (500000000000 / 582773719783) ≤ (76595441 / 500000000) := by
  have h := checkLog_sound (w := (82773719783 / 1082773719783)) (n := 12)
    (lo := (153190881 / 1000000000)) (hi := (76595441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582773719783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582773719783 / 500000000000) = 1/(500000000000 / 582773719783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_268 : Bounds (153190881 / 1000000000) (76595441 / 500000000) (Real.log (582773719783 / 500000000000)) := by
  have h := reflection_log_268_neg
  have he : Real.log (582773719783 / 500000000000) = -Real.log (500000000000 / 582773719783) := by
    rw [show ((582773719783 / 500000000000) : ℝ) = ((500000000000 / 582773719783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_269_neg : (61274841 / 200000000) ≤ -Real.log (250000000000 / 339622641509) ∧
    -Real.log (250000000000 / 339622641509) ≤ (153187103 / 500000000) := by
  have h := checkLog_sound (w := (89622641509 / 589622641509)) (n := 12)
    (lo := (61274841 / 200000000)) (hi := (153187103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339622641509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339622641509 / 250000000000) = 1/(250000000000 / 339622641509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_269 : Bounds (61274841 / 200000000) (153187103 / 500000000) (Real.log (339622641509 / 250000000000)) := by
  have h := reflection_log_269_neg
  have he : Real.log (339622641509 / 250000000000) = -Real.log (250000000000 / 339622641509) := by
    rw [show ((339622641509 / 250000000000) : ℝ) = ((250000000000 / 339622641509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_270_neg : (153289469 / 500000000) ≤ -Real.log (125000000000 / 169846090341) ∧
    -Real.log (125000000000 / 169846090341) ≤ (306578939 / 1000000000) := by
  have h := checkLog_sound (w := (44846090341 / 294846090341)) (n := 12)
    (lo := (153289469 / 500000000)) (hi := (306578939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169846090341 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169846090341 / 125000000000) = 1/(125000000000 / 169846090341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_270 : Bounds (153289469 / 500000000) (306578939 / 1000000000) (Real.log (169846090341 / 125000000000)) := by
  have h := reflection_log_270_neg
  have he : Real.log (169846090341 / 125000000000) = -Real.log (125000000000 / 169846090341) := by
    rw [show ((169846090341 / 125000000000) : ℝ) = ((125000000000 / 169846090341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_271_neg : (70836579 / 500000000) ≤ -Real.log (5000 / 5761) ∧
    -Real.log (5000 / 5761) ≤ (141673159 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 10761)) (n := 12)
    (lo := (70836579 / 500000000)) (hi := (141673159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5761 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5761 / 5000) = 1/(5000 / 5761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_271 : Bounds (70836579 / 500000000) (141673159 / 1000000000) (Real.log (5761 / 5000)) := by
  have h := reflection_log_271_neg
  have he : Real.log (5761 / 5000) = -Real.log (5000 / 5761) := by
    rw [show ((5761 / 5000) : ℝ) = ((5000 / 5761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_272_neg : (4127763 / 25000000) ≤ -Real.log (4239 / 5000) ∧
    -Real.log (4239 / 5000) ≤ (165110521 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 9239)) (n := 12)
    (lo := (4127763 / 25000000)) (hi := (165110521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4239) = 1/(4239 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_272 : Bounds (-165110521 / 1000000000) (-4127763 / 25000000) (Real.log (4239 / 5000)) := by
  have h := reflection_log_272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_273_neg : (38047 / 250000000) ≤ -Real.log (5000000 / 5000761) ∧
    -Real.log (5000000 / 5000761) ≤ (152189 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 10000761)) (n := 12)
    (lo := (38047 / 250000000)) (hi := (152189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000761 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000761 / 5000000) = 1/(5000000 / 5000761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_273 : Bounds (38047 / 250000000) (152189 / 1000000000) (Real.log (5000761 / 5000000)) := by
  have h := reflection_log_273_neg
  have he : Real.log (5000761 / 5000000) = -Real.log (5000000 / 5000761) := by
    rw [show ((5000761 / 5000000) : ℝ) = ((5000000 / 5000761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_274_neg : (152211 / 1000000000) ≤ -Real.log (4999239 / 5000000) ∧
    -Real.log (4999239 / 5000000) ≤ (38053 / 250000000) := by
  have h := checkLog_sound (w := (761 / 9999239)) (n := 12)
    (lo := (152211 / 1000000000)) (hi := (38053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999239) = 1/(4999239 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_274 : Bounds (-38053 / 250000000) (-152211 / 1000000000) (Real.log (4999239 / 5000000)) := by
  have h := reflection_log_274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_275_neg : (73522729 / 1000000000) ≤ -Real.log (1000000 / 1076293) ∧
    -Real.log (1000000 / 1076293) ≤ (7352273 / 100000000) := by
  have h := checkLog_sound (w := (76293 / 2076293)) (n := 12)
    (lo := (73522729 / 1000000000)) (hi := (7352273 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076293 / 1000000) = 1/(1000000 / 1076293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_275 : Bounds (73522729 / 1000000000) (7352273 / 100000000) (Real.log (1076293 / 1000000)) := by
  have h := reflection_log_275_neg
  have he : Real.log (1076293 / 1000000) = -Real.log (1000000 / 1076293) := by
    rw [show ((1076293 / 1000000) : ℝ) = ((1000000 / 1076293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_276_neg : (79360357 / 1000000000) ≤ -Real.log (923707 / 1000000) ∧
    -Real.log (923707 / 1000000) ≤ (39680179 / 500000000) := by
  have h := checkLog_sound (w := (76293 / 1923707)) (n := 12)
    (lo := (79360357 / 1000000000)) (hi := (39680179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923707) = 1/(923707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_276 : Bounds (-39680179 / 500000000) (-79360357 / 1000000000) (Real.log (923707 / 1000000)) := by
  have h := reflection_log_276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_277_neg : (36855661 / 500000000) ≤ -Real.log (62500 / 67281) ∧
    -Real.log (62500 / 67281) ≤ (73711323 / 1000000000) := by
  have h := checkLog_sound (w := (4781 / 129781)) (n := 12)
    (lo := (36855661 / 500000000)) (hi := (73711323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67281 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67281 / 62500) = 1/(62500 / 67281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_277 : Bounds (36855661 / 500000000) (73711323 / 1000000000) (Real.log (67281 / 62500)) := by
  have h := reflection_log_277_neg
  have he : Real.log (67281 / 62500) = -Real.log (62500 / 67281) := by
    rw [show ((67281 / 62500) : ℝ) = ((62500 / 67281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_278_neg : (19895037 / 250000000) ≤ -Real.log (57719 / 62500) ∧
    -Real.log (57719 / 62500) ≤ (79580149 / 1000000000) := by
  have h := checkLog_sound (w := (4781 / 120219)) (n := 12)
    (lo := (19895037 / 250000000)) (hi := (79580149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57719) = 1/(57719 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_278 : Bounds (-79580149 / 1000000000) (-19895037 / 250000000) (Real.log (57719 / 62500)) := by
  have h := reflection_log_278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_279_neg : (234753 / 40000000) ≤ -Real.log (3883392039 / 3906250000) ∧
    -Real.log (3883392039 / 3906250000) ≤ (2934413 / 500000000) := by
  have h := checkLog_sound (w := (22857961 / 7789642039)) (n := 12)
    (lo := (234753 / 40000000)) (hi := (2934413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3883392039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3883392039) = 1/(3883392039 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_279 : Bounds (-2934413 / 500000000) (-234753 / 40000000) (Real.log (3883392039 / 3906250000)) := by
  have h := reflection_log_279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_280_neg : (5837627 / 1000000000) ≤ -Real.log (994179378151 / 1000000000000) ∧
    -Real.log (994179378151 / 1000000000000) ≤ (1459407 / 250000000) := by
  have h := checkLog_sound (w := (5820621849 / 1994179378151)) (n := 12)
    (lo := (5837627 / 1000000000)) (hi := (1459407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994179378151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994179378151) = 1/(994179378151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_280 : Bounds (-1459407 / 250000000) (-5837627 / 1000000000) (Real.log (994179378151 / 1000000000000)) := by
  have h := reflection_log_280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_281_neg : (76441543 / 500000000) ≤ -Real.log (500000000000 / 582594372457) ∧
    -Real.log (500000000000 / 582594372457) ≤ (152883087 / 1000000000) := by
  have h := checkLog_sound (w := (82594372457 / 1082594372457)) (n := 12)
    (lo := (76441543 / 500000000)) (hi := (152883087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582594372457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582594372457 / 500000000000) = 1/(500000000000 / 582594372457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_281 : Bounds (76441543 / 500000000) (152883087 / 1000000000) (Real.log (582594372457 / 500000000000)) := by
  have h := reflection_log_281_neg
  have he : Real.log (582594372457 / 500000000000) = -Real.log (500000000000 / 582594372457) := by
    rw [show ((582594372457 / 500000000000) : ℝ) = ((500000000000 / 582594372457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_282_neg : (15329147 / 100000000) ≤ -Real.log (500000000000 / 582832342903) ∧
    -Real.log (500000000000 / 582832342903) ≤ (153291471 / 1000000000) := by
  have h := checkLog_sound (w := (82832342903 / 1082832342903)) (n := 12)
    (lo := (15329147 / 100000000)) (hi := (153291471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582832342903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582832342903 / 500000000000) = 1/(500000000000 / 582832342903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_282 : Bounds (15329147 / 100000000) (153291471 / 1000000000) (Real.log (582832342903 / 500000000000)) := by
  have h := reflection_log_282_neg
  have he : Real.log (582832342903 / 500000000000) = -Real.log (500000000000 / 582832342903) := by
    rw [show ((582832342903 / 500000000000) : ℝ) = ((500000000000 / 582832342903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_283_neg : (153289469 / 500000000) ≤ -Real.log (500000000000 / 679384361363) ∧
    -Real.log (500000000000 / 679384361363) ≤ (306578939 / 1000000000) := by
  have h := checkLog_sound (w := (179384361363 / 1179384361363)) (n := 12)
    (lo := (153289469 / 500000000)) (hi := (306578939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679384361363 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679384361363 / 500000000000) = 1/(500000000000 / 679384361363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_283 : Bounds (153289469 / 500000000) (306578939 / 1000000000) (Real.log (679384361363 / 500000000000)) := by
  have h := reflection_log_283_neg
  have he : Real.log (679384361363 / 500000000000) = -Real.log (500000000000 / 679384361363) := by
    rw [show ((679384361363 / 500000000000) : ℝ) = ((500000000000 / 679384361363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_284_neg : (153391839 / 500000000) ≤ -Real.log (250000000000 / 339761736259) ∧
    -Real.log (250000000000 / 339761736259) ≤ (306783679 / 1000000000) := by
  have h := checkLog_sound (w := (89761736259 / 589761736259)) (n := 12)
    (lo := (153391839 / 500000000)) (hi := (306783679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339761736259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339761736259 / 250000000000) = 1/(250000000000 / 339761736259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_284 : Bounds (153391839 / 500000000) (306783679 / 1000000000) (Real.log (339761736259 / 250000000000)) := by
  have h := reflection_log_284_neg
  have he : Real.log (339761736259 / 250000000000) = -Real.log (250000000000 / 339761736259) := by
    rw [show ((339761736259 / 250000000000) : ℝ) = ((250000000000 / 339761736259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_285_neg : (28351989 / 200000000) ≤ -Real.log (10000 / 11523) ∧
    -Real.log (10000 / 11523) ≤ (70879973 / 500000000) := by
  have h := checkLog_sound (w := (1523 / 21523)) (n := 12)
    (lo := (28351989 / 200000000)) (hi := (70879973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11523 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11523 / 10000) = 1/(10000 / 11523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_285 : Bounds (28351989 / 200000000) (70879973 / 500000000) (Real.log (11523 / 10000)) := by
  have h := reflection_log_285_neg
  have he : Real.log (11523 / 10000) = -Real.log (10000 / 11523) := by
    rw [show ((11523 / 10000) : ℝ) = ((10000 / 11523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_286_neg : (165228479 / 1000000000) ≤ -Real.log (8477 / 10000) ∧
    -Real.log (8477 / 10000) ≤ (516339 / 3125000) := by
  have h := checkLog_sound (w := (1523 / 18477)) (n := 12)
    (lo := (165228479 / 1000000000)) (hi := (516339 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8477) = 1/(8477 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_286 : Bounds (-516339 / 3125000) (-165228479 / 1000000000) (Real.log (8477 / 10000)) := by
  have h := reflection_log_286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_287_neg : (4759 / 31250000) ≤ -Real.log (10000000 / 10001523) ∧
    -Real.log (10000000 / 10001523) ≤ (152289 / 1000000000) := by
  have h := checkLog_sound (w := (1523 / 20001523)) (n := 12)
    (lo := (4759 / 31250000)) (hi := (152289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001523 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001523 / 10000000) = 1/(10000000 / 10001523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_287 : Bounds (4759 / 31250000) (152289 / 1000000000) (Real.log (10001523 / 10000000)) := by
  have h := reflection_log_287_neg
  have he : Real.log (10001523 / 10000000) = -Real.log (10000000 / 10001523) := by
    rw [show ((10001523 / 10000000) : ℝ) = ((10000000 / 10001523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_288_neg : (152311 / 1000000000) ≤ -Real.log (9998477 / 10000000) ∧
    -Real.log (9998477 / 10000000) ≤ (19039 / 125000000) := by
  have h := checkLog_sound (w := (1523 / 19998477)) (n := 12)
    (lo := (152311 / 1000000000)) (hi := (19039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998477) = 1/(9998477 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_288 : Bounds (-19039 / 125000000) (-152311 / 1000000000) (Real.log (9998477 / 10000000)) := by
  have h := reflection_log_288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_289_neg : (9219837 / 125000000) ≤ -Real.log (1000000 / 1076547) ∧
    -Real.log (1000000 / 1076547) ≤ (73758697 / 1000000000) := by
  have h := checkLog_sound (w := (76547 / 2076547)) (n := 12)
    (lo := (9219837 / 125000000)) (hi := (73758697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076547 / 1000000) = 1/(1000000 / 1076547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_289 : Bounds (9219837 / 125000000) (73758697 / 1000000000) (Real.log (1076547 / 1000000)) := by
  have h := reflection_log_289_neg
  have he : Real.log (1076547 / 1000000) = -Real.log (1000000 / 1076547) := by
    rw [show ((1076547 / 1000000) : ℝ) = ((1000000 / 1076547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_290_neg : (79635373 / 1000000000) ≤ -Real.log (923453 / 1000000) ∧
    -Real.log (923453 / 1000000) ≤ (39817687 / 500000000) := by
  have h := checkLog_sound (w := (76547 / 1923453)) (n := 12)
    (lo := (79635373 / 1000000000)) (hi := (39817687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923453) = 1/(923453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_290 : Bounds (-39817687 / 500000000) (-79635373 / 1000000000) (Real.log (923453 / 1000000)) := by
  have h := reflection_log_290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_291_neg : (5876677 / 1000000000) ≤ -Real.log (994140556791 / 1000000000000) ∧
    -Real.log (994140556791 / 1000000000000) ≤ (2938339 / 500000000) := by
  have h := checkLog_sound (w := (5859443209 / 1994140556791)) (n := 12)
    (lo := (5876677 / 1000000000)) (hi := (2938339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994140556791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994140556791) = 1/(994140556791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_291 : Bounds (-2938339 / 500000000) (-5876677 / 1000000000) (Real.log (994140556791 / 1000000000000)) := by
  have h := reflection_log_291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_292_neg : (38246421 / 250000000) ≤ -Real.log (500000000000 / 582654148297) ∧
    -Real.log (500000000000 / 582654148297) ≤ (30597137 / 200000000) := by
  have h := checkLog_sound (w := (82654148297 / 1082654148297)) (n := 12)
    (lo := (38246421 / 250000000)) (hi := (30597137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582654148297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582654148297 / 500000000000) = 1/(500000000000 / 582654148297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_292 : Bounds (38246421 / 250000000) (30597137 / 200000000) (Real.log (582654148297 / 500000000000)) := by
  have h := reflection_log_292_neg
  have he : Real.log (582654148297 / 500000000000) = -Real.log (500000000000 / 582654148297) := by
    rw [show ((582654148297 / 500000000000) : ℝ) = ((500000000000 / 582654148297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_293_neg : (15339407 / 100000000) ≤ -Real.log (250000000000 / 291446072513) ∧
    -Real.log (250000000000 / 291446072513) ≤ (153394071 / 1000000000) := by
  have h := checkLog_sound (w := (41446072513 / 541446072513)) (n := 12)
    (lo := (15339407 / 100000000)) (hi := (153394071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291446072513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291446072513 / 250000000000) = 1/(250000000000 / 291446072513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_293 : Bounds (15339407 / 100000000) (153394071 / 1000000000) (Real.log (291446072513 / 250000000000)) := by
  have h := reflection_log_293_neg
  have he : Real.log (291446072513 / 250000000000) = -Real.log (250000000000 / 291446072513) := by
    rw [show ((291446072513 / 250000000000) : ℝ) = ((250000000000 / 291446072513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_294_neg : (153391839 / 500000000) ≤ -Real.log (500000000000 / 679523472517) ∧
    -Real.log (500000000000 / 679523472517) ≤ (306783679 / 1000000000) := by
  have h := checkLog_sound (w := (179523472517 / 1179523472517)) (n := 12)
    (lo := (153391839 / 500000000)) (hi := (306783679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679523472517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679523472517 / 500000000000) = 1/(500000000000 / 679523472517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_294 : Bounds (153391839 / 500000000) (306783679 / 1000000000) (Real.log (679523472517 / 500000000000)) := by
  have h := reflection_log_294_neg
  have he : Real.log (679523472517 / 500000000000) = -Real.log (500000000000 / 679523472517) := by
    rw [show ((679523472517 / 500000000000) : ℝ) = ((500000000000 / 679523472517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_295_neg : (38373553 / 125000000) ≤ -Real.log (125000000000 / 169915654123) ∧
    -Real.log (125000000000 / 169915654123) ≤ (12279537 / 40000000) := by
  have h := checkLog_sound (w := (44915654123 / 294915654123)) (n := 12)
    (lo := (38373553 / 125000000)) (hi := (12279537 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169915654123 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169915654123 / 125000000000) = 1/(125000000000 / 169915654123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_295 : Bounds (38373553 / 125000000) (12279537 / 40000000) (Real.log (169915654123 / 125000000000)) := by
  have h := reflection_log_295_neg
  have he : Real.log (169915654123 / 125000000000) = -Real.log (125000000000 / 169915654123) := by
    rw [show ((169915654123 / 125000000000) : ℝ) = ((125000000000 / 169915654123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_296_neg : (35461681 / 250000000) ≤ -Real.log (2500 / 2881) ∧
    -Real.log (2500 / 2881) ≤ (5673869 / 40000000) := by
  have h := checkLog_sound (w := (381 / 5381)) (n := 12)
    (lo := (35461681 / 250000000)) (hi := (5673869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2881 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2881 / 2500) = 1/(2500 / 2881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_296 : Bounds (35461681 / 250000000) (5673869 / 40000000) (Real.log (2881 / 2500)) := by
  have h := reflection_log_296_neg
  have he : Real.log (2881 / 2500) = -Real.log (2500 / 2881) := by
    rw [show ((2881 / 2500) : ℝ) = ((2500 / 2881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_297_neg : (41336613 / 250000000) ≤ -Real.log (2119 / 2500) ∧
    -Real.log (2119 / 2500) ≤ (165346453 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 4619)) (n := 12)
    (lo := (41336613 / 250000000)) (hi := (165346453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2119) = 1/(2119 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_297 : Bounds (-165346453 / 1000000000) (-41336613 / 250000000) (Real.log (2119 / 2500)) := by
  have h := reflection_log_297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_298_neg : (38097 / 250000000) ≤ -Real.log (2500000 / 2500381) ∧
    -Real.log (2500000 / 2500381) ≤ (152389 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 5000381)) (n := 12)
    (lo := (38097 / 250000000)) (hi := (152389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500381 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500381 / 2500000) = 1/(2500000 / 2500381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_298 : Bounds (38097 / 250000000) (152389 / 1000000000) (Real.log (2500381 / 2500000)) := by
  have h := reflection_log_298_neg
  have he : Real.log (2500381 / 2500000) = -Real.log (2500000 / 2500381) := by
    rw [show ((2500381 / 2500000) : ℝ) = ((2500000 / 2500381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_299_neg : (152411 / 1000000000) ≤ -Real.log (2499619 / 2500000) ∧
    -Real.log (2499619 / 2500000) ≤ (38103 / 250000000) := by
  have h := checkLog_sound (w := (381 / 4999619)) (n := 12)
    (lo := (152411 / 1000000000)) (hi := (38103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499619) = 1/(2499619 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_299 : Bounds (-38103 / 250000000) (-152411 / 1000000000) (Real.log (2499619 / 2500000)) := by
  have h := reflection_log_299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_300_neg : (14723313 / 200000000) ≤ -Real.log (500000 / 538197) ∧
    -Real.log (500000 / 538197) ≤ (36808283 / 500000000) := by
  have h := checkLog_sound (w := (38197 / 1038197)) (n := 12)
    (lo := (14723313 / 200000000)) (hi := (36808283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538197 / 500000) = 1/(500000 / 538197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_300 : Bounds (14723313 / 200000000) (36808283 / 500000000) (Real.log (538197 / 500000)) := by
  have h := reflection_log_300_neg
  have he : Real.log (538197 / 500000) = -Real.log (500000 / 538197) := by
    rw [show ((538197 / 500000) : ℝ) = ((500000 / 538197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_301_neg : (15893941 / 200000000) ≤ -Real.log (461803 / 500000) ∧
    -Real.log (461803 / 500000) ≤ (39734853 / 500000000) := by
  have h := checkLog_sound (w := (38197 / 961803)) (n := 12)
    (lo := (15893941 / 200000000)) (hi := (39734853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461803) = 1/(461803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_301 : Bounds (-39734853 / 500000000) (-15893941 / 200000000) (Real.log (461803 / 500000)) := by
  have h := reflection_log_301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_302_neg : (73806069 / 1000000000) ≤ -Real.log (500000 / 538299) ∧
    -Real.log (500000 / 538299) ≤ (7380607 / 100000000) := by
  have h := checkLog_sound (w := (38299 / 1038299)) (n := 12)
    (lo := (73806069 / 1000000000)) (hi := (7380607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538299 / 500000) = 1/(500000 / 538299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_302 : Bounds (73806069 / 1000000000) (7380607 / 100000000) (Real.log (538299 / 500000)) := by
  have h := reflection_log_302_neg
  have he : Real.log (538299 / 500000) = -Real.log (500000 / 538299) := by
    rw [show ((538299 / 500000) : ℝ) = ((500000 / 538299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_303_neg : (79690603 / 1000000000) ≤ -Real.log (461701 / 500000) ∧
    -Real.log (461701 / 500000) ≤ (19922651 / 250000000) := by
  have h := checkLog_sound (w := (38299 / 961701)) (n := 12)
    (lo := (79690603 / 1000000000)) (hi := (19922651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461701) = 1/(461701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_303 : Bounds (-19922651 / 250000000) (-79690603 / 1000000000) (Real.log (461701 / 500000)) := by
  have h := reflection_log_303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_304_neg : (5884533 / 1000000000) ≤ -Real.log (248533186599 / 250000000000) ∧
    -Real.log (248533186599 / 250000000000) ≤ (2942267 / 500000000) := by
  have h := checkLog_sound (w := (1466813401 / 498533186599)) (n := 12)
    (lo := (5884533 / 1000000000)) (hi := (2942267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248533186599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248533186599) = 1/(248533186599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_304 : Bounds (-2942267 / 500000000) (-5884533 / 1000000000) (Real.log (248533186599 / 250000000000)) := by
  have h := reflection_log_304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_305_neg : (5853139 / 1000000000) ≤ -Real.log (248540989191 / 250000000000) ∧
    -Real.log (248540989191 / 250000000000) ≤ (292657 / 50000000) := by
  have h := checkLog_sound (w := (1459010809 / 498540989191)) (n := 12)
    (lo := (5853139 / 1000000000)) (hi := (292657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248540989191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248540989191) = 1/(248540989191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_305 : Bounds (-292657 / 50000000) (-5853139 / 1000000000) (Real.log (248540989191 / 250000000000)) := by
  have h := reflection_log_305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_306_neg : (15308627 / 100000000) ≤ -Real.log (50000000000 / 58271275847) ∧
    -Real.log (50000000000 / 58271275847) ≤ (153086271 / 1000000000) := by
  have h := checkLog_sound (w := (8271275847 / 108271275847)) (n := 12)
    (lo := (15308627 / 100000000)) (hi := (153086271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58271275847 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58271275847 / 50000000000) = 1/(50000000000 / 58271275847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_306 : Bounds (15308627 / 100000000) (153086271 / 1000000000) (Real.log (58271275847 / 50000000000)) := by
  have h := reflection_log_306_neg
  have he : Real.log (58271275847 / 50000000000) = -Real.log (50000000000 / 58271275847) := by
    rw [show ((58271275847 / 50000000000) : ℝ) = ((50000000000 / 58271275847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_307_neg : (4796771 / 31250000) ≤ -Real.log (250000000000 / 291475976877) ∧
    -Real.log (250000000000 / 291475976877) ≤ (153496673 / 1000000000) := by
  have h := checkLog_sound (w := (41475976877 / 541475976877)) (n := 12)
    (lo := (4796771 / 31250000)) (hi := (153496673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291475976877 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291475976877 / 250000000000) = 1/(250000000000 / 291475976877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_307 : Bounds (4796771 / 31250000) (153496673 / 1000000000) (Real.log (291475976877 / 250000000000)) := by
  have h := reflection_log_307_neg
  have he : Real.log (291475976877 / 250000000000) = -Real.log (250000000000 / 291475976877) := by
    rw [show ((291475976877 / 250000000000) : ℝ) = ((250000000000 / 291475976877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_308_neg : (38373553 / 125000000) ≤ -Real.log (500000000000 / 679662616491) ∧
    -Real.log (500000000000 / 679662616491) ≤ (12279537 / 40000000) := by
  have h := checkLog_sound (w := (179662616491 / 1179662616491)) (n := 12)
    (lo := (38373553 / 125000000)) (hi := (12279537 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679662616491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679662616491 / 500000000000) = 1/(500000000000 / 679662616491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_308 : Bounds (38373553 / 125000000) (12279537 / 40000000) (Real.log (679662616491 / 500000000000)) := by
  have h := reflection_log_308_neg
  have he : Real.log (679662616491 / 500000000000) = -Real.log (500000000000 / 679662616491) := by
    rw [show ((679662616491 / 500000000000) : ℝ) = ((500000000000 / 679662616491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_309_neg : (38399147 / 125000000) ≤ -Real.log (500000000000 / 679801793299) ∧
    -Real.log (500000000000 / 679801793299) ≤ (307193177 / 1000000000) := by
  have h := checkLog_sound (w := (179801793299 / 1179801793299)) (n := 12)
    (lo := (38399147 / 125000000)) (hi := (307193177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679801793299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679801793299 / 500000000000) = 1/(500000000000 / 679801793299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_309 : Bounds (38399147 / 125000000) (307193177 / 1000000000) (Real.log (679801793299 / 500000000000)) := by
  have h := reflection_log_309_neg
  have he : Real.log (679801793299 / 500000000000) = -Real.log (500000000000 / 679801793299) := by
    rw [show ((679801793299 / 500000000000) : ℝ) = ((500000000000 / 679801793299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_310_neg : (28386699 / 200000000) ≤ -Real.log (400 / 461) ∧
    -Real.log (400 / 461) ≤ (17741687 / 125000000) := by
  have h := checkLog_sound (w := (61 / 861)) (n := 12)
    (lo := (28386699 / 200000000)) (hi := (17741687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 400) = 1/(400 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_310 : Bounds (28386699 / 200000000) (17741687 / 125000000) (Real.log (461 / 400)) := by
  have h := reflection_log_310_neg
  have he : Real.log (461 / 400) = -Real.log (400 / 461) := by
    rw [show ((461 / 400) : ℝ) = ((400 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_311_neg : (165464439 / 1000000000) ≤ -Real.log (339 / 400) ∧
    -Real.log (339 / 400) ≤ (4136611 / 25000000) := by
  have h := checkLog_sound (w := (61 / 739)) (n := 12)
    (lo := (165464439 / 1000000000)) (hi := (4136611 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 339) = 1/(339 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_311 : Bounds (-4136611 / 25000000) (-165464439 / 1000000000) (Real.log (339 / 400)) := by
  have h := reflection_log_311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_312_neg : (19061 / 125000000) ≤ -Real.log (400000 / 400061) ∧
    -Real.log (400000 / 400061) ≤ (152489 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 800061)) (n := 12)
    (lo := (19061 / 125000000)) (hi := (152489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400061 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400061 / 400000) = 1/(400000 / 400061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_312 : Bounds (19061 / 125000000) (152489 / 1000000000) (Real.log (400061 / 400000)) := by
  have h := reflection_log_312_neg
  have he : Real.log (400061 / 400000) = -Real.log (400000 / 400061) := by
    rw [show ((400061 / 400000) : ℝ) = ((400000 / 400061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_313_neg : (152511 / 1000000000) ≤ -Real.log (399939 / 400000) ∧
    -Real.log (399939 / 400000) ≤ (2383 / 15625000) := by
  have h := checkLog_sound (w := (61 / 799939)) (n := 12)
    (lo := (152511 / 1000000000)) (hi := (2383 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399939) = 1/(399939 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_313 : Bounds (-2383 / 15625000) (-152511 / 1000000000) (Real.log (399939 / 400000)) := by
  have h := reflection_log_313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_314_neg : (14732789 / 200000000) ≤ -Real.log (200000 / 215289) ∧
    -Real.log (200000 / 215289) ≤ (36831973 / 500000000) := by
  have h := checkLog_sound (w := (15289 / 415289)) (n := 12)
    (lo := (14732789 / 200000000)) (hi := (36831973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215289 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215289 / 200000) = 1/(200000 / 215289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_314 : Bounds (14732789 / 200000000) (36831973 / 500000000) (Real.log (215289 / 200000)) := by
  have h := reflection_log_314_neg
  have he : Real.log (215289 / 200000) = -Real.log (200000 / 215289) := by
    rw [show ((215289 / 200000) : ℝ) = ((200000 / 215289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_315_neg : (3180997 / 40000000) ≤ -Real.log (184711 / 200000) ∧
    -Real.log (184711 / 200000) ≤ (39762463 / 500000000) := by
  have h := checkLog_sound (w := (15289 / 384711)) (n := 12)
    (lo := (3180997 / 40000000)) (hi := (39762463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184711) = 1/(184711 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_315 : Bounds (-39762463 / 500000000) (-3180997 / 40000000) (Real.log (184711 / 200000)) := by
  have h := reflection_log_315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_316_neg : (7385251 / 100000000) ≤ -Real.log (125000 / 134581) ∧
    -Real.log (125000 / 134581) ≤ (73852511 / 1000000000) := by
  have h := checkLog_sound (w := (9581 / 259581)) (n := 12)
    (lo := (7385251 / 100000000)) (hi := (73852511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134581 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134581 / 125000) = 1/(125000 / 134581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_316 : Bounds (7385251 / 100000000) (73852511 / 1000000000) (Real.log (134581 / 125000)) := by
  have h := reflection_log_316_neg
  have he : Real.log (134581 / 125000) = -Real.log (125000 / 134581) := by
    rw [show ((134581 / 125000) : ℝ) = ((125000 / 134581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_317_neg : (4984047 / 62500000) ≤ -Real.log (115419 / 125000) ∧
    -Real.log (115419 / 125000) ≤ (79744753 / 1000000000) := by
  have h := checkLog_sound (w := (9581 / 240419)) (n := 12)
    (lo := (4984047 / 62500000)) (hi := (79744753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115419) = 1/(115419 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_317 : Bounds (-79744753 / 1000000000) (-4984047 / 62500000) (Real.log (115419 / 125000)) := by
  have h := reflection_log_317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_318_neg : (5892241 / 1000000000) ≤ -Real.log (15533204439 / 15625000000) ∧
    -Real.log (15533204439 / 15625000000) ≤ (2946121 / 500000000) := by
  have h := checkLog_sound (w := (91795561 / 31158204439)) (n := 12)
    (lo := (5892241 / 1000000000)) (hi := (2946121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15533204439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15533204439) = 1/(15533204439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_318 : Bounds (-2946121 / 500000000) (-5892241 / 1000000000) (Real.log (15533204439 / 15625000000)) := by
  have h := reflection_log_318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_319_neg : (293049 / 50000000) ≤ -Real.log (39766246479 / 40000000000) ∧
    -Real.log (39766246479 / 40000000000) ≤ (5860981 / 1000000000) := by
  have h := checkLog_sound (w := (233753521 / 79766246479)) (n := 12)
    (lo := (293049 / 50000000)) (hi := (5860981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39766246479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39766246479) = 1/(39766246479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_319 : Bounds (-5860981 / 1000000000) (-293049 / 50000000) (Real.log (39766246479 / 40000000000)) := by
  have h := reflection_log_319_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
