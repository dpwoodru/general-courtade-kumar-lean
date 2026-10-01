import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4480_neg : (182283 / 1000000000) ≤ -Real.log (10000000 / 10001823) ∧
    -Real.log (10000000 / 10001823) ≤ (45571 / 250000000) := by
  have h := checkLog_sound (w := (1823 / 20001823)) (n := 12)
    (lo := (182283 / 1000000000)) (hi := (45571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001823 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001823 / 10000000) = 1/(10000000 / 10001823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4480 : Bounds (182283 / 1000000000) (45571 / 250000000) (Real.log (10001823 / 10000000)) := by
  have h := reflection_log_4480_neg
  have he : Real.log (10001823 / 10000000) = -Real.log (10000000 / 10001823) := by
    rw [show ((10001823 / 10000000) : ℝ) = ((10000000 / 10001823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4481_neg : (45579 / 250000000) ≤ -Real.log (9998177 / 10000000) ∧
    -Real.log (9998177 / 10000000) ≤ (182317 / 1000000000) := by
  have h := checkLog_sound (w := (1823 / 19998177)) (n := 12)
    (lo := (45579 / 250000000)) (hi := (182317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998177) = 1/(9998177 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4481 : Bounds (-182317 / 1000000000) (-45579 / 250000000) (Real.log (9998177 / 10000000)) := by
  have h := reflection_log_4481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4482_neg : (17521573 / 200000000) ≤ -Real.log (25000 / 27289) ∧
    -Real.log (25000 / 27289) ≤ (43803933 / 500000000) := by
  have h := checkLog_sound (w := (2289 / 52289)) (n := 12)
    (lo := (17521573 / 200000000)) (hi := (43803933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27289 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27289 / 25000) = 1/(25000 / 27289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4482 : Bounds (17521573 / 200000000) (43803933 / 500000000) (Real.log (27289 / 25000)) := by
  have h := reflection_log_4482_neg
  have he : Real.log (27289 / 25000) = -Real.log (25000 / 27289) := by
    rw [show ((27289 / 25000) : ℝ) = ((25000 / 27289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4483_neg : (24006609 / 250000000) ≤ -Real.log (22711 / 25000) ∧
    -Real.log (22711 / 25000) ≤ (96026437 / 1000000000) := by
  have h := checkLog_sound (w := (2289 / 47711)) (n := 12)
    (lo := (24006609 / 250000000)) (hi := (96026437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22711) = 1/(22711 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4483 : Bounds (-96026437 / 1000000000) (-24006609 / 250000000) (Real.log (22711 / 25000)) := by
  have h := reflection_log_4483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4484_neg : (43910649 / 500000000) ≤ -Real.log (1000000 / 1091793) ∧
    -Real.log (1000000 / 1091793) ≤ (87821299 / 1000000000) := by
  have h := checkLog_sound (w := (91793 / 2091793)) (n := 12)
    (lo := (43910649 / 500000000)) (hi := (87821299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091793 / 1000000) = 1/(1000000 / 1091793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4484 : Bounds (43910649 / 500000000) (87821299 / 1000000000) (Real.log (1091793 / 1000000)) := by
  have h := reflection_log_4484_neg
  have he : Real.log (1091793 / 1000000) = -Real.log (1000000 / 1091793) := by
    rw [show ((1091793 / 1000000) : ℝ) = ((1000000 / 1091793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4485_neg : (12035369 / 125000000) ≤ -Real.log (908207 / 1000000) ∧
    -Real.log (908207 / 1000000) ≤ (96282953 / 1000000000) := by
  have h := checkLog_sound (w := (91793 / 1908207)) (n := 12)
    (lo := (12035369 / 125000000)) (hi := (96282953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908207) = 1/(908207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4485 : Bounds (-96282953 / 1000000000) (-12035369 / 125000000) (Real.log (908207 / 1000000)) := by
  have h := reflection_log_4485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4486_neg : (8461653 / 1000000000) ≤ -Real.log (991574045151 / 1000000000000) ∧
    -Real.log (991574045151 / 1000000000000) ≤ (4230827 / 500000000) := by
  have h := checkLog_sound (w := (8425954849 / 1991574045151)) (n := 12)
    (lo := (8461653 / 1000000000)) (hi := (4230827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991574045151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991574045151) = 1/(991574045151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4486 : Bounds (-4230827 / 500000000) (-8461653 / 1000000000) (Real.log (991574045151 / 1000000000000)) := by
  have h := reflection_log_4486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4487_neg : (841857 / 100000000) ≤ -Real.log (619760479 / 625000000) ∧
    -Real.log (619760479 / 625000000) ≤ (8418571 / 1000000000) := by
  have h := checkLog_sound (w := (5239521 / 1244760479)) (n := 12)
    (lo := (841857 / 100000000)) (hi := (8418571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 619760479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 619760479) = 1/(619760479 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4487 : Bounds (-8418571 / 1000000000) (-841857 / 100000000) (Real.log (619760479 / 625000000)) := by
  have h := reflection_log_4487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4488_neg : (183634301 / 1000000000) ≤ -Real.log (20000000000 / 24031526573) ∧
    -Real.log (20000000000 / 24031526573) ≤ (91817151 / 500000000) := by
  have h := checkLog_sound (w := (4031526573 / 44031526573)) (n := 12)
    (lo := (183634301 / 1000000000)) (hi := (91817151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24031526573 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24031526573 / 20000000000) = 1/(20000000000 / 24031526573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4488 : Bounds (183634301 / 1000000000) (91817151 / 500000000) (Real.log (24031526573 / 20000000000)) := by
  have h := reflection_log_4488_neg
  have he : Real.log (24031526573 / 20000000000) = -Real.log (20000000000 / 24031526573) := by
    rw [show ((24031526573 / 20000000000) : ℝ) = ((20000000000 / 24031526573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4489_neg : (184104251 / 1000000000) ≤ -Real.log (500000000000 / 601070570917) ∧
    -Real.log (500000000000 / 601070570917) ≤ (46026063 / 250000000) := by
  have h := checkLog_sound (w := (101070570917 / 1101070570917)) (n := 12)
    (lo := (184104251 / 1000000000)) (hi := (46026063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601070570917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601070570917 / 500000000000) = 1/(500000000000 / 601070570917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4489 : Bounds (184104251 / 1000000000) (46026063 / 250000000) (Real.log (601070570917 / 500000000000)) := by
  have h := reflection_log_4489_neg
  have he : Real.log (601070570917 / 500000000000) = -Real.log (500000000000 / 601070570917) := by
    rw [show ((601070570917 / 500000000000) : ℝ) = ((500000000000 / 601070570917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4490_neg : (18425729 / 50000000) ≤ -Real.log (500000000000 / 722792858889) ∧
    -Real.log (500000000000 / 722792858889) ≤ (368514581 / 1000000000) := by
  have h := checkLog_sound (w := (222792858889 / 1222792858889)) (n := 12)
    (lo := (18425729 / 50000000)) (hi := (368514581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722792858889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722792858889 / 500000000000) = 1/(500000000000 / 722792858889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4490 : Bounds (18425729 / 50000000) (368514581 / 1000000000) (Real.log (722792858889 / 500000000000)) := by
  have h := reflection_log_4490_neg
  have he : Real.log (722792858889 / 500000000000) = -Real.log (500000000000 / 722792858889) := by
    rw [show ((722792858889 / 500000000000) : ℝ) = ((500000000000 / 722792858889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4491_neg : (368721451 / 1000000000) ≤ -Real.log (500000000000 / 722942399413) ∧
    -Real.log (500000000000 / 722942399413) ≤ (92180363 / 250000000) := by
  have h := checkLog_sound (w := (222942399413 / 1222942399413)) (n := 12)
    (lo := (368721451 / 1000000000)) (hi := (92180363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722942399413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722942399413 / 500000000000) = 1/(500000000000 / 722942399413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4491 : Bounds (368721451 / 1000000000) (92180363 / 250000000) (Real.log (722942399413 / 500000000000)) := by
  have h := reflection_log_4491_neg
  have he : Real.log (722942399413 / 500000000000) = -Real.log (500000000000 / 722942399413) := by
    rw [show ((722942399413 / 500000000000) : ℝ) = ((500000000000 / 722942399413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4492_neg : (167546271 / 1000000000) ≤ -Real.log (625 / 739) ∧
    -Real.log (625 / 739) ≤ (5235821 / 31250000) := by
  have h := checkLog_sound (w := (57 / 682)) (n := 12)
    (lo := (167546271 / 1000000000)) (hi := (5235821 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 625) = 1/(625 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4492 : Bounds (167546271 / 1000000000) (5235821 / 31250000) (Real.log (739 / 625)) := by
  have h := reflection_log_4492_neg
  have he : Real.log (739 / 625) = -Real.log (625 / 739) := by
    rw [show ((739 / 625) : ℝ) = ((625 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4493_neg : (201382059 / 1000000000) ≤ -Real.log (511 / 625) ∧
    -Real.log (511 / 625) ≤ (10069103 / 50000000) := by
  have h := checkLog_sound (w := (57 / 568)) (n := 12)
    (lo := (201382059 / 1000000000)) (hi := (10069103 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 511) = 1/(511 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4493 : Bounds (-10069103 / 50000000) (-201382059 / 1000000000) (Real.log (511 / 625)) := by
  have h := reflection_log_4493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4494_neg : (182383 / 1000000000) ≤ -Real.log (312500 / 312557) ∧
    -Real.log (312500 / 312557) ≤ (11399 / 62500000) := by
  have h := checkLog_sound (w := (57 / 625057)) (n := 12)
    (lo := (182383 / 1000000000)) (hi := (11399 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312557 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312557 / 312500) = 1/(312500 / 312557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4494 : Bounds (182383 / 1000000000) (11399 / 62500000) (Real.log (312557 / 312500)) := by
  have h := reflection_log_4494_neg
  have he : Real.log (312557 / 312500) = -Real.log (312500 / 312557) := by
    rw [show ((312557 / 312500) : ℝ) = ((312500 / 312557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4495_neg : (11401 / 62500000) ≤ -Real.log (312443 / 312500) ∧
    -Real.log (312443 / 312500) ≤ (182417 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 624943)) (n := 12)
    (lo := (11401 / 62500000)) (hi := (182417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312443) = 1/(312443 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4495 : Bounds (-182417 / 1000000000) (-11401 / 62500000) (Real.log (312443 / 312500)) := by
  have h := reflection_log_4495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4496_neg : (43827293 / 500000000) ≤ -Real.log (1000000 / 1091611) ∧
    -Real.log (1000000 / 1091611) ≤ (87654587 / 1000000000) := by
  have h := checkLog_sound (w := (91611 / 2091611)) (n := 12)
    (lo := (43827293 / 500000000)) (hi := (87654587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091611 / 1000000) = 1/(1000000 / 1091611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4496 : Bounds (43827293 / 500000000) (87654587 / 1000000000) (Real.log (1091611 / 1000000)) := by
  have h := reflection_log_4496_neg
  have he : Real.log (1091611 / 1000000) = -Real.log (1000000 / 1091611) := by
    rw [show ((1091611 / 1000000) : ℝ) = ((1000000 / 1091611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4497_neg : (48041289 / 500000000) ≤ -Real.log (908389 / 1000000) ∧
    -Real.log (908389 / 1000000) ≤ (96082579 / 1000000000) := by
  have h := checkLog_sound (w := (91611 / 1908389)) (n := 12)
    (lo := (48041289 / 500000000)) (hi := (96082579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908389) = 1/(908389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4497 : Bounds (-96082579 / 1000000000) (-48041289 / 500000000) (Real.log (908389 / 1000000)) := by
  have h := reflection_log_4497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4498_neg : (87868009 / 1000000000) ≤ -Real.log (250000 / 272961) ∧
    -Real.log (250000 / 272961) ≤ (8786801 / 100000000) := by
  have h := checkLog_sound (w := (22961 / 522961)) (n := 12)
    (lo := (87868009 / 1000000000)) (hi := (8786801 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272961 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272961 / 250000) = 1/(250000 / 272961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4498 : Bounds (87868009 / 1000000000) (8786801 / 100000000) (Real.log (272961 / 250000)) := by
  have h := reflection_log_4498_neg
  have he : Real.log (272961 / 250000) = -Real.log (250000 / 272961) := by
    rw [show ((272961 / 250000) : ℝ) = ((250000 / 272961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4499_neg : (24084777 / 250000000) ≤ -Real.log (227039 / 250000) ∧
    -Real.log (227039 / 250000) ≤ (96339109 / 1000000000) := by
  have h := checkLog_sound (w := (22961 / 477039)) (n := 12)
    (lo := (24084777 / 250000000)) (hi := (96339109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227039) = 1/(227039 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4499 : Bounds (-96339109 / 1000000000) (-24084777 / 250000000) (Real.log (227039 / 250000)) := by
  have h := reflection_log_4499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4500_neg : (4235549 / 500000000) ≤ -Real.log (61972792479 / 62500000000) ∧
    -Real.log (61972792479 / 62500000000) ≤ (8471099 / 1000000000) := by
  have h := checkLog_sound (w := (527207521 / 124472792479)) (n := 12)
    (lo := (4235549 / 500000000)) (hi := (8471099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61972792479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61972792479) = 1/(61972792479 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4500 : Bounds (-8471099 / 1000000000) (-4235549 / 500000000) (Real.log (61972792479 / 62500000000)) := by
  have h := reflection_log_4500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4501_neg : (8427991 / 1000000000) ≤ -Real.log (991607424679 / 1000000000000) ∧
    -Real.log (991607424679 / 1000000000000) ≤ (1053499 / 125000000) := by
  have h := checkLog_sound (w := (8392575321 / 1991607424679)) (n := 12)
    (lo := (8427991 / 1000000000)) (hi := (1053499 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991607424679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991607424679) = 1/(991607424679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4501 : Bounds (-1053499 / 125000000) (-8427991 / 1000000000) (Real.log (991607424679 / 1000000000000)) := by
  have h := reflection_log_4501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4502_neg : (45934291 / 250000000) ≤ -Real.log (250000000000 / 300424983129) ∧
    -Real.log (250000000000 / 300424983129) ≤ (36747433 / 200000000) := by
  have h := checkLog_sound (w := (50424983129 / 550424983129)) (n := 12)
    (lo := (45934291 / 250000000)) (hi := (36747433 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300424983129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300424983129 / 250000000000) = 1/(250000000000 / 300424983129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4502 : Bounds (45934291 / 250000000) (36747433 / 200000000) (Real.log (300424983129 / 250000000000)) := by
  have h := reflection_log_4502_neg
  have he : Real.log (300424983129 / 250000000000) = -Real.log (250000000000 / 300424983129) := by
    rw [show ((300424983129 / 250000000000) : ℝ) = ((250000000000 / 300424983129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4503_neg : (92103559 / 500000000) ≤ -Real.log (100000000000 / 120226480913) ∧
    -Real.log (100000000000 / 120226480913) ≤ (184207119 / 1000000000) := by
  have h := checkLog_sound (w := (20226480913 / 220226480913)) (n := 12)
    (lo := (92103559 / 500000000)) (hi := (184207119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120226480913 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120226480913 / 100000000000) = 1/(100000000000 / 120226480913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4503 : Bounds (92103559 / 500000000) (184207119 / 1000000000) (Real.log (120226480913 / 100000000000)) := by
  have h := reflection_log_4503_neg
  have he : Real.log (120226480913 / 100000000000) = -Real.log (100000000000 / 120226480913) := by
    rw [show ((120226480913 / 100000000000) : ℝ) = ((100000000000 / 120226480913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4504_neg : (368721451 / 1000000000) ≤ -Real.log (125000000000 / 180735599853) ∧
    -Real.log (125000000000 / 180735599853) ≤ (92180363 / 250000000) := by
  have h := checkLog_sound (w := (55735599853 / 305735599853)) (n := 12)
    (lo := (368721451 / 1000000000)) (hi := (92180363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180735599853 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180735599853 / 125000000000) = 1/(125000000000 / 180735599853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4504 : Bounds (368721451 / 1000000000) (92180363 / 250000000) (Real.log (180735599853 / 125000000000)) := by
  have h := reflection_log_4504_neg
  have he : Real.log (180735599853 / 125000000000) = -Real.log (125000000000 / 180735599853) := by
    rw [show ((180735599853 / 125000000000) : ℝ) = ((125000000000 / 180735599853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4505_neg : (36892833 / 100000000) ≤ -Real.log (500000000000 / 723091976517) ∧
    -Real.log (500000000000 / 723091976517) ≤ (368928331 / 1000000000) := by
  have h := checkLog_sound (w := (223091976517 / 1223091976517)) (n := 12)
    (lo := (36892833 / 100000000)) (hi := (368928331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723091976517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723091976517 / 500000000000) = 1/(500000000000 / 723091976517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4505 : Bounds (36892833 / 100000000) (368928331 / 1000000000) (Real.log (723091976517 / 500000000000)) := by
  have h := reflection_log_4505_neg
  have he : Real.log (723091976517 / 500000000000) = -Real.log (500000000000 / 723091976517) := by
    rw [show ((723091976517 / 500000000000) : ℝ) = ((500000000000 / 723091976517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4506_neg : (167630841 / 1000000000) ≤ -Real.log (400 / 473) ∧
    -Real.log (400 / 473) ≤ (83815421 / 500000000) := by
  have h := checkLog_sound (w := (73 / 873)) (n := 12)
    (lo := (167630841 / 1000000000)) (hi := (83815421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473 / 400) = 1/(400 / 473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4506 : Bounds (167630841 / 1000000000) (83815421 / 500000000) (Real.log (473 / 400)) := by
  have h := reflection_log_4506_neg
  have he : Real.log (473 / 400) = -Real.log (400 / 473) := by
    rw [show ((473 / 400) : ℝ) = ((400 / 473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4507_neg : (25188047 / 125000000) ≤ -Real.log (327 / 400) ∧
    -Real.log (327 / 400) ≤ (201504377 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 727)) (n := 12)
    (lo := (25188047 / 125000000)) (hi := (201504377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 327) = 1/(327 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4507 : Bounds (-201504377 / 1000000000) (-25188047 / 125000000) (Real.log (327 / 400)) := by
  have h := reflection_log_4507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4508_neg : (182483 / 1000000000) ≤ -Real.log (400000 / 400073) ∧
    -Real.log (400000 / 400073) ≤ (45621 / 250000000) := by
  have h := checkLog_sound (w := (73 / 800073)) (n := 12)
    (lo := (182483 / 1000000000)) (hi := (45621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400073 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400073 / 400000) = 1/(400000 / 400073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4508 : Bounds (182483 / 1000000000) (45621 / 250000000) (Real.log (400073 / 400000)) := by
  have h := reflection_log_4508_neg
  have he : Real.log (400073 / 400000) = -Real.log (400000 / 400073) := by
    rw [show ((400073 / 400000) : ℝ) = ((400000 / 400073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4509_neg : (45629 / 250000000) ≤ -Real.log (399927 / 400000) ∧
    -Real.log (399927 / 400000) ≤ (182517 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 799927)) (n := 12)
    (lo := (45629 / 250000000)) (hi := (182517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399927) = 1/(399927 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4509 : Bounds (-182517 / 1000000000) (-45629 / 250000000) (Real.log (399927 / 400000)) := by
  have h := reflection_log_4509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4510_neg : (87700389 / 1000000000) ≤ -Real.log (1000000 / 1091661) ∧
    -Real.log (1000000 / 1091661) ≤ (8770039 / 100000000) := by
  have h := checkLog_sound (w := (91661 / 2091661)) (n := 12)
    (lo := (87700389 / 1000000000)) (hi := (8770039 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091661 / 1000000) = 1/(1000000 / 1091661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4510 : Bounds (87700389 / 1000000000) (8770039 / 100000000) (Real.log (1091661 / 1000000)) := by
  have h := reflection_log_4510_neg
  have he : Real.log (1091661 / 1000000) = -Real.log (1000000 / 1091661) := by
    rw [show ((1091661 / 1000000) : ℝ) = ((1000000 / 1091661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4511_neg : (48068811 / 500000000) ≤ -Real.log (908339 / 1000000) ∧
    -Real.log (908339 / 1000000) ≤ (96137623 / 1000000000) := by
  have h := checkLog_sound (w := (91661 / 1908339)) (n := 12)
    (lo := (48068811 / 500000000)) (hi := (96137623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908339) = 1/(908339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4511 : Bounds (-96137623 / 1000000000) (-48068811 / 500000000) (Real.log (908339 / 1000000)) := by
  have h := reflection_log_4511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4512_neg : (43957359 / 500000000) ≤ -Real.log (200000 / 218379) ∧
    -Real.log (200000 / 218379) ≤ (87914719 / 1000000000) := by
  have h := checkLog_sound (w := (18379 / 418379)) (n := 12)
    (lo := (43957359 / 500000000)) (hi := (87914719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218379 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218379 / 200000) = 1/(200000 / 218379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4512 : Bounds (43957359 / 500000000) (87914719 / 1000000000) (Real.log (218379 / 200000)) := by
  have h := reflection_log_4512_neg
  have he : Real.log (218379 / 200000) = -Real.log (200000 / 218379) := by
    rw [show ((218379 / 200000) : ℝ) = ((200000 / 218379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4513_neg : (24098817 / 250000000) ≤ -Real.log (181621 / 200000) ∧
    -Real.log (181621 / 200000) ≤ (96395269 / 1000000000) := by
  have h := checkLog_sound (w := (18379 / 381621)) (n := 12)
    (lo := (24098817 / 250000000)) (hi := (96395269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181621) = 1/(181621 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4513 : Bounds (-96395269 / 1000000000) (-24098817 / 250000000) (Real.log (181621 / 200000)) := by
  have h := reflection_log_4513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4514_neg : (8480549 / 1000000000) ≤ -Real.log (39662212359 / 40000000000) ∧
    -Real.log (39662212359 / 40000000000) ≤ (169611 / 20000000) := by
  have h := checkLog_sound (w := (337787641 / 79662212359)) (n := 12)
    (lo := (8480549 / 1000000000)) (hi := (169611 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39662212359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39662212359) = 1/(39662212359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4514 : Bounds (-169611 / 20000000) (-8480549 / 1000000000) (Real.log (39662212359 / 40000000000)) := by
  have h := reflection_log_4514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4515_neg : (527327 / 62500000) ≤ -Real.log (991598261079 / 1000000000000) ∧
    -Real.log (991598261079 / 1000000000000) ≤ (8437233 / 1000000000) := by
  have h := checkLog_sound (w := (8401738921 / 1991598261079)) (n := 12)
    (lo := (527327 / 62500000)) (hi := (8437233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991598261079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991598261079) = 1/(991598261079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4515 : Bounds (-8437233 / 1000000000) (-527327 / 62500000) (Real.log (991598261079 / 1000000000000)) := by
  have h := reflection_log_4515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4516_neg : (183838011 / 1000000000) ≤ -Real.log (250000000000 / 300455281563) ∧
    -Real.log (250000000000 / 300455281563) ≤ (45959503 / 250000000) := by
  have h := checkLog_sound (w := (50455281563 / 550455281563)) (n := 12)
    (lo := (183838011 / 1000000000)) (hi := (45959503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300455281563 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300455281563 / 250000000000) = 1/(250000000000 / 300455281563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4516 : Bounds (183838011 / 1000000000) (45959503 / 250000000) (Real.log (300455281563 / 250000000000)) := by
  have h := reflection_log_4516_neg
  have he : Real.log (300455281563 / 250000000000) = -Real.log (250000000000 / 300455281563) := by
    rw [show ((300455281563 / 250000000000) : ℝ) = ((250000000000 / 300455281563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4517_neg : (184309987 / 1000000000) ≤ -Real.log (500000000000 / 601194245159) ∧
    -Real.log (500000000000 / 601194245159) ≤ (46077497 / 250000000) := by
  have h := checkLog_sound (w := (101194245159 / 1101194245159)) (n := 12)
    (lo := (184309987 / 1000000000)) (hi := (46077497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601194245159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601194245159 / 500000000000) = 1/(500000000000 / 601194245159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4517 : Bounds (184309987 / 1000000000) (46077497 / 250000000) (Real.log (601194245159 / 500000000000)) := by
  have h := reflection_log_4517_neg
  have he : Real.log (601194245159 / 500000000000) = -Real.log (500000000000 / 601194245159) := by
    rw [show ((601194245159 / 500000000000) : ℝ) = ((500000000000 / 601194245159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4518_neg : (36892833 / 100000000) ≤ -Real.log (125000000000 / 180772994129) ∧
    -Real.log (125000000000 / 180772994129) ≤ (368928331 / 1000000000) := by
  have h := checkLog_sound (w := (55772994129 / 305772994129)) (n := 12)
    (lo := (36892833 / 100000000)) (hi := (368928331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180772994129 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180772994129 / 125000000000) = 1/(125000000000 / 180772994129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4518 : Bounds (36892833 / 100000000) (368928331 / 1000000000) (Real.log (180772994129 / 125000000000)) := by
  have h := reflection_log_4518_neg
  have he : Real.log (180772994129 / 125000000000) = -Real.log (125000000000 / 180772994129) := by
    rw [show ((180772994129 / 125000000000) : ℝ) = ((125000000000 / 180772994129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4519_neg : (369135217 / 1000000000) ≤ -Real.log (100000000000 / 144648318043) ∧
    -Real.log (100000000000 / 144648318043) ≤ (184567609 / 500000000) := by
  have h := checkLog_sound (w := (44648318043 / 244648318043)) (n := 12)
    (lo := (369135217 / 1000000000)) (hi := (184567609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144648318043 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144648318043 / 100000000000) = 1/(100000000000 / 144648318043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4519 : Bounds (369135217 / 1000000000) (184567609 / 500000000) (Real.log (144648318043 / 100000000000)) := by
  have h := reflection_log_4519_neg
  have he : Real.log (144648318043 / 100000000000) = -Real.log (100000000000 / 144648318043) := by
    rw [show ((144648318043 / 100000000000) : ℝ) = ((100000000000 / 144648318043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4520_neg : (41928851 / 250000000) ≤ -Real.log (5000 / 5913) ∧
    -Real.log (5000 / 5913) ≤ (33543081 / 200000000) := by
  have h := checkLog_sound (w := (913 / 10913)) (n := 12)
    (lo := (41928851 / 250000000)) (hi := (33543081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5913 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5913 / 5000) = 1/(5000 / 5913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4520 : Bounds (41928851 / 250000000) (33543081 / 200000000) (Real.log (5913 / 5000)) := by
  have h := reflection_log_4520_neg
  have he : Real.log (5913 / 5000) = -Real.log (5000 / 5913) := by
    rw [show ((5913 / 5000) : ℝ) = ((5000 / 5913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4521_neg : (201626707 / 1000000000) ≤ -Real.log (4087 / 5000) ∧
    -Real.log (4087 / 5000) ≤ (50406677 / 250000000) := by
  have h := checkLog_sound (w := (913 / 9087)) (n := 12)
    (lo := (201626707 / 1000000000)) (hi := (50406677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4087) = 1/(4087 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4521 : Bounds (-50406677 / 250000000) (-201626707 / 1000000000) (Real.log (4087 / 5000)) := by
  have h := reflection_log_4521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4522_neg : (182583 / 1000000000) ≤ -Real.log (5000000 / 5000913) ∧
    -Real.log (5000000 / 5000913) ≤ (22823 / 125000000) := by
  have h := checkLog_sound (w := (913 / 10000913)) (n := 12)
    (lo := (182583 / 1000000000)) (hi := (22823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000913 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000913 / 5000000) = 1/(5000000 / 5000913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4522 : Bounds (182583 / 1000000000) (22823 / 125000000) (Real.log (5000913 / 5000000)) := by
  have h := reflection_log_4522_neg
  have he : Real.log (5000913 / 5000000) = -Real.log (5000000 / 5000913) := by
    rw [show ((5000913 / 5000000) : ℝ) = ((5000000 / 5000913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4523_neg : (22827 / 125000000) ≤ -Real.log (4999087 / 5000000) ∧
    -Real.log (4999087 / 5000000) ≤ (182617 / 1000000000) := by
  have h := checkLog_sound (w := (913 / 9999087)) (n := 12)
    (lo := (22827 / 125000000)) (hi := (182617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999087) = 1/(4999087 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4523 : Bounds (-182617 / 1000000000) (-22827 / 125000000) (Real.log (4999087 / 5000000)) := by
  have h := reflection_log_4523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4524_neg : (43873553 / 500000000) ≤ -Real.log (15625 / 17058) ∧
    -Real.log (15625 / 17058) ≤ (87747107 / 1000000000) := by
  have h := checkLog_sound (w := (1433 / 32683)) (n := 12)
    (lo := (43873553 / 500000000)) (hi := (87747107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17058 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17058 / 15625) = 1/(15625 / 17058) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4524 : Bounds (43873553 / 500000000) (87747107 / 1000000000) (Real.log (17058 / 15625)) := by
  have h := reflection_log_4524_neg
  have he : Real.log (17058 / 15625) = -Real.log (15625 / 17058) := by
    rw [show ((17058 / 15625) : ℝ) = ((15625 / 17058) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4525_neg : (9619377 / 100000000) ≤ -Real.log (14192 / 15625) ∧
    -Real.log (14192 / 15625) ≤ (96193771 / 1000000000) := by
  have h := checkLog_sound (w := (1433 / 29817)) (n := 12)
    (lo := (9619377 / 100000000)) (hi := (96193771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14192) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14192) = 1/(14192 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4525 : Bounds (-96193771 / 1000000000) (-9619377 / 100000000) (Real.log (14192 / 15625)) := by
  have h := reflection_log_4525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4526_neg : (3518457 / 40000000) ≤ -Real.log (500000 / 545973) ∧
    -Real.log (500000 / 545973) ≤ (43980713 / 500000000) := by
  have h := checkLog_sound (w := (45973 / 1045973)) (n := 12)
    (lo := (3518457 / 40000000)) (hi := (43980713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545973 / 500000) = 1/(500000 / 545973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4526 : Bounds (3518457 / 40000000) (43980713 / 500000000) (Real.log (545973 / 500000)) := by
  have h := reflection_log_4526_neg
  have he : Real.log (545973 / 500000) = -Real.log (500000 / 545973) := by
    rw [show ((545973 / 500000) : ℝ) = ((500000 / 545973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4527_neg : (9645143 / 100000000) ≤ -Real.log (454027 / 500000) ∧
    -Real.log (454027 / 500000) ≤ (96451431 / 1000000000) := by
  have h := checkLog_sound (w := (45973 / 954027)) (n := 12)
    (lo := (9645143 / 100000000)) (hi := (96451431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454027) = 1/(454027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4527 : Bounds (-96451431 / 1000000000) (-9645143 / 100000000) (Real.log (454027 / 500000)) := by
  have h := reflection_log_4527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4528_neg : (1698001 / 200000000) ≤ -Real.log (247886483271 / 250000000000) ∧
    -Real.log (247886483271 / 250000000000) ≤ (4245003 / 500000000) := by
  have h := checkLog_sound (w := (2113516729 / 497886483271)) (n := 12)
    (lo := (1698001 / 200000000)) (hi := (4245003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247886483271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247886483271) = 1/(247886483271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4528 : Bounds (-4245003 / 500000000) (-1698001 / 200000000) (Real.log (247886483271 / 250000000000)) := by
  have h := reflection_log_4528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4529_neg : (8446663 / 1000000000) ≤ -Real.log (242087136 / 244140625) ∧
    -Real.log (242087136 / 244140625) ≤ (1055833 / 125000000) := by
  have h := checkLog_sound (w := (2053489 / 486227761)) (n := 12)
    (lo := (8446663 / 1000000000)) (hi := (1055833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242087136) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242087136) = 1/(242087136 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4529 : Bounds (-1055833 / 125000000) (-8446663 / 1000000000) (Real.log (242087136 / 244140625)) := by
  have h := reflection_log_4529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4530_neg : (45985219 / 250000000) ≤ -Real.log (125000000000 / 150243094701) ∧
    -Real.log (125000000000 / 150243094701) ≤ (183940877 / 1000000000) := by
  have h := checkLog_sound (w := (25243094701 / 275243094701)) (n := 12)
    (lo := (45985219 / 250000000)) (hi := (183940877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150243094701 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150243094701 / 125000000000) = 1/(125000000000 / 150243094701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4530 : Bounds (45985219 / 250000000) (183940877 / 1000000000) (Real.log (150243094701 / 125000000000)) := by
  have h := reflection_log_4530_neg
  have he : Real.log (150243094701 / 125000000000) = -Real.log (125000000000 / 150243094701) := by
    rw [show ((150243094701 / 125000000000) : ℝ) = ((125000000000 / 150243094701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4531_neg : (23051607 / 125000000) ≤ -Real.log (5000000000 / 6012560927) ∧
    -Real.log (5000000000 / 6012560927) ≤ (184412857 / 1000000000) := by
  have h := checkLog_sound (w := (1012560927 / 11012560927)) (n := 12)
    (lo := (23051607 / 125000000)) (hi := (184412857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6012560927 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6012560927 / 5000000000) = 1/(5000000000 / 6012560927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4531 : Bounds (23051607 / 125000000) (184412857 / 1000000000) (Real.log (6012560927 / 5000000000)) := by
  have h := reflection_log_4531_neg
  have he : Real.log (6012560927 / 5000000000) = -Real.log (5000000000 / 6012560927) := by
    rw [show ((6012560927 / 5000000000) : ℝ) = ((5000000000 / 6012560927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4532_neg : (369135217 / 1000000000) ≤ -Real.log (250000000000 / 361620795107) ∧
    -Real.log (250000000000 / 361620795107) ≤ (184567609 / 500000000) := by
  have h := checkLog_sound (w := (111620795107 / 611620795107)) (n := 12)
    (lo := (369135217 / 1000000000)) (hi := (184567609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361620795107 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361620795107 / 250000000000) = 1/(250000000000 / 361620795107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4532 : Bounds (369135217 / 1000000000) (184567609 / 500000000) (Real.log (361620795107 / 250000000000)) := by
  have h := reflection_log_4532_neg
  have he : Real.log (361620795107 / 250000000000) = -Real.log (250000000000 / 361620795107) := by
    rw [show ((361620795107 / 250000000000) : ℝ) = ((250000000000 / 361620795107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4533_neg : (11541941 / 31250000) ≤ -Real.log (500000000000 / 723391240519) ∧
    -Real.log (500000000000 / 723391240519) ≤ (369342113 / 1000000000) := by
  have h := checkLog_sound (w := (223391240519 / 1223391240519)) (n := 12)
    (lo := (11541941 / 31250000)) (hi := (369342113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723391240519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723391240519 / 500000000000) = 1/(500000000000 / 723391240519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4533 : Bounds (11541941 / 31250000) (369342113 / 1000000000) (Real.log (723391240519 / 500000000000)) := by
  have h := reflection_log_4533_neg
  have he : Real.log (723391240519 / 500000000000) = -Real.log (500000000000 / 723391240519) := by
    rw [show ((723391240519 / 500000000000) : ℝ) = ((500000000000 / 723391240519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4534_neg : (4194999 / 25000000) ≤ -Real.log (10000 / 11827) ∧
    -Real.log (10000 / 11827) ≤ (167799961 / 1000000000) := by
  have h := checkLog_sound (w := (1827 / 21827)) (n := 12)
    (lo := (4194999 / 25000000)) (hi := (167799961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11827 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11827 / 10000) = 1/(10000 / 11827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4534 : Bounds (4194999 / 25000000) (167799961 / 1000000000) (Real.log (11827 / 10000)) := by
  have h := reflection_log_4534_neg
  have he : Real.log (11827 / 10000) = -Real.log (10000 / 11827) := by
    rw [show ((11827 / 10000) : ℝ) = ((10000 / 11827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4535_neg : (100874527 / 500000000) ≤ -Real.log (8173 / 10000) ∧
    -Real.log (8173 / 10000) ≤ (40349811 / 200000000) := by
  have h := checkLog_sound (w := (1827 / 18173)) (n := 12)
    (lo := (100874527 / 500000000)) (hi := (40349811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8173) = 1/(8173 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4535 : Bounds (-40349811 / 200000000) (-100874527 / 500000000) (Real.log (8173 / 10000)) := by
  have h := reflection_log_4535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4536_neg : (182683 / 1000000000) ≤ -Real.log (10000000 / 10001827) ∧
    -Real.log (10000000 / 10001827) ≤ (45671 / 250000000) := by
  have h := checkLog_sound (w := (1827 / 20001827)) (n := 12)
    (lo := (182683 / 1000000000)) (hi := (45671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001827 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001827 / 10000000) = 1/(10000000 / 10001827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4536 : Bounds (182683 / 1000000000) (45671 / 250000000) (Real.log (10001827 / 10000000)) := by
  have h := reflection_log_4536_neg
  have he : Real.log (10001827 / 10000000) = -Real.log (10000000 / 10001827) := by
    rw [show ((10001827 / 10000000) : ℝ) = ((10000000 / 10001827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4537_neg : (45679 / 250000000) ≤ -Real.log (9998173 / 10000000) ∧
    -Real.log (9998173 / 10000000) ≤ (182717 / 1000000000) := by
  have h := checkLog_sound (w := (1827 / 19998173)) (n := 12)
    (lo := (45679 / 250000000)) (hi := (182717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998173) = 1/(9998173 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4537 : Bounds (-182717 / 1000000000) (-45679 / 250000000) (Real.log (9998173 / 10000000)) := by
  have h := reflection_log_4537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4538_neg : (4389691 / 50000000) ≤ -Real.log (1000000 / 1091763) ∧
    -Real.log (1000000 / 1091763) ≤ (87793821 / 1000000000) := by
  have h := checkLog_sound (w := (91763 / 2091763)) (n := 12)
    (lo := (4389691 / 50000000)) (hi := (87793821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091763 / 1000000) = 1/(1000000 / 1091763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4538 : Bounds (4389691 / 50000000) (87793821 / 1000000000) (Real.log (1091763 / 1000000)) := by
  have h := reflection_log_4538_neg
  have he : Real.log (1091763 / 1000000) = -Real.log (1000000 / 1091763) := by
    rw [show ((1091763 / 1000000) : ℝ) = ((1000000 / 1091763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4539_neg : (96249921 / 1000000000) ≤ -Real.log (908237 / 1000000) ∧
    -Real.log (908237 / 1000000) ≤ (48124961 / 500000000) := by
  have h := checkLog_sound (w := (91763 / 1908237)) (n := 12)
    (lo := (96249921 / 1000000000)) (hi := (48124961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908237) = 1/(908237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4539 : Bounds (-48124961 / 500000000) (-96249921 / 1000000000) (Real.log (908237 / 1000000)) := by
  have h := reflection_log_4539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4540_neg : (8800813 / 100000000) ≤ -Real.log (1000000 / 1091997) ∧
    -Real.log (1000000 / 1091997) ≤ (88008131 / 1000000000) := by
  have h := checkLog_sound (w := (91997 / 2091997)) (n := 12)
    (lo := (8800813 / 100000000)) (hi := (88008131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091997 / 1000000) = 1/(1000000 / 1091997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4540 : Bounds (8800813 / 100000000) (88008131 / 1000000000) (Real.log (1091997 / 1000000)) := by
  have h := reflection_log_4540_neg
  have he : Real.log (1091997 / 1000000) = -Real.log (1000000 / 1091997) := by
    rw [show ((1091997 / 1000000) : ℝ) = ((1000000 / 1091997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4541_neg : (24126899 / 250000000) ≤ -Real.log (908003 / 1000000) ∧
    -Real.log (908003 / 1000000) ≤ (96507597 / 1000000000) := by
  have h := checkLog_sound (w := (91997 / 1908003)) (n := 12)
    (lo := (24126899 / 250000000)) (hi := (96507597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908003) = 1/(908003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4541 : Bounds (-96507597 / 1000000000) (-24126899 / 250000000) (Real.log (908003 / 1000000)) := by
  have h := reflection_log_4541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4542_neg : (4249733 / 500000000) ≤ -Real.log (991536551991 / 1000000000000) ∧
    -Real.log (991536551991 / 1000000000000) ≤ (8499467 / 1000000000) := by
  have h := checkLog_sound (w := (8463448009 / 1991536551991)) (n := 12)
    (lo := (4249733 / 500000000)) (hi := (8499467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991536551991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991536551991) = 1/(991536551991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4542 : Bounds (-8499467 / 1000000000) (-4249733 / 500000000) (Real.log (991536551991 / 1000000000000)) := by
  have h := reflection_log_4542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4543_neg : (84561 / 10000000) ≤ -Real.log (991579551831 / 1000000000000) ∧
    -Real.log (991579551831 / 1000000000000) ≤ (8456101 / 1000000000) := by
  have h := checkLog_sound (w := (8420448169 / 1991579551831)) (n := 12)
    (lo := (84561 / 10000000)) (hi := (8456101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991579551831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991579551831) = 1/(991579551831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4543 : Bounds (-8456101 / 1000000000) (-84561 / 10000000) (Real.log (991579551831 / 1000000000000)) := by
  have h := reflection_log_4543_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
