import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0011
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

theorem reflection_log_1_neg : (202537203 / 500000000) ≤ -Real.log (5120 / 7677) ∧
    -Real.log (5120 / 7677) ≤ (405074407 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 12797)) (n := 12)
    (lo := (202537203 / 500000000)) (hi := (405074407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 5120) = 1/(5120 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (202537203 / 500000000) (405074407 / 1000000000) (Real.log (7677 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7677 / 5120) = -Real.log (5120 / 7677) := by
    rw [show ((7677 / 5120) : ℝ) = ((5120 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (691975991 / 1000000000) ≤ -Real.log (2563 / 5120) ∧
    -Real.log (2563 / 5120) ≤ (86496999 / 125000000) := by
  have h := checkLog_sound (w := (2557 / 7683)) (n := 12)
    (lo := (691975991 / 1000000000)) (hi := (86496999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2563) = 1/(2563 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) (Real.log (2563 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12646361 / 31250000) ≤ -Real.log (2560 / 3837) ∧
    -Real.log (2560 / 3837) ≤ (404683553 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 6397)) (n := 12)
    (lo := (12646361 / 31250000)) (hi := (404683553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3837 / 2560) = 1/(2560 / 3837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12646361 / 31250000) (404683553 / 1000000000) (Real.log (3837 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3837 / 2560) = -Real.log (2560 / 3837) := by
    rw [show ((3837 / 2560) : ℝ) = ((2560 / 3837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (172701543 / 250000000) ≤ -Real.log (1283 / 2560) ∧
    -Real.log (1283 / 2560) ≤ (690806173 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3843)) (n := 12)
    (lo := (172701543 / 250000000)) (hi := (690806173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1283) = 1/(1283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-690806173 / 1000000000) (-172701543 / 250000000) (Real.log (1283 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (692561071 / 1000000000) ≤ -Real.log (2560 / 5117) ∧
    -Real.log (2560 / 5117) ≤ (43285067 / 62500000) := by
  have h := checkLog_sound (w := (2557 / 7677)) (n := 12)
    (lo := (692561071 / 1000000000)) (hi := (43285067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5117 / 2560) = 1/(2560 / 5117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (692561071 / 1000000000) (43285067 / 62500000) (Real.log (5117 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5117 / 2560) = -Real.log (2560 / 5117) := by
    rw [show ((5117 / 2560) : ℝ) = ((2560 / 5117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6749150243 / 1000000000) ≤ -Real.log (3 / 2560) ∧
    -Real.log (3 / 2560) ≤ (6749150253 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(5 / 3) = 1/(3 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) (Real.log (3 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (345987309 / 500000000) ≤ -Real.log (1280 / 2557) ∧
    -Real.log (1280 / 2557) ≤ (691974619 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3837)) (n := 12)
    (lo := (345987309 / 500000000)) (hi := (691974619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2557 / 1280) = 1/(1280 / 2557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (345987309 / 500000000) (691974619 / 1000000000) (Real.log (2557 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2557 / 1280) = -Real.log (1280 / 2557) := by
    rw [show ((2557 / 1280) : ℝ) = ((1280 / 2557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6056003063 / 1000000000) ≤ -Real.log (3 / 1280) ∧
    -Real.log (3 / 1280) ≤ (11828131 / 1953125) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(5 / 3) = 1/(3 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-11828131 / 1953125) (-6056003063 / 1000000000) (Real.log (3 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (897071 / 1562500) ≤ -Real.log (1000000 / 1775577) ∧
    -Real.log (1000000 / 1775577) ≤ (574125441 / 1000000000) := by
  have h := checkLog_sound (w := (775577 / 2775577)) (n := 12)
    (lo := (897071 / 1562500)) (hi := (574125441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1775577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1775577 / 1000000) = 1/(1000000 / 1775577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (897071 / 1562500) (574125441 / 1000000000) (Real.log (1775577 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1775577 / 1000000) = -Real.log (1000000 / 1775577) := by
    rw [show ((1775577 / 1000000) : ℝ) = ((1000000 / 1775577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1494222613 / 1000000000) ≤ -Real.log (224423 / 1000000) ∧
    -Real.log (224423 / 1000000) ≤ (186777827 / 125000000) := by
  have h := checkLog_sound (w := (25577 / 474423)) (n := 12)
    (lo := (107928253 / 1000000000)) (hi := (53964127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224423) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 224423) = 1/(224423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186777827 / 125000000) (-1494222613 / 1000000000) (Real.log (224423 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143812097 / 250000000) ≤ -Real.log (250000 / 444393) ∧
    -Real.log (250000 / 444393) ≤ (575248389 / 1000000000) := by
  have h := checkLog_sound (w := (194393 / 694393)) (n := 12)
    (lo := (143812097 / 250000000)) (hi := (575248389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444393 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444393 / 250000) = 1/(250000 / 444393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143812097 / 250000000) (575248389 / 1000000000) (Real.log (444393 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (444393 / 250000) = -Real.log (250000 / 444393) := by
    rw [show ((444393 / 250000) : ℝ) = ((250000 / 444393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93946989 / 62500000) ≤ -Real.log (55607 / 250000) ∧
    -Real.log (55607 / 250000) ≤ (1503151827 / 1000000000) := by
  have h := checkLog_sound (w := (6893 / 118107)) (n := 12)
    (lo := (14607183 / 125000000)) (hi := (23371493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55607) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 55607) = 1/(55607 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1503151827 / 1000000000) (-93946989 / 62500000) (Real.log (55607 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12582711 / 25000000) ≤ -Real.log (200000 / 330837) ∧
    -Real.log (200000 / 330837) ≤ (503308441 / 1000000000) := by
  have h := checkLog_sound (w := (130837 / 530837)) (n := 12)
    (lo := (12582711 / 25000000)) (hi := (503308441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330837 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330837 / 200000) = 1/(200000 / 330837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12582711 / 25000000) (503308441 / 1000000000) (Real.log (330837 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (330837 / 200000) = -Real.log (200000 / 330837) := by
    rw [show ((330837 / 200000) : ℝ) = ((200000 / 330837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16591427 / 15625000) ≤ -Real.log (69163 / 200000) ∧
    -Real.log (69163 / 200000) ≤ (106185133 / 100000000) := by
  have h := checkLog_sound (w := (30837 / 169163)) (n := 12)
    (lo := (92176037 / 250000000)) (hi := (368704149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69163) = 1/(69163 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106185133 / 100000000) (-16591427 / 15625000) (Real.log (69163 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (504631479 / 1000000000) ≤ -Real.log (8000 / 13251) ∧
    -Real.log (8000 / 13251) ≤ (12615787 / 25000000) := by
  have h := checkLog_sound (w := (5251 / 21251)) (n := 12)
    (lo := (504631479 / 1000000000)) (hi := (12615787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13251 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13251 / 8000) = 1/(8000 / 13251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (504631479 / 1000000000) (12615787 / 25000000) (Real.log (13251 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13251 / 8000) = -Real.log (8000 / 13251) := by
    rw [show ((13251 / 8000) : ℝ) = ((8000 / 13251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1068204331 / 1000000000) ≤ -Real.log (2749 / 8000) ∧
    -Real.log (2749 / 8000) ≤ (1068204333 / 1000000000) := by
  have h := checkLog_sound (w := (1251 / 6749)) (n := 12)
    (lo := (375057151 / 1000000000)) (hi := (1465067 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2749) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 2749) = 1/(2749 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1068204333 / 1000000000) (-1068204331 / 1000000000) (Real.log (2749 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1034174027 / 500000000) ≤ -Real.log (50000000000 / 395587127879) ∧
    -Real.log (50000000000 / 395587127879) ≤ (2068348057 / 1000000000) := by
  have h := checkLog_sound (w := (195587127879 / 595587127879)) (n := 12)
    (lo := (341026847 / 500000000)) (hi := (136410739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395587127879 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(395587127879 / 200000000000) = 1/(50000000000 / 395587127879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1034174027 / 500000000) (2068348057 / 1000000000) (Real.log (395587127879 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (395587127879 / 50000000000) = -Real.log (50000000000 / 395587127879) := by
    rw [show ((395587127879 / 50000000000) : ℝ) = ((50000000000 / 395587127879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (519600053 / 250000000) ≤ -Real.log (500000000000 / 3995836855073) ∧
    -Real.log (500000000000 / 3995836855073) ≤ (415680043 / 200000000) := by
  have h := checkLog_sound (w := (1995836855073 / 5995836855073)) (n := 12)
    (lo := (173026463 / 250000000)) (hi := (692105853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3995836855073 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3995836855073 / 2000000000000) = 1/(500000000000 / 3995836855073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (519600053 / 250000000) (415680043 / 200000000) (Real.log (3995836855073 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3995836855073 / 500000000000) = -Real.log (500000000000 / 3995836855073) := by
    rw [show ((3995836855073 / 500000000000) : ℝ) = ((500000000000 / 3995836855073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (195644971 / 125000000) ≤ -Real.log (125000000000 / 597929890259) ∧
    -Real.log (125000000000 / 597929890259) ≤ (1565159771 / 1000000000) := by
  have h := checkLog_sound (w := (97929890259 / 1097929890259)) (n := 12)
    (lo := (698693 / 3906250)) (hi := (178865409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597929890259 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(597929890259 / 500000000000) = 1/(125000000000 / 597929890259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (195644971 / 125000000) (1565159771 / 1000000000) (Real.log (597929890259 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (597929890259 / 125000000000) = -Real.log (125000000000 / 597929890259) := by
    rw [show ((597929890259 / 125000000000) : ℝ) = ((125000000000 / 597929890259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (157283581 / 100000000) ≤ -Real.log (62500000000 / 301268643143) ∧
    -Real.log (62500000000 / 301268643143) ≤ (1572835813 / 1000000000) := by
  have h := checkLog_sound (w := (51268643143 / 551268643143)) (n := 12)
    (lo := (3730829 / 20000000)) (hi := (186541451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301268643143 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(301268643143 / 250000000000) = 1/(62500000000 / 301268643143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (157283581 / 100000000) (1572835813 / 1000000000) (Real.log (301268643143 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (301268643143 / 62500000000) = -Real.log (62500000000 / 301268643143) := by
    rw [show ((301268643143 / 62500000000) : ℝ) = ((62500000000 / 301268643143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0011
