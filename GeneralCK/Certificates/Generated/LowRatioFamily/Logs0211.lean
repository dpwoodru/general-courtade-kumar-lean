import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13504_neg : (1227582669 / 1000000000) ≤ -Real.log (293 / 1000) ∧
    -Real.log (293 / 1000) ≤ (1227582671 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 793)) (n := 12)
    (lo := (534435489 / 1000000000)) (hi := (53443549 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 293) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 293) = 1/(293 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13504 : Bounds (-1227582671 / 1000000000) (-1227582669 / 1000000000) (Real.log (293 / 1000)) := by
  have h := reflection_log_13504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13505_neg : (2827 / 4000000) ≤ -Real.log (1000000 / 1000707) ∧
    -Real.log (1000000 / 1000707) ≤ (706751 / 1000000000) := by
  have h := checkLog_sound (w := (707 / 2000707)) (n := 12)
    (lo := (2827 / 4000000)) (hi := (706751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000707 / 1000000) = 1/(1000000 / 1000707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13505 : Bounds (2827 / 4000000) (706751 / 1000000000) (Real.log (1000707 / 1000000)) := by
  have h := reflection_log_13505_neg
  have he : Real.log (1000707 / 1000000) = -Real.log (1000000 / 1000707) := by
    rw [show ((1000707 / 1000000) : ℝ) = ((1000000 / 1000707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13506_neg : (2829 / 4000000) ≤ -Real.log (999293 / 1000000) ∧
    -Real.log (999293 / 1000000) ≤ (707251 / 1000000000) := by
  have h := checkLog_sound (w := (707 / 1999293)) (n := 12)
    (lo := (2829 / 4000000)) (hi := (707251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999293) = 1/(999293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13506 : Bounds (-707251 / 1000000000) (-2829 / 4000000) (Real.log (999293 / 1000000)) := by
  have h := reflection_log_13506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13507_neg : (41081467 / 125000000) ≤ -Real.log (500000 / 694547) ∧
    -Real.log (500000 / 694547) ≤ (328651737 / 1000000000) := by
  have h := checkLog_sound (w := (194547 / 1194547)) (n := 12)
    (lo := (41081467 / 125000000)) (hi := (328651737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694547 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694547 / 500000) = 1/(500000 / 694547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13507 : Bounds (41081467 / 125000000) (328651737 / 1000000000) (Real.log (694547 / 500000)) := by
  have h := reflection_log_13507_neg
  have he : Real.log (694547 / 500000) = -Real.log (500000 / 694547) := by
    rw [show ((694547 / 500000) : ℝ) = ((500000 / 694547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13508_neg : (492812177 / 1000000000) ≤ -Real.log (305453 / 500000) ∧
    -Real.log (305453 / 500000) ≤ (246406089 / 500000000) := by
  have h := checkLog_sound (w := (194547 / 805453)) (n := 12)
    (lo := (492812177 / 1000000000)) (hi := (246406089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305453) = 1/(305453 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13508 : Bounds (-246406089 / 500000000) (-492812177 / 1000000000) (Real.log (305453 / 500000)) := by
  have h := reflection_log_13508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13509_neg : (330572007 / 1000000000) ≤ -Real.log (250000 / 347941) ∧
    -Real.log (250000 / 347941) ≤ (41321501 / 125000000) := by
  have h := checkLog_sound (w := (97941 / 597941)) (n := 12)
    (lo := (330572007 / 1000000000)) (hi := (41321501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347941 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347941 / 250000) = 1/(250000 / 347941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13509 : Bounds (330572007 / 1000000000) (41321501 / 125000000) (Real.log (347941 / 250000)) := by
  have h := reflection_log_13509_neg
  have he : Real.log (347941 / 250000) = -Real.log (250000 / 347941) := by
    rw [show ((347941 / 250000) : ℝ) = ((250000 / 347941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13510_neg : (248596157 / 500000000) ≤ -Real.log (152059 / 250000) ∧
    -Real.log (152059 / 250000) ≤ (99438463 / 200000000) := by
  have h := checkLog_sound (w := (97941 / 402059)) (n := 12)
    (lo := (248596157 / 500000000)) (hi := (99438463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152059) = 1/(152059 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13510 : Bounds (-99438463 / 200000000) (-248596157 / 500000000) (Real.log (152059 / 250000)) := by
  have h := reflection_log_13510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13511_neg : (166620307 / 1000000000) ≤ -Real.log (52907560519 / 62500000000) ∧
    -Real.log (52907560519 / 62500000000) ≤ (41655077 / 250000000) := by
  have h := checkLog_sound (w := (9592439481 / 115407560519)) (n := 12)
    (lo := (166620307 / 1000000000)) (hi := (41655077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52907560519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52907560519) = 1/(52907560519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13511 : Bounds (-41655077 / 250000000) (-166620307 / 1000000000) (Real.log (52907560519 / 62500000000)) := by
  have h := reflection_log_13511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13512_neg : (164160441 / 1000000000) ≤ -Real.log (212151464791 / 250000000000) ∧
    -Real.log (212151464791 / 250000000000) ≤ (82080221 / 500000000) := by
  have h := checkLog_sound (w := (37848535209 / 462151464791)) (n := 12)
    (lo := (164160441 / 1000000000)) (hi := (82080221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 212151464791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 212151464791) = 1/(212151464791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13512 : Bounds (-82080221 / 500000000) (-164160441 / 1000000000) (Real.log (212151464791 / 250000000000)) := by
  have h := reflection_log_13512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13513_neg : (821463913 / 1000000000) ≤ -Real.log (100000000000 / 227382608781) ∧
    -Real.log (100000000000 / 227382608781) ≤ (164292783 / 200000000) := by
  have h := checkLog_sound (w := (27382608781 / 427382608781)) (n := 12)
    (lo := (128316733 / 1000000000)) (hi := (64158367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227382608781 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(227382608781 / 200000000000) = 1/(100000000000 / 227382608781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13513 : Bounds (821463913 / 1000000000) (164292783 / 200000000) (Real.log (227382608781 / 100000000000)) := by
  have h := reflection_log_13513_neg
  have he : Real.log (227382608781 / 100000000000) = -Real.log (100000000000 / 227382608781) := by
    rw [show ((227382608781 / 100000000000) : ℝ) = ((100000000000 / 227382608781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13514_neg : (827764321 / 1000000000) ≤ -Real.log (250000000000 / 572049336113) ∧
    -Real.log (250000000000 / 572049336113) ≤ (827764323 / 1000000000) := by
  have h := checkLog_sound (w := (72049336113 / 1072049336113)) (n := 12)
    (lo := (134617141 / 1000000000)) (hi := (67308571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572049336113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572049336113 / 500000000000) = 1/(250000000000 / 572049336113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13514 : Bounds (827764321 / 1000000000) (827764323 / 1000000000) (Real.log (572049336113 / 250000000000)) := by
  have h := reflection_log_13514_neg
  have he : Real.log (572049336113 / 250000000000) = -Real.log (250000000000 / 572049336113) := by
    rw [show ((572049336113 / 250000000000) : ℝ) = ((250000000000 / 572049336113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13515_neg : (1750374251 / 1000000000) ≤ -Real.log (250000000000 / 1439189189189) ∧
    -Real.log (250000000000 / 1439189189189) ≤ (875187127 / 500000000) := by
  have h := checkLog_sound (w := (439189189189 / 2439189189189)) (n := 12)
    (lo := (364079891 / 1000000000)) (hi := (91019973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439189189189 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1439189189189 / 1000000000000) = 1/(250000000000 / 1439189189189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13515 : Bounds (1750374251 / 1000000000) (875187127 / 500000000) (Real.log (1439189189189 / 250000000000)) := by
  have h := reflection_log_13515_neg
  have he : Real.log (1439189189189 / 250000000000) = -Real.log (250000000000 / 1439189189189) := by
    rw [show ((1439189189189 / 250000000000) : ℝ) = ((250000000000 / 1439189189189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13516_neg : (110145007 / 62500000) ≤ -Real.log (500000000000 / 2912969283277) ∧
    -Real.log (500000000000 / 2912969283277) ≤ (352464023 / 200000000) := by
  have h := checkLog_sound (w := (912969283277 / 4912969283277)) (n := 12)
    (lo := (47003219 / 125000000)) (hi := (376025753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2912969283277 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2912969283277 / 2000000000000) = 1/(500000000000 / 2912969283277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13516 : Bounds (110145007 / 62500000) (352464023 / 200000000) (Real.log (2912969283277 / 500000000000)) := by
  have h := reflection_log_13516_neg
  have he : Real.log (2912969283277 / 500000000000) = -Real.log (500000000000 / 2912969283277) := by
    rw [show ((2912969283277 / 500000000000) : ℝ) = ((500000000000 / 2912969283277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13517_neg : (53649337 / 100000000) ≤ -Real.log (100 / 171) ∧
    -Real.log (100 / 171) ≤ (536493371 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 271)) (n := 12)
    (lo := (53649337 / 100000000)) (hi := (536493371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 100) = 1/(100 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13517 : Bounds (53649337 / 100000000) (536493371 / 1000000000) (Real.log (171 / 100)) := by
  have h := reflection_log_13517_neg
  have he : Real.log (171 / 100) = -Real.log (100 / 171) := by
    rw [show ((171 / 100) : ℝ) = ((100 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13518_neg : (247574871 / 200000000) ≤ -Real.log (29 / 100) ∧
    -Real.log (29 / 100) ≤ (1237874357 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 79)) (n := 12)
    (lo := (21789087 / 40000000)) (hi := (68090897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 29) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 29) = 1/(29 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13518 : Bounds (-1237874357 / 1000000000) (-247574871 / 200000000) (Real.log (29 / 100)) := by
  have h := reflection_log_13518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13519_neg : (177437 / 250000000) ≤ -Real.log (100000 / 100071) ∧
    -Real.log (100000 / 100071) ≤ (709749 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 200071)) (n := 12)
    (lo := (177437 / 250000000)) (hi := (709749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100071 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100071 / 100000) = 1/(100000 / 100071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13519 : Bounds (177437 / 250000000) (709749 / 1000000000) (Real.log (100071 / 100000)) := by
  have h := reflection_log_13519_neg
  have he : Real.log (100071 / 100000) = -Real.log (100000 / 100071) := by
    rw [show ((100071 / 100000) : ℝ) = ((100000 / 100071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13520_neg : (177563 / 250000000) ≤ -Real.log (99929 / 100000) ∧
    -Real.log (99929 / 100000) ≤ (710253 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 199929)) (n := 12)
    (lo := (177563 / 250000000)) (hi := (710253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99929) = 1/(99929 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13520 : Bounds (-710253 / 1000000000) (-177563 / 250000000) (Real.log (99929 / 100000)) := by
  have h := reflection_log_13520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13521_neg : (330125711 / 1000000000) ≤ -Real.log (1000000 / 1391143) ∧
    -Real.log (1000000 / 1391143) ≤ (20632857 / 62500000) := by
  have h := checkLog_sound (w := (391143 / 2391143)) (n := 12)
    (lo := (330125711 / 1000000000)) (hi := (20632857 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391143 / 1000000) = 1/(1000000 / 1391143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13521 : Bounds (330125711 / 1000000000) (20632857 / 62500000) (Real.log (1391143 / 1000000)) := by
  have h := reflection_log_13521_neg
  have he : Real.log (1391143 / 1000000) = -Real.log (1000000 / 1391143) := by
    rw [show ((1391143 / 1000000) : ℝ) = ((1000000 / 1391143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13522_neg : (9923437 / 20000000) ≤ -Real.log (608857 / 1000000) ∧
    -Real.log (608857 / 1000000) ≤ (496171851 / 1000000000) := by
  have h := checkLog_sound (w := (391143 / 1608857)) (n := 12)
    (lo := (9923437 / 20000000)) (hi := (496171851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 608857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 608857) = 1/(608857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13522 : Bounds (-496171851 / 1000000000) (-9923437 / 20000000) (Real.log (608857 / 1000000)) := by
  have h := reflection_log_13522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13523_neg : (648533 / 1953125) ≤ -Real.log (1000000 / 1393821) ∧
    -Real.log (1000000 / 1393821) ≤ (332048897 / 1000000000) := by
  have h := checkLog_sound (w := (393821 / 2393821)) (n := 12)
    (lo := (648533 / 1953125)) (hi := (332048897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393821 / 1000000) = 1/(1000000 / 1393821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13523 : Bounds (648533 / 1953125) (332048897 / 1000000000) (Real.log (1393821 / 1000000)) := by
  have h := reflection_log_13523_neg
  have he : Real.log (1393821 / 1000000) = -Real.log (1000000 / 1393821) := by
    rw [show ((1393821 / 1000000) : ℝ) = ((1000000 / 1393821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13524_neg : (125144989 / 250000000) ≤ -Real.log (606179 / 1000000) ∧
    -Real.log (606179 / 1000000) ≤ (500579957 / 1000000000) := by
  have h := checkLog_sound (w := (393821 / 1606179)) (n := 12)
    (lo := (125144989 / 250000000)) (hi := (500579957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606179) = 1/(606179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13524 : Bounds (-500579957 / 1000000000) (-125144989 / 250000000) (Real.log (606179 / 1000000)) := by
  have h := reflection_log_13524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13525_neg : (8426553 / 50000000) ≤ -Real.log (844905019959 / 1000000000000) ∧
    -Real.log (844905019959 / 1000000000000) ≤ (168531061 / 1000000000) := by
  have h := checkLog_sound (w := (155094980041 / 1844905019959)) (n := 12)
    (lo := (8426553 / 50000000)) (hi := (168531061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 844905019959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 844905019959) = 1/(844905019959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13525 : Bounds (-168531061 / 1000000000) (-8426553 / 50000000) (Real.log (844905019959 / 1000000000000)) := by
  have h := reflection_log_13525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13526_neg : (83023069 / 500000000) ≤ -Real.log (847007153551 / 1000000000000) ∧
    -Real.log (847007153551 / 1000000000000) ≤ (166046139 / 1000000000) := by
  have h := checkLog_sound (w := (152992846449 / 1847007153551)) (n := 12)
    (lo := (83023069 / 500000000)) (hi := (166046139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 847007153551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 847007153551) = 1/(847007153551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13526 : Bounds (-166046139 / 1000000000) (-83023069 / 500000000) (Real.log (847007153551 / 1000000000000)) := by
  have h := reflection_log_13526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13527_neg : (20657439 / 25000000) ≤ -Real.log (62500000000 / 142802722971) ∧
    -Real.log (62500000000 / 142802722971) ≤ (413148781 / 500000000) := by
  have h := checkLog_sound (w := (17802722971 / 267802722971)) (n := 12)
    (lo := (6657519 / 50000000)) (hi := (133150381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142802722971 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(142802722971 / 125000000000) = 1/(62500000000 / 142802722971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13527 : Bounds (20657439 / 25000000) (413148781 / 500000000) (Real.log (142802722971 / 62500000000)) := by
  have h := reflection_log_13527_neg
  have he : Real.log (142802722971 / 62500000000) = -Real.log (62500000000 / 142802722971) := by
    rw [show ((142802722971 / 62500000000) : ℝ) = ((62500000000 / 142802722971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13528_neg : (832628853 / 1000000000) ≤ -Real.log (100000000000 / 229935547091) ∧
    -Real.log (100000000000 / 229935547091) ≤ (166525771 / 200000000) := by
  have h := checkLog_sound (w := (29935547091 / 429935547091)) (n := 12)
    (lo := (139481673 / 1000000000)) (hi := (69740837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229935547091 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(229935547091 / 200000000000) = 1/(100000000000 / 229935547091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13528 : Bounds (832628853 / 1000000000) (166525771 / 200000000) (Real.log (229935547091 / 100000000000)) := by
  have h := reflection_log_13528_neg
  have he : Real.log (229935547091 / 100000000000) = -Real.log (100000000000 / 229935547091) := by
    rw [show ((229935547091 / 100000000000) : ℝ) = ((100000000000 / 229935547091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13529_neg : (110145007 / 62500000) ≤ -Real.log (125000000000 / 728242320819) ∧
    -Real.log (125000000000 / 728242320819) ≤ (352464023 / 200000000) := by
  have h := checkLog_sound (w := (228242320819 / 1228242320819)) (n := 12)
    (lo := (47003219 / 125000000)) (hi := (376025753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728242320819 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(728242320819 / 500000000000) = 1/(125000000000 / 728242320819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13529 : Bounds (110145007 / 62500000) (352464023 / 200000000) (Real.log (728242320819 / 125000000000)) := by
  have h := reflection_log_13529_neg
  have he : Real.log (728242320819 / 125000000000) = -Real.log (125000000000 / 728242320819) := by
    rw [show ((728242320819 / 125000000000) : ℝ) = ((125000000000 / 728242320819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13530_neg : (70974709 / 40000000) ≤ -Real.log (500000000000 / 2948275862069) ∧
    -Real.log (500000000000 / 2948275862069) ≤ (110897983 / 62500000) := by
  have h := checkLog_sound (w := (948275862069 / 4948275862069)) (n := 12)
    (lo := (77614673 / 200000000)) (hi := (194036683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2948275862069 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2948275862069 / 2000000000000) = 1/(500000000000 / 2948275862069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13530 : Bounds (70974709 / 40000000) (110897983 / 62500000) (Real.log (2948275862069 / 500000000000)) := by
  have h := reflection_log_13530_neg
  have he : Real.log (2948275862069 / 500000000000) = -Real.log (500000000000 / 2948275862069) := by
    rw [show ((2948275862069 / 500000000000) : ℝ) = ((500000000000 / 2948275862069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13531_neg : (538246219 / 1000000000) ≤ -Real.log (1000 / 1713) ∧
    -Real.log (1000 / 1713) ≤ (26912311 / 50000000) := by
  have h := checkLog_sound (w := (713 / 2713)) (n := 12)
    (lo := (538246219 / 1000000000)) (hi := (26912311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1000) = 1/(1000 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13531 : Bounds (538246219 / 1000000000) (26912311 / 50000000) (Real.log (1713 / 1000)) := by
  have h := reflection_log_13531_neg
  have he : Real.log (1713 / 1000) = -Real.log (1000 / 1713) := by
    rw [show ((1713 / 1000) : ℝ) = ((1000 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13532_neg : (624136531 / 500000000) ≤ -Real.log (287 / 1000) ∧
    -Real.log (287 / 1000) ≤ (156034133 / 125000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 287) = 1/(287 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13532 : Bounds (-156034133 / 125000000) (-624136531 / 500000000) (Real.log (287 / 1000)) := by
  have h := reflection_log_13532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13533_neg : (142549 / 200000000) ≤ -Real.log (1000000 / 1000713) ∧
    -Real.log (1000000 / 1000713) ≤ (356373 / 500000000) := by
  have h := checkLog_sound (w := (713 / 2000713)) (n := 12)
    (lo := (142549 / 200000000)) (hi := (356373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000713 / 1000000) = 1/(1000000 / 1000713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13533 : Bounds (142549 / 200000000) (356373 / 500000000) (Real.log (1000713 / 1000000)) := by
  have h := reflection_log_13533_neg
  have he : Real.log (1000713 / 1000000) = -Real.log (1000000 / 1000713) := by
    rw [show ((1000713 / 1000000) : ℝ) = ((1000000 / 1000713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13534_neg : (356627 / 500000000) ≤ -Real.log (999287 / 1000000) ∧
    -Real.log (999287 / 1000000) ≤ (142651 / 200000000) := by
  have h := checkLog_sound (w := (713 / 1999287)) (n := 12)
    (lo := (356627 / 500000000)) (hi := (142651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999287) = 1/(999287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13534 : Bounds (-142651 / 200000000) (-356627 / 500000000) (Real.log (999287 / 1000000)) := by
  have h := reflection_log_13534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13535_neg : (331601823 / 1000000000) ≤ -Real.log (500000 / 696599) ∧
    -Real.log (500000 / 696599) ≤ (10362557 / 31250000) := by
  have h := checkLog_sound (w := (196599 / 1196599)) (n := 12)
    (lo := (331601823 / 1000000000)) (hi := (10362557 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696599 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696599 / 500000) = 1/(500000 / 696599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13535 : Bounds (331601823 / 1000000000) (10362557 / 31250000) (Real.log (696599 / 500000)) := by
  have h := reflection_log_13535_neg
  have he : Real.log (696599 / 500000) = -Real.log (500000 / 696599) := by
    rw [show ((696599 / 500000) : ℝ) = ((500000 / 696599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13536_neg : (99910547 / 200000000) ≤ -Real.log (303401 / 500000) ∧
    -Real.log (303401 / 500000) ≤ (15611023 / 31250000) := by
  have h := checkLog_sound (w := (196599 / 803401)) (n := 12)
    (lo := (99910547 / 200000000)) (hi := (15611023 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303401) = 1/(303401 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13536 : Bounds (-15611023 / 31250000) (-99910547 / 200000000) (Real.log (303401 / 500000)) := by
  have h := reflection_log_13536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13537_neg : (166763953 / 500000000) ≤ -Real.log (250000 / 348971) ∧
    -Real.log (250000 / 348971) ≤ (333527907 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 598971)) (n := 12)
    (lo := (166763953 / 500000000)) (hi := (333527907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348971 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348971 / 250000) = 1/(250000 / 348971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13537 : Bounds (166763953 / 500000000) (333527907 / 1000000000) (Real.log (348971 / 250000)) := by
  have h := reflection_log_13537_neg
  have he : Real.log (348971 / 250000) = -Real.log (250000 / 348971) := by
    rw [show ((348971 / 250000) : ℝ) = ((250000 / 348971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13538_neg : (251994523 / 500000000) ≤ -Real.log (151029 / 250000) ∧
    -Real.log (151029 / 250000) ≤ (503989047 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 401029)) (n := 12)
    (lo := (251994523 / 500000000)) (hi := (503989047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 151029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 151029) = 1/(151029 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13538 : Bounds (-503989047 / 1000000000) (-251994523 / 500000000) (Real.log (151029 / 250000)) := by
  have h := reflection_log_13538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13539_neg : (8523057 / 50000000) ≤ -Real.log (52704741159 / 62500000000) ∧
    -Real.log (52704741159 / 62500000000) ≤ (170461141 / 1000000000) := by
  have h := checkLog_sound (w := (9795258841 / 115204741159)) (n := 12)
    (lo := (8523057 / 50000000)) (hi := (170461141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 52704741159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 52704741159) = 1/(52704741159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13539 : Bounds (-170461141 / 1000000000) (-8523057 / 50000000) (Real.log (52704741159 / 62500000000)) := by
  have h := reflection_log_13539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13540_neg : (167950911 / 1000000000) ≤ -Real.log (211348833199 / 250000000000) ∧
    -Real.log (211348833199 / 250000000000) ≤ (2624233 / 15625000) := by
  have h := checkLog_sound (w := (38651166801 / 461348833199)) (n := 12)
    (lo := (167950911 / 1000000000)) (hi := (2624233 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 211348833199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 211348833199) = 1/(211348833199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13540 : Bounds (-2624233 / 15625000) (-167950911 / 1000000000) (Real.log (211348833199 / 250000000000)) := by
  have h := reflection_log_13540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13541_neg : (415577279 / 500000000) ≤ -Real.log (250000000000 / 573992010573) ∧
    -Real.log (250000000000 / 573992010573) ≤ (1298679 / 1562500) := by
  have h := checkLog_sound (w := (73992010573 / 1073992010573)) (n := 12)
    (lo := (69003689 / 500000000)) (hi := (138007379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573992010573 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(573992010573 / 500000000000) = 1/(250000000000 / 573992010573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13541 : Bounds (415577279 / 500000000) (1298679 / 1562500) (Real.log (573992010573 / 250000000000)) := by
  have h := reflection_log_13541_neg
  have he : Real.log (573992010573 / 250000000000) = -Real.log (250000000000 / 573992010573) := by
    rw [show ((573992010573 / 250000000000) : ℝ) = ((250000000000 / 573992010573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13542_neg : (104689619 / 125000000) ≤ -Real.log (250000000000 / 577655615809) ∧
    -Real.log (250000000000 / 577655615809) ≤ (418758477 / 500000000) := by
  have h := checkLog_sound (w := (77655615809 / 1077655615809)) (n := 12)
    (lo := (36092443 / 250000000)) (hi := (144369773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577655615809 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(577655615809 / 500000000000) = 1/(250000000000 / 577655615809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13542 : Bounds (104689619 / 125000000) (418758477 / 500000000) (Real.log (577655615809 / 250000000000)) := by
  have h := reflection_log_13542_neg
  have he : Real.log (577655615809 / 250000000000) = -Real.log (250000000000 / 577655615809) := by
    rw [show ((577655615809 / 250000000000) : ℝ) = ((250000000000 / 577655615809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13543_neg : (70974709 / 40000000) ≤ -Real.log (125000000000 / 737068965517) ∧
    -Real.log (125000000000 / 737068965517) ≤ (110897983 / 62500000) := by
  have h := checkLog_sound (w := (237068965517 / 1237068965517)) (n := 12)
    (lo := (77614673 / 200000000)) (hi := (194036683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737068965517 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(737068965517 / 500000000000) = 1/(125000000000 / 737068965517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13543 : Bounds (70974709 / 40000000) (110897983 / 62500000) (Real.log (737068965517 / 125000000000)) := by
  have h := reflection_log_13543_neg
  have he : Real.log (737068965517 / 125000000000) = -Real.log (125000000000 / 737068965517) := by
    rw [show ((737068965517 / 125000000000) : ℝ) = ((125000000000 / 737068965517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13544_neg : (1786519281 / 1000000000) ≤ -Real.log (125000000000 / 746080139373) ∧
    -Real.log (125000000000 / 746080139373) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (246080139373 / 1246080139373)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746080139373 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(746080139373 / 500000000000) = 1/(125000000000 / 746080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13544 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (746080139373 / 125000000000)) := by
  have h := reflection_log_13544_neg
  have he : Real.log (746080139373 / 125000000000) = -Real.log (125000000000 / 746080139373) := by
    rw [show ((746080139373 / 125000000000) : ℝ) = ((125000000000 / 746080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13545_neg : (539996001 / 1000000000) ≤ -Real.log (250 / 429) ∧
    -Real.log (250 / 429) ≤ (269998001 / 500000000) := by
  have h := checkLog_sound (w := (179 / 679)) (n := 12)
    (lo := (539996001 / 1000000000)) (hi := (269998001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 250) = 1/(250 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13545 : Bounds (539996001 / 1000000000) (269998001 / 500000000) (Real.log (429 / 250)) := by
  have h := reflection_log_13545_neg
  have he : Real.log (429 / 250) = -Real.log (250 / 429) := by
    rw [show ((429 / 250) : ℝ) = ((250 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13546_neg : (15734763 / 12500000) ≤ -Real.log (71 / 250) ∧
    -Real.log (71 / 250) ≤ (629390521 / 500000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 71) = 1/(71 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13546 : Bounds (-629390521 / 500000000) (-15734763 / 12500000) (Real.log (71 / 250)) := by
  have h := reflection_log_13546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13547_neg : (715743 / 1000000000) ≤ -Real.log (250000 / 250179) ∧
    -Real.log (250000 / 250179) ≤ (22367 / 31250000) := by
  have h := checkLog_sound (w := (179 / 500179)) (n := 12)
    (lo := (715743 / 1000000000)) (hi := (22367 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250179 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250179 / 250000) = 1/(250000 / 250179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13547 : Bounds (715743 / 1000000000) (22367 / 31250000) (Real.log (250179 / 250000)) := by
  have h := reflection_log_13547_neg
  have he : Real.log (250179 / 250000) = -Real.log (250000 / 250179) := by
    rw [show ((250179 / 250000) : ℝ) = ((250000 / 250179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13548_neg : (22383 / 31250000) ≤ -Real.log (249821 / 250000) ∧
    -Real.log (249821 / 250000) ≤ (716257 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 499821)) (n := 12)
    (lo := (22383 / 31250000)) (hi := (716257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249821) = 1/(249821 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13548 : Bounds (-716257 / 1000000000) (-22383 / 31250000) (Real.log (249821 / 250000)) := by
  have h := reflection_log_13548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13549_neg : (333080777 / 1000000000) ≤ -Real.log (50000 / 69763) ∧
    -Real.log (50000 / 69763) ≤ (166540389 / 500000000) := by
  have h := checkLog_sound (w := (19763 / 119763)) (n := 12)
    (lo := (333080777 / 1000000000)) (hi := (166540389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69763 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69763 / 50000) = 1/(50000 / 69763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13549 : Bounds (333080777 / 1000000000) (166540389 / 500000000) (Real.log (69763 / 50000)) := by
  have h := reflection_log_13549_neg
  have he : Real.log (69763 / 50000) = -Real.log (50000 / 69763) := by
    rw [show ((69763 / 50000) : ℝ) = ((50000 / 69763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13550_neg : (100591333 / 200000000) ≤ -Real.log (30237 / 50000) ∧
    -Real.log (30237 / 50000) ≤ (251478333 / 500000000) := by
  have h := checkLog_sound (w := (19763 / 80237)) (n := 12)
    (lo := (100591333 / 200000000)) (hi := (251478333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 30237) = 1/(30237 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13550 : Bounds (-251478333 / 500000000) (-100591333 / 200000000) (Real.log (30237 / 50000)) := by
  have h := reflection_log_13550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13551_neg : (167505227 / 500000000) ≤ -Real.log (200000 / 279591) ∧
    -Real.log (200000 / 279591) ≤ (67002091 / 200000000) := by
  have h := checkLog_sound (w := (79591 / 479591)) (n := 12)
    (lo := (167505227 / 500000000)) (hi := (67002091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279591 / 200000) = 1/(200000 / 279591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13551 : Bounds (167505227 / 500000000) (67002091 / 200000000) (Real.log (279591 / 200000)) := by
  have h := reflection_log_13551_neg
  have he : Real.log (279591 / 200000) = -Real.log (200000 / 279591) := by
    rw [show ((279591 / 200000) : ℝ) = ((200000 / 279591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13552_neg : (101484617 / 200000000) ≤ -Real.log (120409 / 200000) ∧
    -Real.log (120409 / 200000) ≤ (253711543 / 500000000) := by
  have h := checkLog_sound (w := (79591 / 320409)) (n := 12)
    (lo := (101484617 / 200000000)) (hi := (253711543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120409) = 1/(120409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13552 : Bounds (-253711543 / 500000000) (-101484617 / 200000000) (Real.log (120409 / 200000)) := by
  have h := reflection_log_13552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13553_neg : (172412631 / 1000000000) ≤ -Real.log (33665272719 / 40000000000) ∧
    -Real.log (33665272719 / 40000000000) ≤ (21551579 / 125000000) := by
  have h := checkLog_sound (w := (6334727281 / 73665272719)) (n := 12)
    (lo := (172412631 / 1000000000)) (hi := (21551579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 33665272719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 33665272719) = 1/(33665272719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13553 : Bounds (-21551579 / 125000000) (-172412631 / 1000000000) (Real.log (33665272719 / 40000000000)) := by
  have h := reflection_log_13553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13554_neg : (169875887 / 1000000000) ≤ -Real.log (2109423831 / 2500000000) ∧
    -Real.log (2109423831 / 2500000000) ≤ (10617243 / 62500000) := by
  have h := checkLog_sound (w := (390576169 / 4609423831)) (n := 12)
    (lo := (169875887 / 1000000000)) (hi := (10617243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2109423831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2109423831) = 1/(2109423831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13554 : Bounds (-10617243 / 62500000) (-169875887 / 1000000000) (Real.log (2109423831 / 2500000000)) := by
  have h := reflection_log_13554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13555_neg : (418018721 / 500000000) ≤ -Real.log (4000000000 / 9228825611) ∧
    -Real.log (4000000000 / 9228825611) ≤ (209009361 / 250000000) := by
  have h := checkLog_sound (w := (1228825611 / 17228825611)) (n := 12)
    (lo := (71445131 / 500000000)) (hi := (142890263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9228825611 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9228825611 / 8000000000) = 1/(4000000000 / 9228825611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13555 : Bounds (418018721 / 500000000) (209009361 / 250000000) (Real.log (9228825611 / 4000000000)) := by
  have h := reflection_log_13555_neg
  have he : Real.log (9228825611 / 4000000000) = -Real.log (4000000000 / 9228825611) := by
    rw [show ((9228825611 / 4000000000) : ℝ) = ((4000000000 / 9228825611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13556_neg : (842433539 / 1000000000) ≤ -Real.log (500000000000 / 1161005406573) ∧
    -Real.log (500000000000 / 1161005406573) ≤ (842433541 / 1000000000) := by
  have h := checkLog_sound (w := (161005406573 / 2161005406573)) (n := 12)
    (lo := (149286359 / 1000000000)) (hi := (3732159 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161005406573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161005406573 / 1000000000000) = 1/(500000000000 / 1161005406573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13556 : Bounds (842433539 / 1000000000) (842433541 / 1000000000) (Real.log (1161005406573 / 500000000000)) := by
  have h := reflection_log_13556_neg
  have he : Real.log (1161005406573 / 500000000000) = -Real.log (500000000000 / 1161005406573) := by
    rw [show ((1161005406573 / 500000000000) : ℝ) = ((500000000000 / 1161005406573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13557_neg : (1786519281 / 1000000000) ≤ -Real.log (500000000000 / 2984320557491) ∧
    -Real.log (500000000000 / 2984320557491) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (984320557491 / 4984320557491)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2984320557491 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2984320557491 / 2000000000000) = 1/(500000000000 / 2984320557491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13557 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (2984320557491 / 500000000000)) := by
  have h := reflection_log_13557_neg
  have he : Real.log (2984320557491 / 500000000000) = -Real.log (500000000000 / 2984320557491) := by
    rw [show ((2984320557491 / 500000000000) : ℝ) = ((500000000000 / 2984320557491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13558_neg : (22484713 / 12500000) ≤ -Real.log (125000000000 / 755281690141) ∧
    -Real.log (125000000000 / 755281690141) ≤ (1798777043 / 1000000000) := by
  have h := checkLog_sound (w := (255281690141 / 1255281690141)) (n := 12)
    (lo := (10312067 / 25000000)) (hi := (412482681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755281690141 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(755281690141 / 500000000000) = 1/(125000000000 / 755281690141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13558 : Bounds (22484713 / 12500000) (1798777043 / 1000000000) (Real.log (755281690141 / 125000000000)) := by
  have h := reflection_log_13558_neg
  have he : Real.log (755281690141 / 125000000000) = -Real.log (125000000000 / 755281690141) := by
    rw [show ((755281690141 / 125000000000) : ℝ) = ((125000000000 / 755281690141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13559_neg : (270871363 / 500000000) ≤ -Real.log (1000 / 1719) ∧
    -Real.log (1000 / 1719) ≤ (541742727 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2719)) (n := 12)
    (lo := (270871363 / 500000000)) (hi := (541742727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1000) = 1/(1000 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13559 : Bounds (270871363 / 500000000) (541742727 / 1000000000) (Real.log (1719 / 1000)) := by
  have h := reflection_log_13559_neg
  have he : Real.log (1719 / 1000) = -Real.log (1000 / 1719) := by
    rw [show ((1719 / 1000) : ℝ) = ((1000 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13560_neg : (1269400609 / 1000000000) ≤ -Real.log (281 / 1000) ∧
    -Real.log (281 / 1000) ≤ (1269400611 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 781)) (n := 12)
    (lo := (576253429 / 1000000000)) (hi := (57625343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 281) = 1/(281 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13560 : Bounds (-1269400611 / 1000000000) (-1269400609 / 1000000000) (Real.log (281 / 1000)) := by
  have h := reflection_log_13560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13561_neg : (718741 / 1000000000) ≤ -Real.log (1000000 / 1000719) ∧
    -Real.log (1000000 / 1000719) ≤ (359371 / 500000000) := by
  have h := checkLog_sound (w := (719 / 2000719)) (n := 12)
    (lo := (718741 / 1000000000)) (hi := (359371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000719 / 1000000) = 1/(1000000 / 1000719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13561 : Bounds (718741 / 1000000000) (359371 / 500000000) (Real.log (1000719 / 1000000)) := by
  have h := reflection_log_13561_neg
  have he : Real.log (1000719 / 1000000) = -Real.log (1000000 / 1000719) := by
    rw [show ((1000719 / 1000000) : ℝ) = ((1000000 / 1000719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13562_neg : (359629 / 500000000) ≤ -Real.log (999281 / 1000000) ∧
    -Real.log (999281 / 1000000) ≤ (719259 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 1999281)) (n := 12)
    (lo := (359629 / 500000000)) (hi := (719259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999281) = 1/(999281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13562 : Bounds (-719259 / 1000000000) (-359629 / 500000000) (Real.log (999281 / 1000000)) := by
  have h := reflection_log_13562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13563_neg : (334562557 / 1000000000) ≤ -Real.log (1000000 / 1397329) ∧
    -Real.log (1000000 / 1397329) ≤ (167281279 / 500000000) := by
  have h := checkLog_sound (w := (397329 / 2397329)) (n := 12)
    (lo := (334562557 / 1000000000)) (hi := (167281279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397329 / 1000000) = 1/(1000000 / 1397329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13563 : Bounds (334562557 / 1000000000) (167281279 / 500000000) (Real.log (1397329 / 1000000)) := by
  have h := reflection_log_13563_neg
  have he : Real.log (1397329 / 1000000) = -Real.log (1000000 / 1397329) := by
    rw [show ((1397329 / 1000000) : ℝ) = ((1000000 / 1397329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13564_neg : (126595959 / 250000000) ≤ -Real.log (602671 / 1000000) ∧
    -Real.log (602671 / 1000000) ≤ (506383837 / 1000000000) := by
  have h := checkLog_sound (w := (397329 / 1602671)) (n := 12)
    (lo := (126595959 / 250000000)) (hi := (506383837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602671) = 1/(602671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13564 : Bounds (-506383837 / 1000000000) (-126595959 / 250000000) (Real.log (602671 / 1000000)) := by
  have h := reflection_log_13564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13565_neg : (336495093 / 1000000000) ≤ -Real.log (31250 / 43751) ∧
    -Real.log (31250 / 43751) ≤ (168247547 / 500000000) := by
  have h := checkLog_sound (w := (12501 / 75001)) (n := 12)
    (lo := (336495093 / 1000000000)) (hi := (168247547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43751 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43751 / 31250) = 1/(31250 / 43751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13565 : Bounds (336495093 / 1000000000) (168247547 / 500000000) (Real.log (43751 / 31250)) := by
  have h := reflection_log_13565_neg
  have he : Real.log (43751 / 31250) = -Real.log (31250 / 43751) := by
    rw [show ((43751 / 31250) : ℝ) = ((31250 / 43751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13566_neg : (255439479 / 500000000) ≤ -Real.log (18749 / 31250) ∧
    -Real.log (18749 / 31250) ≤ (510878959 / 1000000000) := by
  have h := checkLog_sound (w := (12501 / 49999)) (n := 12)
    (lo := (255439479 / 500000000)) (hi := (510878959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 18749) = 1/(18749 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13566 : Bounds (-510878959 / 1000000000) (-255439479 / 500000000) (Real.log (18749 / 31250)) := by
  have h := reflection_log_13566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13567_neg : (34876773 / 200000000) ≤ -Real.log (820287499 / 976562500) ∧
    -Real.log (820287499 / 976562500) ≤ (87191933 / 500000000) := by
  have h := checkLog_sound (w := (156275001 / 1796849999)) (n := 12)
    (lo := (34876773 / 200000000)) (hi := (87191933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 820287499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 820287499) = 1/(820287499 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13567 : Bounds (-87191933 / 500000000) (-34876773 / 200000000) (Real.log (820287499 / 976562500)) := by
  have h := reflection_log_13567_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
