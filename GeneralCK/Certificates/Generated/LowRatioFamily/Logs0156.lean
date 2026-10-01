import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9984_neg : (81251227 / 250000000) ≤ -Real.log (250000000000 / 346009359731) ∧
    -Real.log (250000000000 / 346009359731) ≤ (325004909 / 1000000000) := by
  have h := checkLog_sound (w := (96009359731 / 596009359731)) (n := 12)
    (lo := (81251227 / 250000000)) (hi := (325004909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346009359731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346009359731 / 250000000000) = 1/(250000000000 / 346009359731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9984 : Bounds (81251227 / 250000000) (325004909 / 1000000000) (Real.log (346009359731 / 250000000000)) := by
  have h := reflection_log_9984_neg
  have he : Real.log (346009359731 / 250000000000) = -Real.log (250000000000 / 346009359731) := by
    rw [show ((346009359731 / 250000000000) : ℝ) = ((250000000000 / 346009359731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9985_neg : (326086553 / 500000000) ≤ -Real.log (250000000000 / 479927007299) ∧
    -Real.log (250000000000 / 479927007299) ≤ (652173107 / 1000000000) := by
  have h := checkLog_sound (w := (229927007299 / 729927007299)) (n := 12)
    (lo := (326086553 / 500000000)) (hi := (652173107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479927007299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479927007299 / 250000000000) = 1/(250000000000 / 479927007299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9985 : Bounds (326086553 / 500000000) (652173107 / 1000000000) (Real.log (479927007299 / 250000000000)) := by
  have h := reflection_log_9985_neg
  have he : Real.log (479927007299 / 250000000000) = -Real.log (250000000000 / 479927007299) := by
    rw [show ((479927007299 / 250000000000) : ℝ) = ((250000000000 / 479927007299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9986_neg : (327197097 / 500000000) ≤ -Real.log (250000000000 / 480994152047) ∧
    -Real.log (250000000000 / 480994152047) ≤ (130878839 / 200000000) := by
  have h := checkLog_sound (w := (230994152047 / 730994152047)) (n := 12)
    (lo := (327197097 / 500000000)) (hi := (130878839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((480994152047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(480994152047 / 250000000000) = 1/(250000000000 / 480994152047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9986 : Bounds (327197097 / 500000000) (130878839 / 200000000) (Real.log (480994152047 / 250000000000)) := by
  have h := reflection_log_9986_neg
  have he : Real.log (480994152047 / 250000000000) = -Real.log (250000000000 / 480994152047) := by
    rw [show ((480994152047 / 250000000000) : ℝ) = ((250000000000 / 480994152047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9987_neg : (137678211 / 500000000) ≤ -Real.log (1000 / 1317) ∧
    -Real.log (1000 / 1317) ≤ (275356423 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 2317)) (n := 12)
    (lo := (137678211 / 500000000)) (hi := (275356423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1000) = 1/(1000 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9987 : Bounds (137678211 / 500000000) (275356423 / 1000000000) (Real.log (1317 / 1000)) := by
  have h := reflection_log_9987_neg
  have he : Real.log (1317 / 1000) = -Real.log (1000 / 1317) := by
    rw [show ((1317 / 1000) : ℝ) = ((1000 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9988_neg : (381260419 / 1000000000) ≤ -Real.log (683 / 1000) ∧
    -Real.log (683 / 1000) ≤ (19063021 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1683)) (n := 12)
    (lo := (381260419 / 1000000000)) (hi := (19063021 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 683) = 1/(683 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9988 : Bounds (-19063021 / 50000000) (-381260419 / 1000000000) (Real.log (683 / 1000)) := by
  have h := reflection_log_9988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9989_neg : (316949 / 1000000000) ≤ -Real.log (1000000 / 1000317) ∧
    -Real.log (1000000 / 1000317) ≤ (6339 / 20000000) := by
  have h := checkLog_sound (w := (317 / 2000317)) (n := 12)
    (lo := (316949 / 1000000000)) (hi := (6339 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000317 / 1000000) = 1/(1000000 / 1000317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9989 : Bounds (316949 / 1000000000) (6339 / 20000000) (Real.log (1000317 / 1000000)) := by
  have h := reflection_log_9989_neg
  have he : Real.log (1000317 / 1000000) = -Real.log (1000000 / 1000317) := by
    rw [show ((1000317 / 1000000) : ℝ) = ((1000000 / 1000317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9990_neg : (6341 / 20000000) ≤ -Real.log (999683 / 1000000) ∧
    -Real.log (999683 / 1000000) ≤ (317051 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1999683)) (n := 12)
    (lo := (6341 / 20000000)) (hi := (317051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999683) = 1/(999683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9990 : Bounds (-317051 / 1000000000) (-6341 / 20000000) (Real.log (999683 / 1000000)) := by
  have h := reflection_log_9990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9991_neg : (74544373 / 500000000) ≤ -Real.log (125000 / 145097) ∧
    -Real.log (125000 / 145097) ≤ (149088747 / 1000000000) := by
  have h := checkLog_sound (w := (20097 / 270097)) (n := 12)
    (lo := (74544373 / 500000000)) (hi := (149088747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145097 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145097 / 125000) = 1/(125000 / 145097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9991 : Bounds (74544373 / 500000000) (149088747 / 1000000000) (Real.log (145097 / 125000)) := by
  have h := reflection_log_9991_neg
  have he : Real.log (145097 / 125000) = -Real.log (125000 / 145097) := by
    rw [show ((145097 / 125000) : ℝ) = ((125000 / 145097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9992_neg : (175277623 / 1000000000) ≤ -Real.log (104903 / 125000) ∧
    -Real.log (104903 / 125000) ≤ (21909703 / 125000000) := by
  have h := checkLog_sound (w := (20097 / 229903)) (n := 12)
    (lo := (175277623 / 1000000000)) (hi := (21909703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104903) = 1/(104903 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9992 : Bounds (-21909703 / 125000000) (-175277623 / 1000000000) (Real.log (104903 / 125000)) := by
  have h := reflection_log_9992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9993_neg : (149812999 / 1000000000) ≤ -Real.log (1000000 / 1161617) ∧
    -Real.log (1000000 / 1161617) ≤ (149813 / 1000000) := by
  have h := checkLog_sound (w := (161617 / 2161617)) (n := 12)
    (lo := (149812999 / 1000000000)) (hi := (149813 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161617 / 1000000) = 1/(1000000 / 1161617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9993 : Bounds (149812999 / 1000000000) (149813 / 1000000) (Real.log (1161617 / 1000000)) := by
  have h := reflection_log_9993_neg
  have he : Real.log (1161617 / 1000000) = -Real.log (1000000 / 1161617) := by
    rw [show ((1161617 / 1000000) : ℝ) = ((1000000 / 1161617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9994_neg : (88140121 / 500000000) ≤ -Real.log (838383 / 1000000) ∧
    -Real.log (838383 / 1000000) ≤ (176280243 / 1000000000) := by
  have h := checkLog_sound (w := (161617 / 1838383)) (n := 12)
    (lo := (88140121 / 500000000)) (hi := (176280243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838383) = 1/(838383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9994 : Bounds (-176280243 / 1000000000) (-88140121 / 500000000) (Real.log (838383 / 1000000)) := by
  have h := reflection_log_9994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9995_neg : (13233621 / 500000000) ≤ -Real.log (973879945311 / 1000000000000) ∧
    -Real.log (973879945311 / 1000000000000) ≤ (26467243 / 1000000000) := by
  have h := checkLog_sound (w := (26120054689 / 1973879945311)) (n := 12)
    (lo := (13233621 / 500000000)) (hi := (26467243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973879945311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973879945311) = 1/(973879945311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9995 : Bounds (-26467243 / 1000000000) (-13233621 / 500000000) (Real.log (973879945311 / 1000000000000)) := by
  have h := reflection_log_9995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9996_neg : (6547219 / 250000000) ≤ -Real.log (15221110591 / 15625000000) ∧
    -Real.log (15221110591 / 15625000000) ≤ (26188877 / 1000000000) := by
  have h := checkLog_sound (w := (403889409 / 30846110591)) (n := 12)
    (lo := (6547219 / 250000000)) (hi := (26188877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15221110591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15221110591) = 1/(15221110591 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9996 : Bounds (-26188877 / 1000000000) (-6547219 / 250000000) (Real.log (15221110591 / 15625000000)) := by
  have h := reflection_log_9996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9997_neg : (32436637 / 100000000) ≤ -Real.log (500000000000 / 691576980639) ∧
    -Real.log (500000000000 / 691576980639) ≤ (324366371 / 1000000000) := by
  have h := checkLog_sound (w := (191576980639 / 1191576980639)) (n := 12)
    (lo := (32436637 / 100000000)) (hi := (324366371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691576980639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691576980639 / 500000000000) = 1/(500000000000 / 691576980639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9997 : Bounds (32436637 / 100000000) (324366371 / 1000000000) (Real.log (691576980639 / 500000000000)) := by
  have h := reflection_log_9997_neg
  have he : Real.log (691576980639 / 500000000000) = -Real.log (500000000000 / 691576980639) := by
    rw [show ((691576980639 / 500000000000) : ℝ) = ((500000000000 / 691576980639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9998_neg : (163046621 / 500000000) ≤ -Real.log (50000000000 / 69277227711) ∧
    -Real.log (50000000000 / 69277227711) ≤ (326093243 / 1000000000) := by
  have h := checkLog_sound (w := (19277227711 / 119277227711)) (n := 12)
    (lo := (163046621 / 500000000)) (hi := (326093243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69277227711 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69277227711 / 50000000000) = 1/(50000000000 / 69277227711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9998 : Bounds (163046621 / 500000000) (326093243 / 1000000000) (Real.log (69277227711 / 50000000000)) := by
  have h := reflection_log_9998_neg
  have he : Real.log (69277227711 / 50000000000) = -Real.log (50000000000 / 69277227711) := by
    rw [show ((69277227711 / 50000000000) : ℝ) = ((50000000000 / 69277227711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9999_neg : (327197097 / 500000000) ≤ -Real.log (500000000000 / 961988304093) ∧
    -Real.log (500000000000 / 961988304093) ≤ (130878839 / 200000000) := by
  have h := checkLog_sound (w := (461988304093 / 1461988304093)) (n := 12)
    (lo := (327197097 / 500000000)) (hi := (130878839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961988304093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961988304093 / 500000000000) = 1/(500000000000 / 961988304093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9999 : Bounds (327197097 / 500000000) (130878839 / 200000000) (Real.log (961988304093 / 500000000000)) := by
  have h := reflection_log_9999_neg
  have he : Real.log (961988304093 / 500000000000) = -Real.log (500000000000 / 961988304093) := by
    rw [show ((961988304093 / 500000000000) : ℝ) = ((500000000000 / 961988304093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10000_neg : (328308421 / 500000000) ≤ -Real.log (500000000000 / 964128843339) ∧
    -Real.log (500000000000 / 964128843339) ≤ (656616843 / 1000000000) := by
  have h := checkLog_sound (w := (464128843339 / 1464128843339)) (n := 12)
    (lo := (328308421 / 500000000)) (hi := (656616843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964128843339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964128843339 / 500000000000) = 1/(500000000000 / 964128843339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10000 : Bounds (328308421 / 500000000) (656616843 / 1000000000) (Real.log (964128843339 / 500000000000)) := by
  have h := reflection_log_10000_neg
  have he : Real.log (964128843339 / 500000000000) = -Real.log (500000000000 / 964128843339) := by
    rw [show ((964128843339 / 500000000000) : ℝ) = ((500000000000 / 964128843339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10001_neg : (69028859 / 250000000) ≤ -Real.log (500 / 659) ∧
    -Real.log (500 / 659) ≤ (276115437 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1159)) (n := 12)
    (lo := (69028859 / 250000000)) (hi := (276115437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 500) = 1/(500 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10001 : Bounds (69028859 / 250000000) (276115437 / 1000000000) (Real.log (659 / 500)) := by
  have h := reflection_log_10001_neg
  have he : Real.log (659 / 500) = -Real.log (500 / 659) := by
    rw [show ((659 / 500) : ℝ) = ((500 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10002_neg : (382725621 / 1000000000) ≤ -Real.log (341 / 500) ∧
    -Real.log (341 / 500) ≤ (191362811 / 500000000) := by
  have h := checkLog_sound (w := (159 / 841)) (n := 12)
    (lo := (382725621 / 1000000000)) (hi := (191362811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 341) = 1/(341 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10002 : Bounds (-191362811 / 500000000) (-382725621 / 1000000000) (Real.log (341 / 500)) := by
  have h := reflection_log_10002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10003_neg : (317949 / 1000000000) ≤ -Real.log (500000 / 500159) ∧
    -Real.log (500000 / 500159) ≤ (6359 / 20000000) := by
  have h := checkLog_sound (w := (159 / 1000159)) (n := 12)
    (lo := (317949 / 1000000000)) (hi := (6359 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500159 / 500000) = 1/(500000 / 500159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10003 : Bounds (317949 / 1000000000) (6359 / 20000000) (Real.log (500159 / 500000)) := by
  have h := reflection_log_10003_neg
  have he : Real.log (500159 / 500000) = -Real.log (500000 / 500159) := by
    rw [show ((500159 / 500000) : ℝ) = ((500000 / 500159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10004_neg : (6361 / 20000000) ≤ -Real.log (499841 / 500000) ∧
    -Real.log (499841 / 500000) ≤ (318051 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 999841)) (n := 12)
    (lo := (6361 / 20000000)) (hi := (318051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499841) = 1/(499841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10004 : Bounds (-318051 / 1000000000) (-6361 / 20000000) (Real.log (499841 / 500000)) := by
  have h := reflection_log_10004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10005_neg : (149543511 / 1000000000) ≤ -Real.log (125000 / 145163) ∧
    -Real.log (125000 / 145163) ≤ (18692939 / 125000000) := by
  have h := checkLog_sound (w := (20163 / 270163)) (n := 12)
    (lo := (149543511 / 1000000000)) (hi := (18692939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145163 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145163 / 125000) = 1/(125000 / 145163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10005 : Bounds (149543511 / 1000000000) (18692939 / 125000000) (Real.log (145163 / 125000)) := by
  have h := reflection_log_10005_neg
  have he : Real.log (145163 / 125000) = -Real.log (125000 / 145163) := by
    rw [show ((145163 / 125000) : ℝ) = ((125000 / 145163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10006_neg : (87953487 / 500000000) ≤ -Real.log (104837 / 125000) ∧
    -Real.log (104837 / 125000) ≤ (7036279 / 40000000) := by
  have h := checkLog_sound (w := (20163 / 229837)) (n := 12)
    (lo := (87953487 / 500000000)) (hi := (7036279 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104837) = 1/(104837 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10006 : Bounds (-7036279 / 40000000) (-87953487 / 500000000) (Real.log (104837 / 125000)) := by
  have h := reflection_log_10006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10007_neg : (30053659 / 200000000) ≤ -Real.log (500000 / 581073) ∧
    -Real.log (500000 / 581073) ≤ (18783537 / 125000000) := by
  have h := checkLog_sound (w := (81073 / 1081073)) (n := 12)
    (lo := (30053659 / 200000000)) (hi := (18783537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581073 / 500000) = 1/(500000 / 581073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10007 : Bounds (30053659 / 200000000) (18783537 / 125000000) (Real.log (581073 / 500000)) := by
  have h := reflection_log_10007_neg
  have he : Real.log (581073 / 500000) = -Real.log (500000 / 581073) := by
    rw [show ((581073 / 500000) : ℝ) = ((500000 / 581073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10008_neg : (88455709 / 500000000) ≤ -Real.log (418927 / 500000) ∧
    -Real.log (418927 / 500000) ≤ (176911419 / 1000000000) := by
  have h := checkLog_sound (w := (81073 / 918927)) (n := 12)
    (lo := (88455709 / 500000000)) (hi := (176911419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418927) = 1/(418927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10008 : Bounds (-176911419 / 1000000000) (-88455709 / 500000000) (Real.log (418927 / 500000)) := by
  have h := reflection_log_10008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10009_neg : (13321561 / 500000000) ≤ -Real.log (243427168671 / 250000000000) ∧
    -Real.log (243427168671 / 250000000000) ≤ (26643123 / 1000000000) := by
  have h := checkLog_sound (w := (6572831329 / 493427168671)) (n := 12)
    (lo := (13321561 / 500000000)) (hi := (26643123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243427168671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243427168671) = 1/(243427168671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10009 : Bounds (-26643123 / 1000000000) (-13321561 / 500000000) (Real.log (243427168671 / 250000000000)) := by
  have h := reflection_log_10009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10010_neg : (13181731 / 500000000) ≤ -Real.log (15218453431 / 15625000000) ∧
    -Real.log (15218453431 / 15625000000) ≤ (26363463 / 1000000000) := by
  have h := checkLog_sound (w := (406546569 / 30843453431)) (n := 12)
    (lo := (13181731 / 500000000)) (hi := (26363463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15218453431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15218453431) = 1/(15218453431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10010 : Bounds (-26363463 / 1000000000) (-13181731 / 500000000) (Real.log (15218453431 / 15625000000)) := by
  have h := reflection_log_10010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10011_neg : (65090097 / 200000000) ≤ -Real.log (500000000000 / 692327136411) ∧
    -Real.log (500000000000 / 692327136411) ≤ (162725243 / 500000000) := by
  have h := checkLog_sound (w := (192327136411 / 1192327136411)) (n := 12)
    (lo := (65090097 / 200000000)) (hi := (162725243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692327136411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692327136411 / 500000000000) = 1/(500000000000 / 692327136411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10011 : Bounds (65090097 / 200000000) (162725243 / 500000000) (Real.log (692327136411 / 500000000000)) := by
  have h := reflection_log_10011_neg
  have he : Real.log (692327136411 / 500000000000) = -Real.log (500000000000 / 692327136411) := by
    rw [show ((692327136411 / 500000000000) : ℝ) = ((500000000000 / 692327136411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10012_neg : (327179713 / 1000000000) ≤ -Real.log (62500000000 / 86690670451) ∧
    -Real.log (62500000000 / 86690670451) ≤ (163589857 / 500000000) := by
  have h := checkLog_sound (w := (24190670451 / 149190670451)) (n := 12)
    (lo := (327179713 / 1000000000)) (hi := (163589857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86690670451 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86690670451 / 62500000000) = 1/(62500000000 / 86690670451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10012 : Bounds (327179713 / 1000000000) (163589857 / 500000000) (Real.log (86690670451 / 62500000000)) := by
  have h := reflection_log_10012_neg
  have he : Real.log (86690670451 / 62500000000) = -Real.log (62500000000 / 86690670451) := by
    rw [show ((86690670451 / 62500000000) : ℝ) = ((62500000000 / 86690670451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10013_neg : (328308421 / 500000000) ≤ -Real.log (250000000000 / 482064421669) ∧
    -Real.log (250000000000 / 482064421669) ≤ (656616843 / 1000000000) := by
  have h := checkLog_sound (w := (232064421669 / 732064421669)) (n := 12)
    (lo := (328308421 / 500000000)) (hi := (656616843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482064421669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482064421669 / 250000000000) = 1/(250000000000 / 482064421669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10013 : Bounds (328308421 / 500000000) (656616843 / 1000000000) (Real.log (482064421669 / 250000000000)) := by
  have h := reflection_log_10013_neg
  have he : Real.log (482064421669 / 250000000000) = -Real.log (250000000000 / 482064421669) := by
    rw [show ((482064421669 / 250000000000) : ℝ) = ((250000000000 / 482064421669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10014_neg : (658841057 / 1000000000) ≤ -Real.log (20000000000 / 38651026393) ∧
    -Real.log (20000000000 / 38651026393) ≤ (329420529 / 500000000) := by
  have h := checkLog_sound (w := (18651026393 / 58651026393)) (n := 12)
    (lo := (658841057 / 1000000000)) (hi := (329420529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38651026393 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38651026393 / 20000000000) = 1/(20000000000 / 38651026393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10014 : Bounds (658841057 / 1000000000) (329420529 / 500000000) (Real.log (38651026393 / 20000000000)) := by
  have h := reflection_log_10014_neg
  have he : Real.log (38651026393 / 20000000000) = -Real.log (20000000000 / 38651026393) := by
    rw [show ((38651026393 / 20000000000) : ℝ) = ((20000000000 / 38651026393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10015_neg : (276873873 / 1000000000) ≤ -Real.log (1000 / 1319) ∧
    -Real.log (1000 / 1319) ≤ (138436937 / 500000000) := by
  have h := checkLog_sound (w := (319 / 2319)) (n := 12)
    (lo := (276873873 / 1000000000)) (hi := (138436937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1000) = 1/(1000 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10015 : Bounds (276873873 / 1000000000) (138436937 / 500000000) (Real.log (1319 / 1000)) := by
  have h := reflection_log_10015_neg
  have he : Real.log (1319 / 1000) = -Real.log (1000 / 1319) := by
    rw [show ((1319 / 1000) : ℝ) = ((1000 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10016_neg : (96048243 / 250000000) ≤ -Real.log (681 / 1000) ∧
    -Real.log (681 / 1000) ≤ (384192973 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1681)) (n := 12)
    (lo := (96048243 / 250000000)) (hi := (384192973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 681) = 1/(681 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10016 : Bounds (-384192973 / 1000000000) (-96048243 / 250000000) (Real.log (681 / 1000)) := by
  have h := reflection_log_10016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10017_neg : (318949 / 1000000000) ≤ -Real.log (1000000 / 1000319) ∧
    -Real.log (1000000 / 1000319) ≤ (6379 / 20000000) := by
  have h := checkLog_sound (w := (319 / 2000319)) (n := 12)
    (lo := (318949 / 1000000000)) (hi := (6379 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000319 / 1000000) = 1/(1000000 / 1000319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10017 : Bounds (318949 / 1000000000) (6379 / 20000000) (Real.log (1000319 / 1000000)) := by
  have h := reflection_log_10017_neg
  have he : Real.log (1000319 / 1000000) = -Real.log (1000000 / 1000319) := by
    rw [show ((1000319 / 1000000) : ℝ) = ((1000000 / 1000319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10018_neg : (6381 / 20000000) ≤ -Real.log (999681 / 1000000) ∧
    -Real.log (999681 / 1000000) ≤ (319051 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1999681)) (n := 12)
    (lo := (6381 / 20000000)) (hi := (319051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999681) = 1/(999681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10018 : Bounds (-319051 / 1000000000) (-6381 / 20000000) (Real.log (999681 / 1000000)) := by
  have h := reflection_log_10018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10019_neg : (14999893 / 100000000) ≤ -Real.log (1000000 / 1161833) ∧
    -Real.log (1000000 / 1161833) ≤ (149998931 / 1000000000) := by
  have h := checkLog_sound (w := (161833 / 2161833)) (n := 12)
    (lo := (14999893 / 100000000)) (hi := (149998931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161833 / 1000000) = 1/(1000000 / 1161833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10019 : Bounds (14999893 / 100000000) (149998931 / 1000000000) (Real.log (1161833 / 1000000)) := by
  have h := reflection_log_10019_neg
  have he : Real.log (1161833 / 1000000) = -Real.log (1000000 / 1161833) := by
    rw [show ((1161833 / 1000000) : ℝ) = ((1000000 / 1161833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10020_neg : (88268957 / 500000000) ≤ -Real.log (838167 / 1000000) ∧
    -Real.log (838167 / 1000000) ≤ (35307583 / 200000000) := by
  have h := checkLog_sound (w := (161833 / 1838167)) (n := 12)
    (lo := (88268957 / 500000000)) (hi := (35307583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838167) = 1/(838167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10020 : Bounds (-35307583 / 200000000) (-88268957 / 500000000) (Real.log (838167 / 1000000)) := by
  have h := reflection_log_10020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10021_neg : (18840423 / 125000000) ≤ -Real.log (40000 / 46507) ∧
    -Real.log (40000 / 46507) ≤ (30144677 / 200000000) := by
  have h := checkLog_sound (w := (6507 / 86507)) (n := 12)
    (lo := (18840423 / 125000000)) (hi := (30144677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46507 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46507 / 40000) = 1/(40000 / 46507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10021 : Bounds (18840423 / 125000000) (30144677 / 200000000) (Real.log (46507 / 40000)) := by
  have h := reflection_log_10021_neg
  have he : Real.log (46507 / 40000) = -Real.log (40000 / 46507) := by
    rw [show ((46507 / 40000) : ℝ) = ((40000 / 46507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10022_neg : (11096437 / 62500000) ≤ -Real.log (33493 / 40000) ∧
    -Real.log (33493 / 40000) ≤ (177542993 / 1000000000) := by
  have h := checkLog_sound (w := (6507 / 73493)) (n := 12)
    (lo := (11096437 / 62500000)) (hi := (177542993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33493) = 1/(33493 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10022 : Bounds (-177542993 / 1000000000) (-11096437 / 62500000) (Real.log (33493 / 40000)) := by
  have h := reflection_log_10022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10023_neg : (26819607 / 1000000000) ≤ -Real.log (1557658951 / 1600000000) ∧
    -Real.log (1557658951 / 1600000000) ≤ (3352451 / 125000000) := by
  have h := checkLog_sound (w := (42341049 / 3157658951)) (n := 12)
    (lo := (26819607 / 1000000000)) (hi := (3352451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1557658951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1557658951) = 1/(1557658951 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10023 : Bounds (-3352451 / 125000000) (-26819607 / 1000000000) (Real.log (1557658951 / 1600000000)) := by
  have h := reflection_log_10023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10024_neg : (26538983 / 1000000000) ≤ -Real.log (973810080111 / 1000000000000) ∧
    -Real.log (973810080111 / 1000000000000) ≤ (3317373 / 125000000) := by
  have h := checkLog_sound (w := (26189919889 / 1973810080111)) (n := 12)
    (lo := (26538983 / 1000000000)) (hi := (3317373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973810080111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973810080111) = 1/(973810080111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10024 : Bounds (-3317373 / 125000000) (-26538983 / 1000000000) (Real.log (973810080111 / 1000000000000)) := by
  have h := reflection_log_10024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10025_neg : (81634211 / 250000000) ≤ -Real.log (100000000000 / 138615932147) ∧
    -Real.log (100000000000 / 138615932147) ≤ (65307369 / 200000000) := by
  have h := checkLog_sound (w := (38615932147 / 238615932147)) (n := 12)
    (lo := (81634211 / 250000000)) (hi := (65307369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138615932147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138615932147 / 100000000000) = 1/(100000000000 / 138615932147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10025 : Bounds (81634211 / 250000000) (65307369 / 200000000) (Real.log (138615932147 / 100000000000)) := by
  have h := reflection_log_10025_neg
  have he : Real.log (138615932147 / 100000000000) = -Real.log (100000000000 / 138615932147) := by
    rw [show ((138615932147 / 100000000000) : ℝ) = ((100000000000 / 138615932147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10026_neg : (328266377 / 1000000000) ≤ -Real.log (500000000000 / 694279401667) ∧
    -Real.log (500000000000 / 694279401667) ≤ (164133189 / 500000000) := by
  have h := checkLog_sound (w := (194279401667 / 1194279401667)) (n := 12)
    (lo := (328266377 / 1000000000)) (hi := (164133189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694279401667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694279401667 / 500000000000) = 1/(500000000000 / 694279401667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10026 : Bounds (328266377 / 1000000000) (164133189 / 500000000) (Real.log (694279401667 / 500000000000)) := by
  have h := reflection_log_10026_neg
  have he : Real.log (694279401667 / 500000000000) = -Real.log (500000000000 / 694279401667) := by
    rw [show ((694279401667 / 500000000000) : ℝ) = ((500000000000 / 694279401667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10027_neg : (658841057 / 1000000000) ≤ -Real.log (31250000000 / 60392228739) ∧
    -Real.log (31250000000 / 60392228739) ≤ (329420529 / 500000000) := by
  have h := checkLog_sound (w := (29142228739 / 91642228739)) (n := 12)
    (lo := (658841057 / 1000000000)) (hi := (329420529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60392228739 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60392228739 / 31250000000) = 1/(31250000000 / 60392228739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10027 : Bounds (658841057 / 1000000000) (329420529 / 500000000) (Real.log (60392228739 / 31250000000)) := by
  have h := reflection_log_10027_neg
  have he : Real.log (60392228739 / 31250000000) = -Real.log (31250000000 / 60392228739) := by
    rw [show ((60392228739 / 31250000000) : ℝ) = ((31250000000 / 60392228739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10028_neg : (330533423 / 500000000) ≤ -Real.log (100000000000 / 193685756241) ∧
    -Real.log (100000000000 / 193685756241) ≤ (661066847 / 1000000000) := by
  have h := checkLog_sound (w := (93685756241 / 293685756241)) (n := 12)
    (lo := (330533423 / 500000000)) (hi := (661066847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193685756241 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193685756241 / 100000000000) = 1/(100000000000 / 193685756241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10028 : Bounds (330533423 / 500000000) (661066847 / 1000000000) (Real.log (193685756241 / 100000000000)) := by
  have h := reflection_log_10028_neg
  have he : Real.log (193685756241 / 100000000000) = -Real.log (100000000000 / 193685756241) := by
    rw [show ((193685756241 / 100000000000) : ℝ) = ((100000000000 / 193685756241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10029_neg : (34703967 / 125000000) ≤ -Real.log (25 / 33) ∧
    -Real.log (25 / 33) ≤ (277631737 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 29)) (n := 12)
    (lo := (34703967 / 125000000)) (hi := (277631737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33 / 25) = 1/(25 / 33) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10029 : Bounds (34703967 / 125000000) (277631737 / 1000000000) (Real.log (33 / 25)) := by
  have h := reflection_log_10029_neg
  have he : Real.log (33 / 25) = -Real.log (25 / 33) := by
    rw [show ((33 / 25) : ℝ) = ((25 / 33) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10030_neg : (4820781 / 12500000) ≤ -Real.log (17 / 25) ∧
    -Real.log (17 / 25) ≤ (385662481 / 1000000000) := by
  have h := checkLog_sound (w := (4 / 21)) (n := 12)
    (lo := (4820781 / 12500000)) (hi := (385662481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 17) = 1/(17 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10030 : Bounds (-385662481 / 1000000000) (-4820781 / 12500000) (Real.log (17 / 25)) := by
  have h := reflection_log_10030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10031_neg : (79987 / 250000000) ≤ -Real.log (3125 / 3126) ∧
    -Real.log (3125 / 3126) ≤ (319949 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6251)) (n := 12)
    (lo := (79987 / 250000000)) (hi := (319949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3126 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3126 / 3125) = 1/(3125 / 3126) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10031 : Bounds (79987 / 250000000) (319949 / 1000000000) (Real.log (3126 / 3125)) := by
  have h := reflection_log_10031_neg
  have he : Real.log (3126 / 3125) = -Real.log (3125 / 3126) := by
    rw [show ((3126 / 3125) : ℝ) = ((3125 / 3126) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10032_neg : (320051 / 1000000000) ≤ -Real.log (3124 / 3125) ∧
    -Real.log (3124 / 3125) ≤ (80013 / 250000000) := by
  have h := checkLog_sound (w := (1 / 6249)) (n := 12)
    (lo := (320051 / 1000000000)) (hi := (80013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3124) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 3124) = 1/(3124 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10032 : Bounds (-80013 / 250000000) (-320051 / 1000000000) (Real.log (3124 / 3125)) := by
  have h := reflection_log_10032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10033_neg : (150453281 / 1000000000) ≤ -Real.log (1000000 / 1162361) ∧
    -Real.log (1000000 / 1162361) ≤ (75226641 / 500000000) := by
  have h := checkLog_sound (w := (162361 / 2162361)) (n := 12)
    (lo := (150453281 / 1000000000)) (hi := (75226641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162361 / 1000000) = 1/(1000000 / 1162361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10033 : Bounds (150453281 / 1000000000) (75226641 / 500000000) (Real.log (1162361 / 1000000)) := by
  have h := reflection_log_10033_neg
  have he : Real.log (1162361 / 1000000) = -Real.log (1000000 / 1162361) := by
    rw [show ((1162361 / 1000000) : ℝ) = ((1000000 / 1162361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10034_neg : (88584029 / 500000000) ≤ -Real.log (837639 / 1000000) ∧
    -Real.log (837639 / 1000000) ≤ (177168059 / 1000000000) := by
  have h := checkLog_sound (w := (162361 / 1837639)) (n := 12)
    (lo := (88584029 / 500000000)) (hi := (177168059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837639) = 1/(837639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10034 : Bounds (-177168059 / 1000000000) (-88584029 / 500000000) (Real.log (837639 / 1000000)) := by
  have h := reflection_log_10034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10035_neg : (75589133 / 500000000) ≤ -Real.log (250000 / 290801) ∧
    -Real.log (250000 / 290801) ≤ (151178267 / 1000000000) := by
  have h := checkLog_sound (w := (40801 / 540801)) (n := 12)
    (lo := (75589133 / 500000000)) (hi := (151178267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290801 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290801 / 250000) = 1/(250000 / 290801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10035 : Bounds (75589133 / 500000000) (151178267 / 1000000000) (Real.log (290801 / 250000)) := by
  have h := reflection_log_10035_neg
  have he : Real.log (290801 / 250000) = -Real.log (250000 / 290801) := by
    rw [show ((290801 / 250000) : ℝ) = ((250000 / 290801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10036_neg : (35634993 / 200000000) ≤ -Real.log (209199 / 250000) ∧
    -Real.log (209199 / 250000) ≤ (89087483 / 500000000) := by
  have h := checkLog_sound (w := (40801 / 459199)) (n := 12)
    (lo := (35634993 / 200000000)) (hi := (89087483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209199) = 1/(209199 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10036 : Bounds (-89087483 / 500000000) (-35634993 / 200000000) (Real.log (209199 / 250000)) := by
  have h := reflection_log_10036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10037_neg : (26996699 / 1000000000) ≤ -Real.log (60835278399 / 62500000000) ∧
    -Real.log (60835278399 / 62500000000) ≤ (269967 / 10000000) := by
  have h := checkLog_sound (w := (1664721601 / 123335278399)) (n := 12)
    (lo := (26996699 / 1000000000)) (hi := (269967 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60835278399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60835278399) = 1/(60835278399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10037 : Bounds (-269967 / 10000000) (-26996699 / 1000000000) (Real.log (60835278399 / 62500000000)) := by
  have h := reflection_log_10037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10038_neg : (26714777 / 1000000000) ≤ -Real.log (973638905679 / 1000000000000) ∧
    -Real.log (973638905679 / 1000000000000) ≤ (13357389 / 500000000) := by
  have h := checkLog_sound (w := (26361094321 / 1973638905679)) (n := 12)
    (lo := (26714777 / 1000000000)) (hi := (13357389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973638905679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973638905679) = 1/(973638905679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10038 : Bounds (-13357389 / 500000000) (-26714777 / 1000000000) (Real.log (973638905679 / 1000000000000)) := by
  have h := reflection_log_10038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10039_neg : (16381067 / 50000000) ≤ -Real.log (500000000000 / 693831710319) ∧
    -Real.log (500000000000 / 693831710319) ≤ (327621341 / 1000000000) := by
  have h := checkLog_sound (w := (193831710319 / 1193831710319)) (n := 12)
    (lo := (16381067 / 50000000)) (hi := (327621341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693831710319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693831710319 / 500000000000) = 1/(500000000000 / 693831710319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10039 : Bounds (16381067 / 50000000) (327621341 / 1000000000) (Real.log (693831710319 / 500000000000)) := by
  have h := reflection_log_10039_neg
  have he : Real.log (693831710319 / 500000000000) = -Real.log (500000000000 / 693831710319) := by
    rw [show ((693831710319 / 500000000000) : ℝ) = ((500000000000 / 693831710319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10040_neg : (20584577 / 62500000) ≤ -Real.log (50000000000 / 69503439309) ∧
    -Real.log (50000000000 / 69503439309) ≤ (329353233 / 1000000000) := by
  have h := checkLog_sound (w := (19503439309 / 119503439309)) (n := 12)
    (lo := (20584577 / 62500000)) (hi := (329353233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69503439309 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69503439309 / 50000000000) = 1/(50000000000 / 69503439309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10040 : Bounds (20584577 / 62500000) (329353233 / 1000000000) (Real.log (69503439309 / 50000000000)) := by
  have h := reflection_log_10040_neg
  have he : Real.log (69503439309 / 50000000000) = -Real.log (50000000000 / 69503439309) := by
    rw [show ((69503439309 / 50000000000) : ℝ) = ((50000000000 / 69503439309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10041_neg : (330533423 / 500000000) ≤ -Real.log (125000000000 / 242107195301) ∧
    -Real.log (125000000000 / 242107195301) ≤ (661066847 / 1000000000) := by
  have h := checkLog_sound (w := (117107195301 / 367107195301)) (n := 12)
    (lo := (330533423 / 500000000)) (hi := (661066847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242107195301 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242107195301 / 125000000000) = 1/(125000000000 / 242107195301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10041 : Bounds (330533423 / 500000000) (661066847 / 1000000000) (Real.log (242107195301 / 125000000000)) := by
  have h := reflection_log_10041_neg
  have he : Real.log (242107195301 / 125000000000) = -Real.log (125000000000 / 242107195301) := by
    rw [show ((242107195301 / 125000000000) : ℝ) = ((125000000000 / 242107195301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10042_neg : (663294217 / 1000000000) ≤ -Real.log (100000000000 / 194117647059) ∧
    -Real.log (100000000000 / 194117647059) ≤ (331647109 / 500000000) := by
  have h := checkLog_sound (w := (94117647059 / 294117647059)) (n := 12)
    (lo := (663294217 / 1000000000)) (hi := (331647109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194117647059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194117647059 / 100000000000) = 1/(100000000000 / 194117647059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10042 : Bounds (663294217 / 1000000000) (331647109 / 500000000) (Real.log (194117647059 / 100000000000)) := by
  have h := reflection_log_10042_neg
  have he : Real.log (194117647059 / 100000000000) = -Real.log (100000000000 / 194117647059) := by
    rw [show ((194117647059 / 100000000000) : ℝ) = ((100000000000 / 194117647059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10043_neg : (11135561 / 40000000) ≤ -Real.log (1000 / 1321) ∧
    -Real.log (1000 / 1321) ≤ (139194513 / 500000000) := by
  have h := checkLog_sound (w := (321 / 2321)) (n := 12)
    (lo := (11135561 / 40000000)) (hi := (139194513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321 / 1000) = 1/(1000 / 1321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10043 : Bounds (11135561 / 40000000) (139194513 / 500000000) (Real.log (1321 / 1000)) := by
  have h := reflection_log_10043_neg
  have he : Real.log (1321 / 1000) = -Real.log (1000 / 1321) := by
    rw [show ((1321 / 1000) : ℝ) = ((1000 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10044_neg : (387134151 / 1000000000) ≤ -Real.log (679 / 1000) ∧
    -Real.log (679 / 1000) ≤ (48391769 / 125000000) := by
  have h := checkLog_sound (w := (321 / 1679)) (n := 12)
    (lo := (387134151 / 1000000000)) (hi := (48391769 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 679) = 1/(679 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10044 : Bounds (-48391769 / 125000000) (-387134151 / 1000000000) (Real.log (679 / 1000)) := by
  have h := reflection_log_10044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10045_neg : (80237 / 250000000) ≤ -Real.log (1000000 / 1000321) ∧
    -Real.log (1000000 / 1000321) ≤ (320949 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 2000321)) (n := 12)
    (lo := (80237 / 250000000)) (hi := (320949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000321 / 1000000) = 1/(1000000 / 1000321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10045 : Bounds (80237 / 250000000) (320949 / 1000000000) (Real.log (1000321 / 1000000)) := by
  have h := reflection_log_10045_neg
  have he : Real.log (1000321 / 1000000) = -Real.log (1000000 / 1000321) := by
    rw [show ((1000321 / 1000000) : ℝ) = ((1000000 / 1000321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10046_neg : (321051 / 1000000000) ≤ -Real.log (999679 / 1000000) ∧
    -Real.log (999679 / 1000000) ≤ (80263 / 250000000) := by
  have h := checkLog_sound (w := (321 / 1999679)) (n := 12)
    (lo := (321051 / 1000000000)) (hi := (80263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999679) = 1/(999679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10046 : Bounds (-80263 / 250000000) (-321051 / 1000000000) (Real.log (999679 / 1000000)) := by
  have h := reflection_log_10046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10047_neg : (75454143 / 500000000) ≤ -Real.log (100000 / 116289) ∧
    -Real.log (100000 / 116289) ≤ (150908287 / 1000000000) := by
  have h := checkLog_sound (w := (16289 / 216289)) (n := 12)
    (lo := (75454143 / 500000000)) (hi := (150908287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116289 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116289 / 100000) = 1/(100000 / 116289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10047 : Bounds (75454143 / 500000000) (150908287 / 1000000000) (Real.log (116289 / 100000)) := by
  have h := reflection_log_10047_neg
  have he : Real.log (116289 / 100000) = -Real.log (100000 / 116289) := by
    rw [show ((116289 / 100000) : ℝ) = ((100000 / 116289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
