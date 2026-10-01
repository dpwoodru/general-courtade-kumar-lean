import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7680_neg : (114408577 / 500000000) ≤ -Real.log (500000000000 / 628556080209) ∧
    -Real.log (500000000000 / 628556080209) ≤ (45763431 / 200000000) := by
  have h := checkLog_sound (w := (128556080209 / 1128556080209)) (n := 12)
    (lo := (114408577 / 500000000)) (hi := (45763431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628556080209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628556080209 / 500000000000) = 1/(500000000000 / 628556080209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7680 : Bounds (114408577 / 500000000) (45763431 / 200000000) (Real.log (628556080209 / 500000000000)) := by
  have h := reflection_log_7680_neg
  have he : Real.log (628556080209 / 500000000000) = -Real.log (500000000000 / 628556080209) := by
    rw [show ((628556080209 / 500000000000) : ℝ) = ((500000000000 / 628556080209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7681_neg : (457833093 / 1000000000) ≤ -Real.log (100000000000 / 158064516129) ∧
    -Real.log (100000000000 / 158064516129) ≤ (228916547 / 500000000) := by
  have h := checkLog_sound (w := (58064516129 / 258064516129)) (n := 12)
    (lo := (457833093 / 1000000000)) (hi := (228916547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158064516129 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158064516129 / 100000000000) = 1/(100000000000 / 158064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7681 : Bounds (457833093 / 1000000000) (228916547 / 500000000) (Real.log (158064516129 / 100000000000)) := by
  have h := reflection_log_7681_neg
  have he : Real.log (158064516129 / 100000000000) = -Real.log (100000000000 / 158064516129) := by
    rw [show ((158064516129 / 100000000000) : ℝ) = ((100000000000 / 158064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7682_neg : (458886543 / 1000000000) ≤ -Real.log (62500000000 / 98894448031) ∧
    -Real.log (62500000000 / 98894448031) ≤ (28680409 / 62500000) := by
  have h := checkLog_sound (w := (36394448031 / 161394448031)) (n := 12)
    (lo := (458886543 / 1000000000)) (hi := (28680409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98894448031 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98894448031 / 62500000000) = 1/(62500000000 / 98894448031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7682 : Bounds (458886543 / 1000000000) (28680409 / 62500000) (Real.log (98894448031 / 62500000000)) := by
  have h := reflection_log_7682_neg
  have he : Real.log (98894448031 / 62500000000) = -Real.log (62500000000 / 98894448031) := by
    rw [show ((98894448031 / 62500000000) : ℝ) = ((62500000000 / 98894448031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7683_neg : (203756837 / 1000000000) ≤ -Real.log (500 / 613) ∧
    -Real.log (500 / 613) ≤ (101878419 / 500000000) := by
  have h := checkLog_sound (w := (113 / 1113)) (n := 12)
    (lo := (203756837 / 1000000000)) (hi := (101878419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 500) = 1/(500 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7683 : Bounds (203756837 / 1000000000) (101878419 / 500000000) (Real.log (613 / 500)) := by
  have h := reflection_log_7683_neg
  have he : Real.log (613 / 500) = -Real.log (500 / 613) := by
    rw [show ((613 / 500) : ℝ) = ((500 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7684_neg : (51236681 / 200000000) ≤ -Real.log (387 / 500) ∧
    -Real.log (387 / 500) ≤ (128091703 / 500000000) := by
  have h := checkLog_sound (w := (113 / 887)) (n := 12)
    (lo := (51236681 / 200000000)) (hi := (128091703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 387) = 1/(387 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7684 : Bounds (-128091703 / 500000000) (-51236681 / 200000000) (Real.log (387 / 500)) := by
  have h := reflection_log_7684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7685_neg : (112987 / 500000000) ≤ -Real.log (500000 / 500113) ∧
    -Real.log (500000 / 500113) ≤ (9039 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1000113)) (n := 12)
    (lo := (112987 / 500000000)) (hi := (9039 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500113 / 500000) = 1/(500000 / 500113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7685 : Bounds (112987 / 500000000) (9039 / 40000000) (Real.log (500113 / 500000)) := by
  have h := reflection_log_7685_neg
  have he : Real.log (500113 / 500000) = -Real.log (500000 / 500113) := by
    rw [show ((500113 / 500000) : ℝ) = ((500000 / 500113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7686_neg : (9041 / 40000000) ≤ -Real.log (499887 / 500000) ∧
    -Real.log (499887 / 500000) ≤ (113013 / 500000000) := by
  have h := checkLog_sound (w := (113 / 999887)) (n := 12)
    (lo := (9041 / 40000000)) (hi := (113013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499887) = 1/(499887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7686 : Bounds (-113013 / 500000000) (-9041 / 40000000) (Real.log (499887 / 500000)) := by
  have h := reflection_log_7686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7687_neg : (26919033 / 250000000) ≤ -Real.log (1000000 / 1113687) ∧
    -Real.log (1000000 / 1113687) ≤ (107676133 / 1000000000) := by
  have h := checkLog_sound (w := (113687 / 2113687)) (n := 12)
    (lo := (26919033 / 250000000)) (hi := (107676133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113687 / 1000000) = 1/(1000000 / 1113687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7687 : Bounds (26919033 / 250000000) (107676133 / 1000000000) (Real.log (1113687 / 1000000)) := by
  have h := reflection_log_7687_neg
  have he : Real.log (1113687 / 1000000) = -Real.log (1000000 / 1113687) := by
    rw [show ((1113687 / 1000000) : ℝ) = ((1000000 / 1113687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7688_neg : (120685117 / 1000000000) ≤ -Real.log (886313 / 1000000) ∧
    -Real.log (886313 / 1000000) ≤ (60342559 / 500000000) := by
  have h := checkLog_sound (w := (113687 / 1886313)) (n := 12)
    (lo := (120685117 / 1000000000)) (hi := (60342559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886313) = 1/(886313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7688 : Bounds (-60342559 / 500000000) (-120685117 / 1000000000) (Real.log (886313 / 1000000)) := by
  have h := reflection_log_7688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7689_neg : (21621767 / 200000000) ≤ -Real.log (1000000 / 1114169) ∧
    -Real.log (1000000 / 1114169) ≤ (27027209 / 250000000) := by
  have h := checkLog_sound (w := (114169 / 2114169)) (n := 12)
    (lo := (21621767 / 200000000)) (hi := (27027209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114169 / 1000000) = 1/(1000000 / 1114169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7689 : Bounds (21621767 / 200000000) (27027209 / 250000000) (Real.log (1114169 / 1000000)) := by
  have h := reflection_log_7689_neg
  have he : Real.log (1114169 / 1000000) = -Real.log (1000000 / 1114169) := by
    rw [show ((1114169 / 1000000) : ℝ) = ((1000000 / 1114169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7690_neg : (121229091 / 1000000000) ≤ -Real.log (885831 / 1000000) ∧
    -Real.log (885831 / 1000000) ≤ (30307273 / 250000000) := by
  have h := checkLog_sound (w := (114169 / 1885831)) (n := 12)
    (lo := (121229091 / 1000000000)) (hi := (30307273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885831) = 1/(885831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7690 : Bounds (-30307273 / 250000000) (-121229091 / 1000000000) (Real.log (885831 / 1000000)) := by
  have h := reflection_log_7690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7691_neg : (2624051 / 200000000) ≤ -Real.log (986965439439 / 1000000000000) ∧
    -Real.log (986965439439 / 1000000000000) ≤ (51251 / 3906250) := by
  have h := checkLog_sound (w := (13034560561 / 1986965439439)) (n := 12)
    (lo := (2624051 / 200000000)) (hi := (51251 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986965439439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986965439439) = 1/(986965439439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7691 : Bounds (-51251 / 3906250) (-2624051 / 200000000) (Real.log (986965439439 / 1000000000000)) := by
  have h := reflection_log_7691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7692_neg : (2601797 / 200000000) ≤ -Real.log (987075266031 / 1000000000000) ∧
    -Real.log (987075266031 / 1000000000000) ≤ (6504493 / 500000000) := by
  have h := checkLog_sound (w := (12924733969 / 1987075266031)) (n := 12)
    (lo := (2601797 / 200000000)) (hi := (6504493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987075266031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987075266031) = 1/(987075266031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7692 : Bounds (-6504493 / 500000000) (-2601797 / 200000000) (Real.log (987075266031 / 1000000000000)) := by
  have h := reflection_log_7692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7693_neg : (182689 / 800000) ≤ -Real.log (500000000000 / 628269584221) ∧
    -Real.log (500000000000 / 628269584221) ≤ (228361251 / 1000000000) := by
  have h := checkLog_sound (w := (128269584221 / 1128269584221)) (n := 12)
    (lo := (182689 / 800000)) (hi := (228361251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628269584221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628269584221 / 500000000000) = 1/(500000000000 / 628269584221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7693 : Bounds (182689 / 800000) (228361251 / 1000000000) (Real.log (628269584221 / 500000000000)) := by
  have h := reflection_log_7693_neg
  have he : Real.log (628269584221 / 500000000000) = -Real.log (500000000000 / 628269584221) := by
    rw [show ((628269584221 / 500000000000) : ℝ) = ((500000000000 / 628269584221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7694_neg : (229337927 / 1000000000) ≤ -Real.log (7812500000 / 9826304693) ∧
    -Real.log (7812500000 / 9826304693) ≤ (28667241 / 125000000) := by
  have h := checkLog_sound (w := (2013804693 / 17638804693)) (n := 12)
    (lo := (229337927 / 1000000000)) (hi := (28667241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9826304693 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9826304693 / 7812500000) = 1/(7812500000 / 9826304693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7694 : Bounds (229337927 / 1000000000) (28667241 / 125000000) (Real.log (9826304693 / 7812500000)) := by
  have h := reflection_log_7694_neg
  have he : Real.log (9826304693 / 7812500000) = -Real.log (7812500000 / 9826304693) := by
    rw [show ((9826304693 / 7812500000) : ℝ) = ((7812500000 / 9826304693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7695_neg : (458886543 / 1000000000) ≤ -Real.log (500000000000 / 791155584247) ∧
    -Real.log (500000000000 / 791155584247) ≤ (28680409 / 62500000) := by
  have h := checkLog_sound (w := (291155584247 / 1291155584247)) (n := 12)
    (lo := (458886543 / 1000000000)) (hi := (28680409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791155584247 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791155584247 / 500000000000) = 1/(500000000000 / 791155584247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7695 : Bounds (458886543 / 1000000000) (28680409 / 62500000) (Real.log (791155584247 / 500000000000)) := by
  have h := reflection_log_7695_neg
  have he : Real.log (791155584247 / 500000000000) = -Real.log (500000000000 / 791155584247) := by
    rw [show ((791155584247 / 500000000000) : ℝ) = ((500000000000 / 791155584247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7696_neg : (229970121 / 500000000) ≤ -Real.log (500000000000 / 791989664083) ∧
    -Real.log (500000000000 / 791989664083) ≤ (459940243 / 1000000000) := by
  have h := checkLog_sound (w := (291989664083 / 1291989664083)) (n := 12)
    (lo := (229970121 / 500000000)) (hi := (459940243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791989664083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791989664083 / 500000000000) = 1/(500000000000 / 791989664083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7696 : Bounds (229970121 / 500000000) (459940243 / 1000000000) (Real.log (791989664083 / 500000000000)) := by
  have h := reflection_log_7696_neg
  have he : Real.log (791989664083 / 500000000000) = -Real.log (500000000000 / 791989664083) := by
    rw [show ((791989664083 / 500000000000) : ℝ) = ((500000000000 / 791989664083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7697_neg : (25520573 / 125000000) ≤ -Real.log (2000 / 2453) ∧
    -Real.log (2000 / 2453) ≤ (40832917 / 200000000) := by
  have h := checkLog_sound (w := (453 / 4453)) (n := 12)
    (lo := (25520573 / 125000000)) (hi := (40832917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2453 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2453 / 2000) = 1/(2000 / 2453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7697 : Bounds (25520573 / 125000000) (40832917 / 200000000) (Real.log (2453 / 2000)) := by
  have h := reflection_log_7697_neg
  have he : Real.log (2453 / 2000) = -Real.log (2000 / 2453) := by
    rw [show ((2453 / 2000) : ℝ) = ((2000 / 2453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7698_neg : (32103701 / 125000000) ≤ -Real.log (1547 / 2000) ∧
    -Real.log (1547 / 2000) ≤ (256829609 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 3547)) (n := 12)
    (lo := (32103701 / 125000000)) (hi := (256829609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1547) = 1/(1547 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7698 : Bounds (-256829609 / 1000000000) (-32103701 / 125000000) (Real.log (1547 / 2000)) := by
  have h := reflection_log_7698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7699_neg : (113237 / 500000000) ≤ -Real.log (2000000 / 2000453) ∧
    -Real.log (2000000 / 2000453) ≤ (9059 / 40000000) := by
  have h := checkLog_sound (w := (453 / 4000453)) (n := 12)
    (lo := (113237 / 500000000)) (hi := (9059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000453 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000453 / 2000000) = 1/(2000000 / 2000453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7699 : Bounds (113237 / 500000000) (9059 / 40000000) (Real.log (2000453 / 2000000)) := by
  have h := reflection_log_7699_neg
  have he : Real.log (2000453 / 2000000) = -Real.log (2000000 / 2000453) := by
    rw [show ((2000453 / 2000000) : ℝ) = ((2000000 / 2000453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7700_neg : (9061 / 40000000) ≤ -Real.log (1999547 / 2000000) ∧
    -Real.log (1999547 / 2000000) ≤ (113263 / 500000000) := by
  have h := checkLog_sound (w := (453 / 3999547)) (n := 12)
    (lo := (9061 / 40000000)) (hi := (113263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999547) = 1/(1999547 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7700 : Bounds (-113263 / 500000000) (-9061 / 40000000) (Real.log (1999547 / 2000000)) := by
  have h := reflection_log_7700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7701_neg : (10790687 / 100000000) ≤ -Real.log (125000 / 139243) ∧
    -Real.log (125000 / 139243) ≤ (107906871 / 1000000000) := by
  have h := checkLog_sound (w := (14243 / 264243)) (n := 12)
    (lo := (10790687 / 100000000)) (hi := (107906871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139243 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139243 / 125000) = 1/(125000 / 139243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7701 : Bounds (10790687 / 100000000) (107906871 / 1000000000) (Real.log (139243 / 125000)) := by
  have h := reflection_log_7701_neg
  have he : Real.log (139243 / 125000) = -Real.log (125000 / 139243) := by
    rw [show ((139243 / 125000) : ℝ) = ((125000 / 139243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7702_neg : (30243781 / 250000000) ≤ -Real.log (110757 / 125000) ∧
    -Real.log (110757 / 125000) ≤ (967801 / 8000000) := by
  have h := checkLog_sound (w := (14243 / 235757)) (n := 12)
    (lo := (30243781 / 250000000)) (hi := (967801 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110757) = 1/(110757 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7702 : Bounds (-967801 / 8000000) (-30243781 / 250000000) (Real.log (110757 / 125000)) := by
  have h := reflection_log_7702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7703_neg : (54169737 / 500000000) ≤ -Real.log (500000 / 557213) ∧
    -Real.log (500000 / 557213) ≤ (4333579 / 40000000) := by
  have h := checkLog_sound (w := (57213 / 1057213)) (n := 12)
    (lo := (54169737 / 500000000)) (hi := (4333579 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557213 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557213 / 500000) = 1/(500000 / 557213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7703 : Bounds (54169737 / 500000000) (4333579 / 40000000) (Real.log (557213 / 500000)) := by
  have h := reflection_log_7703_neg
  have he : Real.log (557213 / 500000) = -Real.log (500000 / 557213) := by
    rw [show ((557213 / 500000) : ℝ) = ((500000 / 557213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7704_neg : (15189907 / 125000000) ≤ -Real.log (442787 / 500000) ∧
    -Real.log (442787 / 500000) ≤ (121519257 / 1000000000) := by
  have h := checkLog_sound (w := (57213 / 942787)) (n := 12)
    (lo := (15189907 / 125000000)) (hi := (121519257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442787) = 1/(442787 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7704 : Bounds (-121519257 / 1000000000) (-15189907 / 125000000) (Real.log (442787 / 500000)) := by
  have h := reflection_log_7704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7705_neg : (6589891 / 500000000) ≤ -Real.log (246726672631 / 250000000000) ∧
    -Real.log (246726672631 / 250000000000) ≤ (13179783 / 1000000000) := by
  have h := checkLog_sound (w := (3273327369 / 496726672631)) (n := 12)
    (lo := (6589891 / 500000000)) (hi := (13179783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246726672631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246726672631) = 1/(246726672631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7705 : Bounds (-13179783 / 1000000000) (-6589891 / 500000000) (Real.log (246726672631 / 250000000000)) := by
  have h := reflection_log_7705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7706_neg : (6534127 / 500000000) ≤ -Real.log (15422136951 / 15625000000) ∧
    -Real.log (15422136951 / 15625000000) ≤ (2613651 / 200000000) := by
  have h := checkLog_sound (w := (202863049 / 31047136951)) (n := 12)
    (lo := (6534127 / 500000000)) (hi := (2613651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15422136951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15422136951) = 1/(15422136951 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7706 : Bounds (-2613651 / 200000000) (-6534127 / 500000000) (Real.log (15422136951 / 15625000000)) := by
  have h := reflection_log_7706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7707_neg : (45776399 / 200000000) ≤ -Real.log (500000000000 / 628596838123) ∧
    -Real.log (500000000000 / 628596838123) ≤ (57220499 / 250000000) := by
  have h := checkLog_sound (w := (128596838123 / 1128596838123)) (n := 12)
    (lo := (45776399 / 200000000)) (hi := (57220499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628596838123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628596838123 / 500000000000) = 1/(500000000000 / 628596838123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7707 : Bounds (45776399 / 200000000) (57220499 / 250000000) (Real.log (628596838123 / 500000000000)) := by
  have h := reflection_log_7707_neg
  have he : Real.log (628596838123 / 500000000000) = -Real.log (500000000000 / 628596838123) := by
    rw [show ((628596838123 / 500000000000) : ℝ) = ((500000000000 / 628596838123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7708_neg : (22985873 / 100000000) ≤ -Real.log (250000000000 / 314605555267) ∧
    -Real.log (250000000000 / 314605555267) ≤ (229858731 / 1000000000) := by
  have h := checkLog_sound (w := (64605555267 / 564605555267)) (n := 12)
    (lo := (22985873 / 100000000)) (hi := (229858731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314605555267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314605555267 / 250000000000) = 1/(250000000000 / 314605555267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7708 : Bounds (22985873 / 100000000) (229858731 / 1000000000) (Real.log (314605555267 / 250000000000)) := by
  have h := reflection_log_7708_neg
  have he : Real.log (314605555267 / 250000000000) = -Real.log (250000000000 / 314605555267) := by
    rw [show ((314605555267 / 250000000000) : ℝ) = ((250000000000 / 314605555267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7709_neg : (229970121 / 500000000) ≤ -Real.log (250000000000 / 395994832041) ∧
    -Real.log (250000000000 / 395994832041) ≤ (459940243 / 1000000000) := by
  have h := checkLog_sound (w := (145994832041 / 645994832041)) (n := 12)
    (lo := (229970121 / 500000000)) (hi := (459940243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395994832041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395994832041 / 250000000000) = 1/(250000000000 / 395994832041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7709 : Bounds (229970121 / 500000000) (459940243 / 1000000000) (Real.log (395994832041 / 250000000000)) := by
  have h := reflection_log_7709_neg
  have he : Real.log (395994832041 / 250000000000) = -Real.log (250000000000 / 395994832041) := by
    rw [show ((395994832041 / 250000000000) : ℝ) = ((250000000000 / 395994832041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7710_neg : (460994193 / 1000000000) ≤ -Real.log (500000000000 / 792824822237) ∧
    -Real.log (500000000000 / 792824822237) ≤ (230497097 / 500000000) := by
  have h := checkLog_sound (w := (292824822237 / 1292824822237)) (n := 12)
    (lo := (460994193 / 1000000000)) (hi := (230497097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792824822237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792824822237 / 500000000000) = 1/(500000000000 / 792824822237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7710 : Bounds (460994193 / 1000000000) (230497097 / 500000000) (Real.log (792824822237 / 500000000000)) := by
  have h := reflection_log_7710_neg
  have he : Real.log (792824822237 / 500000000000) = -Real.log (500000000000 / 792824822237) := by
    rw [show ((792824822237 / 500000000000) : ℝ) = ((500000000000 / 792824822237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7711_neg : (40914433 / 200000000) ≤ -Real.log (1000 / 1227) ∧
    -Real.log (1000 / 1227) ≤ (102286083 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2227)) (n := 12)
    (lo := (40914433 / 200000000)) (hi := (102286083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227 / 1000) = 1/(1000 / 1227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7711 : Bounds (40914433 / 200000000) (102286083 / 500000000) (Real.log (1227 / 1000)) := by
  have h := reflection_log_7711_neg
  have he : Real.log (1227 / 1000) = -Real.log (1000 / 1227) := by
    rw [show ((1227 / 1000) : ℝ) = ((1000 / 1227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7712_neg : (25747623 / 100000000) ≤ -Real.log (773 / 1000) ∧
    -Real.log (773 / 1000) ≤ (257476231 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1773)) (n := 12)
    (lo := (25747623 / 100000000)) (hi := (257476231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 773) = 1/(773 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7712 : Bounds (-257476231 / 1000000000) (-25747623 / 100000000) (Real.log (773 / 1000)) := by
  have h := reflection_log_7712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7713_neg : (113487 / 500000000) ≤ -Real.log (1000000 / 1000227) ∧
    -Real.log (1000000 / 1000227) ≤ (9079 / 40000000) := by
  have h := checkLog_sound (w := (227 / 2000227)) (n := 12)
    (lo := (113487 / 500000000)) (hi := (9079 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000227 / 1000000) = 1/(1000000 / 1000227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7713 : Bounds (113487 / 500000000) (9079 / 40000000) (Real.log (1000227 / 1000000)) := by
  have h := reflection_log_7713_neg
  have he : Real.log (1000227 / 1000000) = -Real.log (1000000 / 1000227) := by
    rw [show ((1000227 / 1000000) : ℝ) = ((1000000 / 1000227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7714_neg : (9081 / 40000000) ≤ -Real.log (999773 / 1000000) ∧
    -Real.log (999773 / 1000000) ≤ (113513 / 500000000) := by
  have h := checkLog_sound (w := (227 / 1999773)) (n := 12)
    (lo := (9081 / 40000000)) (hi := (113513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999773) = 1/(999773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7714 : Bounds (-113513 / 500000000) (-9081 / 40000000) (Real.log (999773 / 1000000)) := by
  have h := reflection_log_7714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7715_neg : (27034389 / 250000000) ≤ -Real.log (1000000 / 1114201) ∧
    -Real.log (1000000 / 1114201) ≤ (108137557 / 1000000000) := by
  have h := checkLog_sound (w := (114201 / 2114201)) (n := 12)
    (lo := (27034389 / 250000000)) (hi := (108137557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114201 / 1000000) = 1/(1000000 / 1114201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7715 : Bounds (27034389 / 250000000) (108137557 / 1000000000) (Real.log (1114201 / 1000000)) := by
  have h := reflection_log_7715_neg
  have he : Real.log (1114201 / 1000000) = -Real.log (1000000 / 1114201) := by
    rw [show ((1114201 / 1000000) : ℝ) = ((1000000 / 1114201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7716_neg : (1894769 / 15625000) ≤ -Real.log (885799 / 1000000) ∧
    -Real.log (885799 / 1000000) ≤ (121265217 / 1000000000) := by
  have h := checkLog_sound (w := (114201 / 1885799)) (n := 12)
    (lo := (1894769 / 15625000)) (hi := (121265217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885799) = 1/(885799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7716 : Bounds (-121265217 / 1000000000) (-1894769 / 15625000) (Real.log (885799 / 1000000)) := by
  have h := reflection_log_7716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7717_neg : (27142739 / 250000000) ≤ -Real.log (250000 / 278671) ∧
    -Real.log (250000 / 278671) ≤ (108570957 / 1000000000) := by
  have h := checkLog_sound (w := (28671 / 528671)) (n := 12)
    (lo := (27142739 / 250000000)) (hi := (108570957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278671 / 250000) = 1/(250000 / 278671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7717 : Bounds (27142739 / 250000000) (108570957 / 1000000000) (Real.log (278671 / 250000)) := by
  have h := reflection_log_7717_neg
  have he : Real.log (278671 / 250000) = -Real.log (250000 / 278671) := by
    rw [show ((278671 / 250000) : ℝ) = ((250000 / 278671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7718_neg : (24362127 / 200000000) ≤ -Real.log (221329 / 250000) ∧
    -Real.log (221329 / 250000) ≤ (30452659 / 250000000) := by
  have h := checkLog_sound (w := (28671 / 471329)) (n := 12)
    (lo := (24362127 / 200000000)) (hi := (30452659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221329) = 1/(221329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7718 : Bounds (-30452659 / 250000000) (-24362127 / 200000000) (Real.log (221329 / 250000)) := by
  have h := reflection_log_7718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7719_neg : (6619839 / 500000000) ≤ -Real.log (61677973759 / 62500000000) ∧
    -Real.log (61677973759 / 62500000000) ≤ (13239679 / 1000000000) := by
  have h := checkLog_sound (w := (822026241 / 124177973759)) (n := 12)
    (lo := (6619839 / 500000000)) (hi := (13239679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61677973759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61677973759) = 1/(61677973759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7719 : Bounds (-13239679 / 1000000000) (-6619839 / 500000000) (Real.log (61677973759 / 62500000000)) := by
  have h := reflection_log_7719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7720_neg : (656383 / 50000000) ≤ -Real.log (986958131599 / 1000000000000) ∧
    -Real.log (986958131599 / 1000000000000) ≤ (13127661 / 1000000000) := by
  have h := checkLog_sound (w := (13041868401 / 1986958131599)) (n := 12)
    (lo := (656383 / 50000000)) (hi := (13127661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986958131599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986958131599) = 1/(986958131599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7720 : Bounds (-13127661 / 1000000000) (-656383 / 50000000) (Real.log (986958131599 / 1000000000000)) := by
  have h := reflection_log_7720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7721_neg : (57350693 / 250000000) ≤ -Real.log (500000000000 / 628924281919) ∧
    -Real.log (500000000000 / 628924281919) ≤ (229402773 / 1000000000) := by
  have h := checkLog_sound (w := (128924281919 / 1128924281919)) (n := 12)
    (lo := (57350693 / 250000000)) (hi := (229402773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628924281919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628924281919 / 500000000000) = 1/(500000000000 / 628924281919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7721 : Bounds (57350693 / 250000000) (229402773 / 1000000000) (Real.log (628924281919 / 500000000000)) := by
  have h := reflection_log_7721_neg
  have he : Real.log (628924281919 / 500000000000) = -Real.log (500000000000 / 628924281919) := by
    rw [show ((628924281919 / 500000000000) : ℝ) = ((500000000000 / 628924281919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7722_neg : (28797699 / 125000000) ≤ -Real.log (500000000000 / 629540186781) ∧
    -Real.log (500000000000 / 629540186781) ≤ (230381593 / 1000000000) := by
  have h := checkLog_sound (w := (129540186781 / 1129540186781)) (n := 12)
    (lo := (28797699 / 125000000)) (hi := (230381593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629540186781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629540186781 / 500000000000) = 1/(500000000000 / 629540186781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7722 : Bounds (28797699 / 125000000) (230381593 / 1000000000) (Real.log (629540186781 / 500000000000)) := by
  have h := reflection_log_7722_neg
  have he : Real.log (629540186781 / 500000000000) = -Real.log (500000000000 / 629540186781) := by
    rw [show ((629540186781 / 500000000000) : ℝ) = ((500000000000 / 629540186781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7723_neg : (460994193 / 1000000000) ≤ -Real.log (125000000000 / 198206205559) ∧
    -Real.log (125000000000 / 198206205559) ≤ (230497097 / 500000000) := by
  have h := checkLog_sound (w := (73206205559 / 323206205559)) (n := 12)
    (lo := (460994193 / 1000000000)) (hi := (230497097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198206205559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198206205559 / 125000000000) = 1/(125000000000 / 198206205559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7723 : Bounds (460994193 / 1000000000) (230497097 / 500000000) (Real.log (198206205559 / 125000000000)) := by
  have h := reflection_log_7723_neg
  have he : Real.log (198206205559 / 125000000000) = -Real.log (125000000000 / 198206205559) := by
    rw [show ((198206205559 / 125000000000) : ℝ) = ((125000000000 / 198206205559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7724_neg : (115512099 / 250000000) ≤ -Real.log (500000000000 / 793661060803) ∧
    -Real.log (500000000000 / 793661060803) ≤ (462048397 / 1000000000) := by
  have h := checkLog_sound (w := (293661060803 / 1293661060803)) (n := 12)
    (lo := (115512099 / 250000000)) (hi := (462048397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793661060803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793661060803 / 500000000000) = 1/(500000000000 / 793661060803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7724 : Bounds (115512099 / 250000000) (462048397 / 1000000000) (Real.log (793661060803 / 500000000000)) := by
  have h := reflection_log_7724_neg
  have he : Real.log (793661060803 / 500000000000) = -Real.log (500000000000 / 793661060803) := by
    rw [show ((793661060803 / 500000000000) : ℝ) = ((500000000000 / 793661060803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7725_neg : (10248979 / 50000000) ≤ -Real.log (400 / 491) ∧
    -Real.log (400 / 491) ≤ (204979581 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 891)) (n := 12)
    (lo := (10248979 / 50000000)) (hi := (204979581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 400) = 1/(400 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7725 : Bounds (10248979 / 50000000) (204979581 / 1000000000) (Real.log (491 / 400)) := by
  have h := reflection_log_7725_neg
  have he : Real.log (491 / 400) = -Real.log (400 / 491) := by
    rw [show ((491 / 400) : ℝ) = ((400 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7726_neg : (25812327 / 100000000) ≤ -Real.log (309 / 400) ∧
    -Real.log (309 / 400) ≤ (258123271 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 709)) (n := 12)
    (lo := (25812327 / 100000000)) (hi := (258123271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 309) = 1/(309 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7726 : Bounds (-258123271 / 1000000000) (-25812327 / 100000000) (Real.log (309 / 400)) := by
  have h := reflection_log_7726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7727_neg : (113737 / 500000000) ≤ -Real.log (400000 / 400091) ∧
    -Real.log (400000 / 400091) ≤ (9099 / 40000000) := by
  have h := checkLog_sound (w := (91 / 800091)) (n := 12)
    (lo := (113737 / 500000000)) (hi := (9099 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400091 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400091 / 400000) = 1/(400000 / 400091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7727 : Bounds (113737 / 500000000) (9099 / 40000000) (Real.log (400091 / 400000)) := by
  have h := reflection_log_7727_neg
  have he : Real.log (400091 / 400000) = -Real.log (400000 / 400091) := by
    rw [show ((400091 / 400000) : ℝ) = ((400000 / 400091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7728_neg : (9101 / 40000000) ≤ -Real.log (399909 / 400000) ∧
    -Real.log (399909 / 400000) ≤ (113763 / 500000000) := by
  have h := checkLog_sound (w := (91 / 799909)) (n := 12)
    (lo := (9101 / 40000000)) (hi := (113763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399909) = 1/(399909 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7728 : Bounds (-113763 / 500000000) (-9101 / 40000000) (Real.log (399909 / 400000)) := by
  have h := reflection_log_7728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7729_neg : (27092047 / 250000000) ≤ -Real.log (500000 / 557229) ∧
    -Real.log (500000 / 557229) ≤ (108368189 / 1000000000) := by
  have h := checkLog_sound (w := (57229 / 1057229)) (n := 12)
    (lo := (27092047 / 250000000)) (hi := (108368189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557229 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557229 / 500000) = 1/(500000 / 557229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7729 : Bounds (27092047 / 250000000) (108368189 / 1000000000) (Real.log (557229 / 500000)) := by
  have h := reflection_log_7729_neg
  have he : Real.log (557229 / 500000) = -Real.log (500000 / 557229) := by
    rw [show ((557229 / 500000) : ℝ) = ((500000 / 557229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7730_neg : (1899303 / 15625000) ≤ -Real.log (442771 / 500000) ∧
    -Real.log (442771 / 500000) ≤ (121555393 / 1000000000) := by
  have h := checkLog_sound (w := (57229 / 942771)) (n := 12)
    (lo := (1899303 / 15625000)) (hi := (121555393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442771) = 1/(442771 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7730 : Bounds (-121555393 / 1000000000) (-1899303 / 15625000) (Real.log (442771 / 500000)) := by
  have h := reflection_log_7730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7731_neg : (6800093 / 62500000) ≤ -Real.log (1000000 / 1114941) ∧
    -Real.log (1000000 / 1114941) ≤ (108801489 / 1000000000) := by
  have h := checkLog_sound (w := (114941 / 2114941)) (n := 12)
    (lo := (6800093 / 62500000)) (hi := (108801489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1114941 / 1000000) = 1/(1000000 / 1114941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7731 : Bounds (6800093 / 62500000) (108801489 / 1000000000) (Real.log (1114941 / 1000000)) := by
  have h := reflection_log_7731_neg
  have he : Real.log (1114941 / 1000000) = -Real.log (1000000 / 1114941) := by
    rw [show ((1114941 / 1000000) : ℝ) = ((1000000 / 1114941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7732_neg : (122100969 / 1000000000) ≤ -Real.log (885059 / 1000000) ∧
    -Real.log (885059 / 1000000) ≤ (12210097 / 100000000) := by
  have h := checkLog_sound (w := (114941 / 1885059)) (n := 12)
    (lo := (122100969 / 1000000000)) (hi := (12210097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 885059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 885059) = 1/(885059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7732 : Bounds (-12210097 / 100000000) (-122100969 / 1000000000) (Real.log (885059 / 1000000)) := by
  have h := reflection_log_7732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7733_neg : (332487 / 25000000) ≤ -Real.log (986788566519 / 1000000000000) ∧
    -Real.log (986788566519 / 1000000000000) ≤ (13299481 / 1000000000) := by
  have h := checkLog_sound (w := (13211433481 / 1986788566519)) (n := 12)
    (lo := (332487 / 25000000)) (hi := (13299481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986788566519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986788566519) = 1/(986788566519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7733 : Bounds (-13299481 / 1000000000) (-332487 / 25000000) (Real.log (986788566519 / 1000000000000)) := by
  have h := reflection_log_7733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7734_neg : (13187203 / 1000000000) ≤ -Real.log (246724841559 / 250000000000) ∧
    -Real.log (246724841559 / 250000000000) ≤ (3296801 / 250000000) := by
  have h := checkLog_sound (w := (3275158441 / 496724841559)) (n := 12)
    (lo := (13187203 / 1000000000)) (hi := (3296801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246724841559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246724841559) = 1/(246724841559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7734 : Bounds (-3296801 / 250000000) (-13187203 / 1000000000) (Real.log (246724841559 / 250000000000)) := by
  have h := reflection_log_7734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7735_neg : (11496179 / 50000000) ≤ -Real.log (20000000000 / 25170076631) ∧
    -Real.log (20000000000 / 25170076631) ≤ (229923581 / 1000000000) := by
  have h := checkLog_sound (w := (5170076631 / 45170076631)) (n := 12)
    (lo := (11496179 / 50000000)) (hi := (229923581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25170076631 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25170076631 / 20000000000) = 1/(20000000000 / 25170076631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7735 : Bounds (11496179 / 50000000) (229923581 / 1000000000) (Real.log (25170076631 / 20000000000)) := by
  have h := reflection_log_7735_neg
  have he : Real.log (25170076631 / 20000000000) = -Real.log (20000000000 / 25170076631) := by
    rw [show ((25170076631 / 20000000000) : ℝ) = ((20000000000 / 25170076631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7736_neg : (115451229 / 500000000) ≤ -Real.log (12500000000 / 15746704457) ∧
    -Real.log (12500000000 / 15746704457) ≤ (230902459 / 1000000000) := by
  have h := checkLog_sound (w := (3246704457 / 28246704457)) (n := 12)
    (lo := (115451229 / 500000000)) (hi := (230902459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15746704457 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15746704457 / 12500000000) = 1/(12500000000 / 15746704457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7736 : Bounds (115451229 / 500000000) (230902459 / 1000000000) (Real.log (15746704457 / 12500000000)) := by
  have h := reflection_log_7736_neg
  have he : Real.log (15746704457 / 12500000000) = -Real.log (12500000000 / 15746704457) := by
    rw [show ((15746704457 / 12500000000) : ℝ) = ((12500000000 / 15746704457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7737_neg : (115512099 / 250000000) ≤ -Real.log (250000000000 / 396830530401) ∧
    -Real.log (250000000000 / 396830530401) ≤ (462048397 / 1000000000) := by
  have h := checkLog_sound (w := (146830530401 / 646830530401)) (n := 12)
    (lo := (115512099 / 250000000)) (hi := (462048397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396830530401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396830530401 / 250000000000) = 1/(250000000000 / 396830530401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7737 : Bounds (115512099 / 250000000) (462048397 / 1000000000) (Real.log (396830530401 / 250000000000)) := by
  have h := reflection_log_7737_neg
  have he : Real.log (396830530401 / 250000000000) = -Real.log (250000000000 / 396830530401) := by
    rw [show ((396830530401 / 250000000000) : ℝ) = ((250000000000 / 396830530401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7738_neg : (9262057 / 20000000) ≤ -Real.log (250000000000 / 397249190939) ∧
    -Real.log (250000000000 / 397249190939) ≤ (463102851 / 1000000000) := by
  have h := checkLog_sound (w := (147249190939 / 647249190939)) (n := 12)
    (lo := (9262057 / 20000000)) (hi := (463102851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397249190939 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397249190939 / 250000000000) = 1/(250000000000 / 397249190939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7738 : Bounds (9262057 / 20000000) (463102851 / 1000000000) (Real.log (397249190939 / 250000000000)) := by
  have h := reflection_log_7738_neg
  have he : Real.log (397249190939 / 250000000000) = -Real.log (250000000000 / 397249190939) := by
    rw [show ((397249190939 / 250000000000) : ℝ) = ((250000000000 / 397249190939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7739_neg : (205386829 / 1000000000) ≤ -Real.log (250 / 307) ∧
    -Real.log (250 / 307) ≤ (20538683 / 100000000) := by
  have h := checkLog_sound (w := (57 / 557)) (n := 12)
    (lo := (205386829 / 1000000000)) (hi := (20538683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307 / 250) = 1/(250 / 307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7739 : Bounds (205386829 / 1000000000) (20538683 / 100000000) (Real.log (307 / 250)) := by
  have h := reflection_log_7739_neg
  have he : Real.log (307 / 250) = -Real.log (250 / 307) := by
    rw [show ((307 / 250) : ℝ) = ((250 / 307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7740_neg : (32346341 / 125000000) ≤ -Real.log (193 / 250) ∧
    -Real.log (193 / 250) ≤ (258770729 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 443)) (n := 12)
    (lo := (32346341 / 125000000)) (hi := (258770729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 193) = 1/(193 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7740 : Bounds (-258770729 / 1000000000) (-32346341 / 125000000) (Real.log (193 / 250)) := by
  have h := reflection_log_7740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7741_neg : (113987 / 500000000) ≤ -Real.log (250000 / 250057) ∧
    -Real.log (250000 / 250057) ≤ (9119 / 40000000) := by
  have h := checkLog_sound (w := (57 / 500057)) (n := 12)
    (lo := (113987 / 500000000)) (hi := (9119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250057 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250057 / 250000) = 1/(250000 / 250057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7741 : Bounds (113987 / 500000000) (9119 / 40000000) (Real.log (250057 / 250000)) := by
  have h := reflection_log_7741_neg
  have he : Real.log (250057 / 250000) = -Real.log (250000 / 250057) := by
    rw [show ((250057 / 250000) : ℝ) = ((250000 / 250057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7742_neg : (9121 / 40000000) ≤ -Real.log (249943 / 250000) ∧
    -Real.log (249943 / 250000) ≤ (114013 / 500000000) := by
  have h := checkLog_sound (w := (57 / 499943)) (n := 12)
    (lo := (9121 / 40000000)) (hi := (114013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249943) = 1/(249943 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7742 : Bounds (-114013 / 500000000) (-9121 / 40000000) (Real.log (249943 / 250000)) := by
  have h := reflection_log_7742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7743_neg : (54299383 / 500000000) ≤ -Real.log (200000 / 222943) ∧
    -Real.log (200000 / 222943) ≤ (108598767 / 1000000000) := by
  have h := checkLog_sound (w := (22943 / 422943)) (n := 12)
    (lo := (54299383 / 500000000)) (hi := (108598767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222943 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222943 / 200000) = 1/(200000 / 222943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7743 : Bounds (54299383 / 500000000) (108598767 / 1000000000) (Real.log (222943 / 200000)) := by
  have h := reflection_log_7743_neg
  have he : Real.log (222943 / 200000) = -Real.log (200000 / 222943) := by
    rw [show ((222943 / 200000) : ℝ) = ((200000 / 222943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
