import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11072_neg : (25126341 / 50000000) ≤ -Real.log (121 / 200) ∧
    -Real.log (121 / 200) ≤ (502526821 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 121) = 1/(121 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11072 : Bounds (-502526821 / 1000000000) (-25126341 / 50000000) (Real.log (121 / 200)) := by
  have h := reflection_log_11072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11073_neg : (197461 / 500000000) ≤ -Real.log (200000 / 200079) ∧
    -Real.log (200000 / 200079) ≤ (394923 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 400079)) (n := 12)
    (lo := (197461 / 500000000)) (hi := (394923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200079 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200079 / 200000) = 1/(200000 / 200079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11073 : Bounds (197461 / 500000000) (394923 / 1000000000) (Real.log (200079 / 200000)) := by
  have h := reflection_log_11073_neg
  have he : Real.log (200079 / 200000) = -Real.log (200000 / 200079) := by
    rw [show ((200079 / 200000) : ℝ) = ((200000 / 200079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11074_neg : (197539 / 500000000) ≤ -Real.log (199921 / 200000) ∧
    -Real.log (199921 / 200000) ≤ (395079 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 399921)) (n := 12)
    (lo := (197539 / 500000000)) (hi := (395079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199921) = 1/(199921 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11074 : Bounds (-395079 / 1000000000) (-197539 / 500000000) (Real.log (199921 / 200000)) := by
  have h := reflection_log_11074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11075_neg : (184479227 / 1000000000) ≤ -Real.log (31250 / 37581) ∧
    -Real.log (31250 / 37581) ≤ (46119807 / 250000000) := by
  have h := checkLog_sound (w := (6331 / 68831)) (n := 12)
    (lo := (184479227 / 1000000000)) (hi := (46119807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37581 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37581 / 31250) = 1/(31250 / 37581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11075 : Bounds (184479227 / 1000000000) (46119807 / 250000000) (Real.log (37581 / 31250)) := by
  have h := reflection_log_11075_neg
  have he : Real.log (37581 / 31250) = -Real.log (31250 / 37581) := by
    rw [show ((37581 / 31250) : ℝ) = ((31250 / 37581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11076_neg : (226388811 / 1000000000) ≤ -Real.log (24919 / 31250) ∧
    -Real.log (24919 / 31250) ≤ (56597203 / 250000000) := by
  have h := checkLog_sound (w := (6331 / 56169)) (n := 12)
    (lo := (226388811 / 1000000000)) (hi := (56597203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24919) = 1/(24919 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11076 : Bounds (-56597203 / 250000000) (-226388811 / 1000000000) (Real.log (24919 / 31250)) := by
  have h := reflection_log_11076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11077_neg : (185251427 / 1000000000) ≤ -Real.log (1000000 / 1203521) ∧
    -Real.log (1000000 / 1203521) ≤ (46312857 / 250000000) := by
  have h := checkLog_sound (w := (203521 / 2203521)) (n := 12)
    (lo := (185251427 / 1000000000)) (hi := (46312857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203521 / 1000000) = 1/(1000000 / 1203521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11077 : Bounds (185251427 / 1000000000) (46312857 / 250000000) (Real.log (1203521 / 1000000)) := by
  have h := reflection_log_11077_neg
  have he : Real.log (1203521 / 1000000) = -Real.log (1000000 / 1203521) := by
    rw [show ((1203521 / 1000000) : ℝ) = ((1000000 / 1203521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11078_neg : (45510903 / 200000000) ≤ -Real.log (796479 / 1000000) ∧
    -Real.log (796479 / 1000000) ≤ (56888629 / 250000000) := by
  have h := checkLog_sound (w := (203521 / 1796479)) (n := 12)
    (lo := (45510903 / 200000000)) (hi := (56888629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796479) = 1/(796479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11078 : Bounds (-56888629 / 250000000) (-45510903 / 200000000) (Real.log (796479 / 1000000)) := by
  have h := reflection_log_11078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11079_neg : (2643943 / 62500000) ≤ -Real.log (958579202559 / 1000000000000) ∧
    -Real.log (958579202559 / 1000000000000) ≤ (42303089 / 1000000000) := by
  have h := checkLog_sound (w := (41420797441 / 1958579202559)) (n := 12)
    (lo := (2643943 / 62500000)) (hi := (42303089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958579202559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958579202559) = 1/(958579202559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11079 : Bounds (-42303089 / 1000000000) (-2643943 / 62500000) (Real.log (958579202559 / 1000000000000)) := by
  have h := reflection_log_11079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11080_neg : (2619349 / 62500000) ≤ -Real.log (936480939 / 976562500) ∧
    -Real.log (936480939 / 976562500) ≤ (8381917 / 200000000) := by
  have h := checkLog_sound (w := (40081561 / 1913043439)) (n := 12)
    (lo := (2619349 / 62500000)) (hi := (8381917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 936480939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 936480939) = 1/(936480939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11080 : Bounds (-8381917 / 200000000) (-2619349 / 62500000) (Real.log (936480939 / 976562500)) := by
  have h := reflection_log_11080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11081_neg : (205434019 / 500000000) ≤ -Real.log (500000000000 / 754063164653) ∧
    -Real.log (500000000000 / 754063164653) ≤ (410868039 / 1000000000) := by
  have h := checkLog_sound (w := (254063164653 / 1254063164653)) (n := 12)
    (lo := (205434019 / 500000000)) (hi := (410868039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754063164653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754063164653 / 500000000000) = 1/(500000000000 / 754063164653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11081 : Bounds (205434019 / 500000000) (410868039 / 1000000000) (Real.log (754063164653 / 500000000000)) := by
  have h := reflection_log_11081_neg
  have he : Real.log (754063164653 / 500000000000) = -Real.log (500000000000 / 754063164653) := by
    rw [show ((754063164653 / 500000000000) : ℝ) = ((500000000000 / 754063164653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11082_neg : (206402971 / 500000000) ≤ -Real.log (250000000000 / 377762941647) ∧
    -Real.log (250000000000 / 377762941647) ≤ (412805943 / 1000000000) := by
  have h := checkLog_sound (w := (127762941647 / 627762941647)) (n := 12)
    (lo := (206402971 / 500000000)) (hi := (412805943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377762941647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377762941647 / 250000000000) = 1/(250000000000 / 377762941647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11082 : Bounds (206402971 / 500000000) (412805943 / 1000000000) (Real.log (377762941647 / 250000000000)) := by
  have h := reflection_log_11082_neg
  have he : Real.log (377762941647 / 250000000000) = -Real.log (250000000000 / 377762941647) := by
    rw [show ((377762941647 / 250000000000) : ℝ) = ((250000000000 / 377762941647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11083_neg : (208263151 / 250000000) ≤ -Real.log (500000000000 / 1150165016501) ∧
    -Real.log (500000000000 / 1150165016501) ≤ (416526303 / 500000000) := by
  have h := checkLog_sound (w := (150165016501 / 2150165016501)) (n := 12)
    (lo := (8744089 / 62500000)) (hi := (5596217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150165016501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1150165016501 / 1000000000000) = 1/(500000000000 / 1150165016501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11083 : Bounds (208263151 / 250000000) (416526303 / 500000000) (Real.log (1150165016501 / 500000000000)) := by
  have h := reflection_log_11083_neg
  have he : Real.log (1150165016501 / 500000000000) = -Real.log (500000000000 / 1150165016501) := by
    rw [show ((1150165016501 / 500000000000) : ℝ) = ((500000000000 / 1150165016501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11084_neg : (167084247 / 200000000) ≤ -Real.log (7812500000 / 18013946281) ∧
    -Real.log (7812500000 / 18013946281) ≤ (835421237 / 1000000000) := by
  have h := checkLog_sound (w := (2388946281 / 33638946281)) (n := 12)
    (lo := (28454811 / 200000000)) (hi := (17784257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18013946281 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(18013946281 / 15625000000) = 1/(7812500000 / 18013946281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11084 : Bounds (167084247 / 200000000) (835421237 / 1000000000) (Real.log (18013946281 / 7812500000)) := by
  have h := reflection_log_11084_neg
  have he : Real.log (18013946281 / 7812500000) = -Real.log (7812500000 / 18013946281) := by
    rw [show ((18013946281 / 7812500000) : ℝ) = ((7812500000 / 18013946281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11085_neg : (83402751 / 250000000) ≤ -Real.log (250 / 349) ∧
    -Real.log (250 / 349) ≤ (66722201 / 200000000) := by
  have h := checkLog_sound (w := (99 / 599)) (n := 12)
    (lo := (83402751 / 250000000)) (hi := (66722201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349 / 250) = 1/(250 / 349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11085 : Bounds (83402751 / 250000000) (66722201 / 200000000) (Real.log (349 / 250)) := by
  have h := reflection_log_11085_neg
  have he : Real.log (349 / 250) = -Real.log (250 / 349) := by
    rw [show ((349 / 250) : ℝ) = ((250 / 349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11086_neg : (504181081 / 1000000000) ≤ -Real.log (151 / 250) ∧
    -Real.log (151 / 250) ≤ (252090541 / 500000000) := by
  have h := checkLog_sound (w := (99 / 401)) (n := 12)
    (lo := (504181081 / 1000000000)) (hi := (252090541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 151) = 1/(151 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11086 : Bounds (-252090541 / 500000000) (-504181081 / 1000000000) (Real.log (151 / 250)) := by
  have h := reflection_log_11086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11087_neg : (395921 / 1000000000) ≤ -Real.log (250000 / 250099) ∧
    -Real.log (250000 / 250099) ≤ (197961 / 500000000) := by
  have h := checkLog_sound (w := (99 / 500099)) (n := 12)
    (lo := (395921 / 1000000000)) (hi := (197961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250099 / 250000) = 1/(250000 / 250099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11087 : Bounds (395921 / 1000000000) (197961 / 500000000) (Real.log (250099 / 250000)) := by
  have h := reflection_log_11087_neg
  have he : Real.log (250099 / 250000) = -Real.log (250000 / 250099) := by
    rw [show ((250099 / 250000) : ℝ) = ((250000 / 250099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11088_neg : (198039 / 500000000) ≤ -Real.log (249901 / 250000) ∧
    -Real.log (249901 / 250000) ≤ (396079 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 499901)) (n := 12)
    (lo := (198039 / 500000000)) (hi := (396079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249901) = 1/(249901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11088 : Bounds (-396079 / 1000000000) (-198039 / 500000000) (Real.log (249901 / 250000)) := by
  have h := reflection_log_11088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11089_neg : (23116539 / 125000000) ≤ -Real.log (1000000 / 1203137) ∧
    -Real.log (1000000 / 1203137) ≤ (184932313 / 1000000000) := by
  have h := checkLog_sound (w := (203137 / 2203137)) (n := 12)
    (lo := (23116539 / 125000000)) (hi := (184932313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203137 / 1000000) = 1/(1000000 / 1203137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11089 : Bounds (23116539 / 125000000) (184932313 / 1000000000) (Real.log (1203137 / 1000000)) := by
  have h := reflection_log_11089_neg
  have he : Real.log (1203137 / 1000000) = -Real.log (1000000 / 1203137) := by
    rw [show ((1203137 / 1000000) : ℝ) = ((1000000 / 1203137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11090_neg : (227072509 / 1000000000) ≤ -Real.log (796863 / 1000000) ∧
    -Real.log (796863 / 1000000) ≤ (22707251 / 100000000) := by
  have h := checkLog_sound (w := (203137 / 1796863)) (n := 12)
    (lo := (227072509 / 1000000000)) (hi := (22707251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796863) = 1/(796863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11090 : Bounds (-22707251 / 100000000) (-227072509 / 1000000000) (Real.log (796863 / 1000000)) := by
  have h := reflection_log_11090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11091_neg : (185704993 / 1000000000) ≤ -Real.log (1000000 / 1204067) ∧
    -Real.log (1000000 / 1204067) ≤ (92852497 / 500000000) := by
  have h := checkLog_sound (w := (204067 / 2204067)) (n := 12)
    (lo := (185704993 / 1000000000)) (hi := (92852497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204067 / 1000000) = 1/(1000000 / 1204067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11091 : Bounds (185704993 / 1000000000) (92852497 / 500000000) (Real.log (1204067 / 1000000)) := by
  have h := reflection_log_11091_neg
  have he : Real.log (1204067 / 1000000) = -Real.log (1000000 / 1204067) := by
    rw [show ((1204067 / 1000000) : ℝ) = ((1000000 / 1204067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11092_neg : (228240267 / 1000000000) ≤ -Real.log (795933 / 1000000) ∧
    -Real.log (795933 / 1000000) ≤ (57060067 / 250000000) := by
  have h := checkLog_sound (w := (204067 / 1795933)) (n := 12)
    (lo := (228240267 / 1000000000)) (hi := (57060067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795933) = 1/(795933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11092 : Bounds (-57060067 / 250000000) (-228240267 / 1000000000) (Real.log (795933 / 1000000)) := by
  have h := reflection_log_11092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11093_neg : (21267637 / 500000000) ≤ -Real.log (958356659511 / 1000000000000) ∧
    -Real.log (958356659511 / 1000000000000) ≤ (1701411 / 40000000) := by
  have h := checkLog_sound (w := (41643340489 / 1958356659511)) (n := 12)
    (lo := (21267637 / 500000000)) (hi := (1701411 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958356659511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958356659511) = 1/(958356659511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11093 : Bounds (-1701411 / 40000000) (-21267637 / 500000000) (Real.log (958356659511 / 1000000000000)) := by
  have h := reflection_log_11093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11094_neg : (42140197 / 1000000000) ≤ -Real.log (958735359231 / 1000000000000) ∧
    -Real.log (958735359231 / 1000000000000) ≤ (21070099 / 500000000) := by
  have h := checkLog_sound (w := (41264640769 / 1958735359231)) (n := 12)
    (lo := (42140197 / 1000000000)) (hi := (21070099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958735359231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958735359231) = 1/(958735359231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11094 : Bounds (-21070099 / 500000000) (-42140197 / 1000000000) (Real.log (958735359231 / 1000000000000)) := by
  have h := reflection_log_11094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11095_neg : (206002411 / 500000000) ≤ -Real.log (31250000000 / 47182553651) ∧
    -Real.log (31250000000 / 47182553651) ≤ (412004823 / 1000000000) := by
  have h := checkLog_sound (w := (15932553651 / 78432553651)) (n := 12)
    (lo := (206002411 / 500000000)) (hi := (412004823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47182553651 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47182553651 / 31250000000) = 1/(31250000000 / 47182553651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11095 : Bounds (206002411 / 500000000) (412004823 / 1000000000) (Real.log (47182553651 / 31250000000)) := by
  have h := reflection_log_11095_neg
  have he : Real.log (47182553651 / 31250000000) = -Real.log (31250000000 / 47182553651) := by
    rw [show ((47182553651 / 31250000000) : ℝ) = ((31250000000 / 47182553651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11096_neg : (20697263 / 50000000) ≤ -Real.log (62500000000 / 94548394777) ∧
    -Real.log (62500000000 / 94548394777) ≤ (413945261 / 1000000000) := by
  have h := checkLog_sound (w := (32048394777 / 157048394777)) (n := 12)
    (lo := (20697263 / 50000000)) (hi := (413945261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94548394777 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94548394777 / 62500000000) = 1/(62500000000 / 94548394777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11096 : Bounds (20697263 / 50000000) (413945261 / 1000000000) (Real.log (94548394777 / 62500000000)) := by
  have h := reflection_log_11096_neg
  have he : Real.log (94548394777 / 62500000000) = -Real.log (62500000000 / 94548394777) := by
    rw [show ((94548394777 / 62500000000) : ℝ) = ((62500000000 / 94548394777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11097_neg : (167084247 / 200000000) ≤ -Real.log (500000000000 / 1152892561983) ∧
    -Real.log (500000000000 / 1152892561983) ≤ (835421237 / 1000000000) := by
  have h := checkLog_sound (w := (152892561983 / 2152892561983)) (n := 12)
    (lo := (28454811 / 200000000)) (hi := (17784257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152892561983 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1152892561983 / 1000000000000) = 1/(500000000000 / 1152892561983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11097 : Bounds (167084247 / 200000000) (835421237 / 1000000000) (Real.log (1152892561983 / 500000000000)) := by
  have h := reflection_log_11097_neg
  have he : Real.log (1152892561983 / 500000000000) = -Real.log (500000000000 / 1152892561983) := by
    rw [show ((1152892561983 / 500000000000) : ℝ) = ((500000000000 / 1152892561983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11098_neg : (209448021 / 250000000) ≤ -Real.log (500000000000 / 1155629139073) ∧
    -Real.log (500000000000 / 1155629139073) ≤ (418896043 / 500000000) := by
  have h := checkLog_sound (w := (155629139073 / 2155629139073)) (n := 12)
    (lo := (18080613 / 125000000)) (hi := (28928981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155629139073 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1155629139073 / 1000000000000) = 1/(500000000000 / 1155629139073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11098 : Bounds (209448021 / 250000000) (418896043 / 500000000) (Real.log (1155629139073 / 500000000000)) := by
  have h := reflection_log_11098_neg
  have he : Real.log (1155629139073 / 500000000000) = -Real.log (500000000000 / 1155629139073) := by
    rw [show ((1155629139073 / 500000000000) : ℝ) = ((500000000000 / 1155629139073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11099_neg : (8358177 / 25000000) ≤ -Real.log (1000 / 1397) ∧
    -Real.log (1000 / 1397) ≤ (334327081 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2397)) (n := 12)
    (lo := (8358177 / 25000000)) (hi := (334327081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 1000) = 1/(1000 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11099 : Bounds (8358177 / 25000000) (334327081 / 1000000000) (Real.log (1397 / 1000)) := by
  have h := reflection_log_11099_neg
  have he : Real.log (1397 / 1000) = -Real.log (1000 / 1397) := by
    rw [show ((1397 / 1000) : ℝ) = ((1000 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11100_neg : (252919041 / 500000000) ≤ -Real.log (603 / 1000) ∧
    -Real.log (603 / 1000) ≤ (505838083 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 1603)) (n := 12)
    (lo := (252919041 / 500000000)) (hi := (505838083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 603) = 1/(603 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11100 : Bounds (-505838083 / 1000000000) (-252919041 / 500000000) (Real.log (603 / 1000)) := by
  have h := reflection_log_11100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11101_neg : (396921 / 1000000000) ≤ -Real.log (1000000 / 1000397) ∧
    -Real.log (1000000 / 1000397) ≤ (198461 / 500000000) := by
  have h := checkLog_sound (w := (397 / 2000397)) (n := 12)
    (lo := (396921 / 1000000000)) (hi := (198461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000397 / 1000000) = 1/(1000000 / 1000397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11101 : Bounds (396921 / 1000000000) (198461 / 500000000) (Real.log (1000397 / 1000000)) := by
  have h := reflection_log_11101_neg
  have he : Real.log (1000397 / 1000000) = -Real.log (1000000 / 1000397) := by
    rw [show ((1000397 / 1000000) : ℝ) = ((1000000 / 1000397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11102_neg : (198539 / 500000000) ≤ -Real.log (999603 / 1000000) ∧
    -Real.log (999603 / 1000000) ≤ (397079 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 1999603)) (n := 12)
    (lo := (198539 / 500000000)) (hi := (397079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999603) = 1/(999603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11102 : Bounds (-397079 / 1000000000) (-198539 / 500000000) (Real.log (999603 / 1000000)) := by
  have h := reflection_log_11102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11103_neg : (23173149 / 125000000) ≤ -Real.log (500000 / 601841) ∧
    -Real.log (500000 / 601841) ≤ (185385193 / 1000000000) := by
  have h := checkLog_sound (w := (101841 / 1101841)) (n := 12)
    (lo := (23173149 / 125000000)) (hi := (185385193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601841 / 500000) = 1/(500000 / 601841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11103 : Bounds (23173149 / 125000000) (185385193 / 1000000000) (Real.log (601841 / 500000)) := by
  have h := reflection_log_11103_neg
  have he : Real.log (601841 / 500000) = -Real.log (500000 / 601841) := by
    rw [show ((601841 / 500000) : ℝ) = ((500000 / 601841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11104_neg : (9110267 / 40000000) ≤ -Real.log (398159 / 500000) ∧
    -Real.log (398159 / 500000) ≤ (56939169 / 250000000) := by
  have h := checkLog_sound (w := (101841 / 898159)) (n := 12)
    (lo := (9110267 / 40000000)) (hi := (56939169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 398159) = 1/(398159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11104 : Bounds (-56939169 / 250000000) (-9110267 / 40000000) (Real.log (398159 / 500000)) := by
  have h := reflection_log_11104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11105_neg : (186159183 / 1000000000) ≤ -Real.log (500000 / 602307) ∧
    -Real.log (500000 / 602307) ≤ (11634949 / 62500000) := by
  have h := checkLog_sound (w := (102307 / 1102307)) (n := 12)
    (lo := (186159183 / 1000000000)) (hi := (11634949 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602307 / 500000) = 1/(500000 / 602307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11105 : Bounds (186159183 / 1000000000) (11634949 / 62500000) (Real.log (602307 / 500000)) := by
  have h := reflection_log_11105_neg
  have he : Real.log (602307 / 500000) = -Real.log (500000 / 602307) := by
    rw [show ((602307 / 500000) : ℝ) = ((500000 / 602307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11106_neg : (228927747 / 1000000000) ≤ -Real.log (397693 / 500000) ∧
    -Real.log (397693 / 500000) ≤ (57231937 / 250000000) := by
  have h := checkLog_sound (w := (102307 / 897693)) (n := 12)
    (lo := (228927747 / 1000000000)) (hi := (57231937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397693) = 1/(397693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11106 : Bounds (-57231937 / 250000000) (-228927747 / 1000000000) (Real.log (397693 / 500000)) := by
  have h := reflection_log_11106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11107_neg : (42768563 / 1000000000) ≤ -Real.log (239533277751 / 250000000000) ∧
    -Real.log (239533277751 / 250000000000) ≤ (10692141 / 250000000) := by
  have h := checkLog_sound (w := (10466722249 / 489533277751)) (n := 12)
    (lo := (42768563 / 1000000000)) (hi := (10692141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239533277751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239533277751) = 1/(239533277751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11107 : Bounds (-10692141 / 250000000) (-42768563 / 1000000000) (Real.log (239533277751 / 250000000000)) := by
  have h := reflection_log_11107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11108_neg : (42371483 / 1000000000) ≤ -Real.log (239628410719 / 250000000000) ∧
    -Real.log (239628410719 / 250000000000) ≤ (10592871 / 250000000) := by
  have h := checkLog_sound (w := (10371589281 / 489628410719)) (n := 12)
    (lo := (42371483 / 1000000000)) (hi := (10592871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239628410719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239628410719) = 1/(239628410719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11108 : Bounds (-10592871 / 250000000) (-42371483 / 1000000000) (Real.log (239628410719 / 250000000000)) := by
  have h := reflection_log_11108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11109_neg : (413141867 / 1000000000) ≤ -Real.log (500000000000 / 755779726189) ∧
    -Real.log (500000000000 / 755779726189) ≤ (103285467 / 250000000) := by
  have h := checkLog_sound (w := (255779726189 / 1255779726189)) (n := 12)
    (lo := (413141867 / 1000000000)) (hi := (103285467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755779726189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755779726189 / 500000000000) = 1/(500000000000 / 755779726189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11109 : Bounds (413141867 / 1000000000) (103285467 / 250000000) (Real.log (755779726189 / 500000000000)) := by
  have h := reflection_log_11109_neg
  have he : Real.log (755779726189 / 500000000000) = -Real.log (500000000000 / 755779726189) := by
    rw [show ((755779726189 / 500000000000) : ℝ) = ((500000000000 / 755779726189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11110_neg : (415086931 / 1000000000) ≤ -Real.log (20000000000 / 30290047851) ∧
    -Real.log (20000000000 / 30290047851) ≤ (103771733 / 250000000) := by
  have h := checkLog_sound (w := (10290047851 / 50290047851)) (n := 12)
    (lo := (415086931 / 1000000000)) (hi := (103771733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30290047851 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30290047851 / 20000000000) = 1/(20000000000 / 30290047851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11110 : Bounds (415086931 / 1000000000) (103771733 / 250000000) (Real.log (30290047851 / 20000000000)) := by
  have h := reflection_log_11110_neg
  have he : Real.log (30290047851 / 20000000000) = -Real.log (20000000000 / 30290047851) := by
    rw [show ((30290047851 / 20000000000) : ℝ) = ((20000000000 / 30290047851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11111_neg : (209448021 / 250000000) ≤ -Real.log (3906250000 / 9028352649) ∧
    -Real.log (3906250000 / 9028352649) ≤ (418896043 / 500000000) := by
  have h := checkLog_sound (w := (1215852649 / 16840852649)) (n := 12)
    (lo := (18080613 / 125000000)) (hi := (28928981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9028352649 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9028352649 / 7812500000) = 1/(3906250000 / 9028352649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11111 : Bounds (209448021 / 250000000) (418896043 / 500000000) (Real.log (9028352649 / 3906250000)) := by
  have h := reflection_log_11111_neg
  have he : Real.log (9028352649 / 3906250000) = -Real.log (3906250000 / 9028352649) := by
    rw [show ((9028352649 / 3906250000) : ℝ) = ((3906250000 / 9028352649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11112_neg : (840165161 / 1000000000) ≤ -Real.log (976562500 / 2262450767) ∧
    -Real.log (976562500 / 2262450767) ≤ (840165163 / 1000000000) := by
  have h := checkLog_sound (w := (309325767 / 4215575767)) (n := 12)
    (lo := (147017981 / 1000000000)) (hi := (73508991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2262450767 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2262450767 / 1953125000) = 1/(976562500 / 2262450767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11112 : Bounds (840165161 / 1000000000) (840165163 / 1000000000) (Real.log (2262450767 / 976562500)) := by
  have h := reflection_log_11112_neg
  have he : Real.log (2262450767 / 976562500) = -Real.log (976562500 / 2262450767) := by
    rw [show ((2262450767 / 976562500) : ℝ) = ((976562500 / 2262450767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11113_neg : (335042643 / 1000000000) ≤ -Real.log (500 / 699) ∧
    -Real.log (500 / 699) ≤ (83760661 / 250000000) := by
  have h := checkLog_sound (w := (199 / 1199)) (n := 12)
    (lo := (335042643 / 1000000000)) (hi := (83760661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 500) = 1/(500 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11113 : Bounds (335042643 / 1000000000) (83760661 / 250000000) (Real.log (699 / 500)) := by
  have h := reflection_log_11113_neg
  have he : Real.log (699 / 500) = -Real.log (500 / 699) := by
    rw [show ((699 / 500) : ℝ) = ((500 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11114_neg : (507497833 / 1000000000) ≤ -Real.log (301 / 500) ∧
    -Real.log (301 / 500) ≤ (253748917 / 500000000) := by
  have h := checkLog_sound (w := (199 / 801)) (n := 12)
    (lo := (507497833 / 1000000000)) (hi := (253748917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 301) = 1/(301 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11114 : Bounds (-253748917 / 500000000) (-507497833 / 1000000000) (Real.log (301 / 500)) := by
  have h := reflection_log_11114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11115_neg : (2487 / 6250000) ≤ -Real.log (500000 / 500199) ∧
    -Real.log (500000 / 500199) ≤ (397921 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1000199)) (n := 12)
    (lo := (2487 / 6250000)) (hi := (397921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500199 / 500000) = 1/(500000 / 500199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11115 : Bounds (2487 / 6250000) (397921 / 1000000000) (Real.log (500199 / 500000)) := by
  have h := reflection_log_11115_neg
  have he : Real.log (500199 / 500000) = -Real.log (500000 / 500199) := by
    rw [show ((500199 / 500000) : ℝ) = ((500000 / 500199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11116_neg : (398079 / 1000000000) ≤ -Real.log (499801 / 500000) ∧
    -Real.log (499801 / 500000) ≤ (311 / 781250) := by
  have h := checkLog_sound (w := (199 / 999801)) (n := 12)
    (lo := (398079 / 1000000000)) (hi := (311 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499801) = 1/(499801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11116 : Bounds (-311 / 781250) (-398079 / 1000000000) (Real.log (499801 / 500000)) := by
  have h := reflection_log_11116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11117_neg : (185838697 / 1000000000) ≤ -Real.log (250000 / 301057) ∧
    -Real.log (250000 / 301057) ≤ (92919349 / 500000000) := by
  have h := checkLog_sound (w := (51057 / 551057)) (n := 12)
    (lo := (185838697 / 1000000000)) (hi := (92919349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301057 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301057 / 250000) = 1/(250000 / 301057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11117 : Bounds (185838697 / 1000000000) (92919349 / 500000000) (Real.log (301057 / 250000)) := by
  have h := reflection_log_11117_neg
  have he : Real.log (301057 / 250000) = -Real.log (250000 / 301057) := by
    rw [show ((301057 / 250000) : ℝ) = ((250000 / 301057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11118_neg : (114221283 / 500000000) ≤ -Real.log (198943 / 250000) ∧
    -Real.log (198943 / 250000) ≤ (228442567 / 1000000000) := by
  have h := checkLog_sound (w := (51057 / 448943)) (n := 12)
    (lo := (114221283 / 500000000)) (hi := (228442567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198943) = 1/(198943 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11118 : Bounds (-228442567 / 1000000000) (-114221283 / 500000000) (Real.log (198943 / 250000)) := by
  have h := reflection_log_11118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11119_neg : (93306169 / 500000000) ≤ -Real.log (25000 / 30129) ∧
    -Real.log (25000 / 30129) ≤ (186612339 / 1000000000) := by
  have h := checkLog_sound (w := (5129 / 55129)) (n := 12)
    (lo := (93306169 / 500000000)) (hi := (186612339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30129 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30129 / 25000) = 1/(25000 / 30129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11119 : Bounds (93306169 / 500000000) (186612339 / 1000000000) (Real.log (30129 / 25000)) := by
  have h := reflection_log_11119_neg
  have he : Real.log (30129 / 25000) = -Real.log (25000 / 30129) := by
    rw [show ((30129 / 25000) : ℝ) = ((25000 / 30129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11120_neg : (114807221 / 500000000) ≤ -Real.log (19871 / 25000) ∧
    -Real.log (19871 / 25000) ≤ (229614443 / 1000000000) := by
  have h := checkLog_sound (w := (5129 / 44871)) (n := 12)
    (lo := (114807221 / 500000000)) (hi := (229614443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19871) = 1/(19871 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11120 : Bounds (-229614443 / 1000000000) (-114807221 / 500000000) (Real.log (19871 / 25000)) := by
  have h := reflection_log_11120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11121_neg : (5375263 / 125000000) ≤ -Real.log (598693359 / 625000000) ∧
    -Real.log (598693359 / 625000000) ≤ (8600421 / 200000000) := by
  have h := checkLog_sound (w := (26306641 / 1223693359)) (n := 12)
    (lo := (5375263 / 125000000)) (hi := (8600421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 598693359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 598693359) = 1/(598693359 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11121 : Bounds (-8600421 / 200000000) (-5375263 / 125000000) (Real.log (598693359 / 625000000)) := by
  have h := reflection_log_11121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11122_neg : (10650967 / 250000000) ≤ -Real.log (59893182751 / 62500000000) ∧
    -Real.log (59893182751 / 62500000000) ≤ (42603869 / 1000000000) := by
  have h := checkLog_sound (w := (2606817249 / 122393182751)) (n := 12)
    (lo := (10650967 / 250000000)) (hi := (42603869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59893182751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59893182751) = 1/(59893182751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11122 : Bounds (-42603869 / 1000000000) (-10650967 / 250000000) (Real.log (59893182751 / 62500000000)) := by
  have h := reflection_log_11122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11123_neg : (25892579 / 62500000) ≤ -Real.log (125000000000 / 189160337383) ∧
    -Real.log (125000000000 / 189160337383) ≤ (82856253 / 200000000) := by
  have h := checkLog_sound (w := (64160337383 / 314160337383)) (n := 12)
    (lo := (25892579 / 62500000)) (hi := (82856253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189160337383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189160337383 / 125000000000) = 1/(125000000000 / 189160337383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11123 : Bounds (25892579 / 62500000) (82856253 / 200000000) (Real.log (189160337383 / 125000000000)) := by
  have h := reflection_log_11123_neg
  have he : Real.log (189160337383 / 125000000000) = -Real.log (125000000000 / 189160337383) := by
    rw [show ((189160337383 / 125000000000) : ℝ) = ((125000000000 / 189160337383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11124_neg : (20811339 / 50000000) ≤ -Real.log (500000000000 / 758114840723) ∧
    -Real.log (500000000000 / 758114840723) ≤ (416226781 / 1000000000) := by
  have h := checkLog_sound (w := (258114840723 / 1258114840723)) (n := 12)
    (lo := (20811339 / 50000000)) (hi := (416226781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758114840723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758114840723 / 500000000000) = 1/(500000000000 / 758114840723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11124 : Bounds (20811339 / 50000000) (416226781 / 1000000000) (Real.log (758114840723 / 500000000000)) := by
  have h := reflection_log_11124_neg
  have he : Real.log (758114840723 / 500000000000) = -Real.log (500000000000 / 758114840723) := by
    rw [show ((758114840723 / 500000000000) : ℝ) = ((500000000000 / 758114840723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11125_neg : (840165161 / 1000000000) ≤ -Real.log (500000000000 / 1158374792703) ∧
    -Real.log (500000000000 / 1158374792703) ≤ (840165163 / 1000000000) := by
  have h := checkLog_sound (w := (158374792703 / 2158374792703)) (n := 12)
    (lo := (147017981 / 1000000000)) (hi := (73508991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158374792703 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158374792703 / 1000000000000) = 1/(500000000000 / 1158374792703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11125 : Bounds (840165161 / 1000000000) (840165163 / 1000000000) (Real.log (1158374792703 / 500000000000)) := by
  have h := reflection_log_11125_neg
  have he : Real.log (1158374792703 / 500000000000) = -Real.log (500000000000 / 1158374792703) := by
    rw [show ((1158374792703 / 500000000000) : ℝ) = ((500000000000 / 1158374792703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11126_neg : (210635119 / 250000000) ≤ -Real.log (500000000000 / 1161129568107) ∧
    -Real.log (500000000000 / 1161129568107) ≤ (421270239 / 500000000) := by
  have h := checkLog_sound (w := (161129568107 / 2161129568107)) (n := 12)
    (lo := (9337081 / 62500000)) (hi := (149393297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161129568107 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161129568107 / 1000000000000) = 1/(500000000000 / 1161129568107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11126 : Bounds (210635119 / 250000000) (421270239 / 500000000) (Real.log (1161129568107 / 500000000000)) := by
  have h := reflection_log_11126_neg
  have he : Real.log (1161129568107 / 500000000000) = -Real.log (500000000000 / 1161129568107) := by
    rw [show ((1161129568107 / 500000000000) : ℝ) = ((500000000000 / 1161129568107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11127_neg : (67151539 / 200000000) ≤ -Real.log (1000 / 1399) ∧
    -Real.log (1000 / 1399) ≤ (2623107 / 7812500) := by
  have h := checkLog_sound (w := (399 / 2399)) (n := 12)
    (lo := (67151539 / 200000000)) (hi := (2623107 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1399 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1399 / 1000) = 1/(1000 / 1399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11127 : Bounds (67151539 / 200000000) (2623107 / 7812500) (Real.log (1399 / 1000)) := by
  have h := reflection_log_11127_neg
  have he : Real.log (1399 / 1000) = -Real.log (1000 / 1399) := by
    rw [show ((1399 / 1000) : ℝ) = ((1000 / 1399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11128_neg : (63645043 / 125000000) ≤ -Real.log (601 / 1000) ∧
    -Real.log (601 / 1000) ≤ (101832069 / 200000000) := by
  have h := checkLog_sound (w := (399 / 1601)) (n := 12)
    (lo := (63645043 / 125000000)) (hi := (101832069 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 601) = 1/(601 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11128 : Bounds (-101832069 / 200000000) (-63645043 / 125000000) (Real.log (601 / 1000)) := by
  have h := reflection_log_11128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11129_neg : (9973 / 25000000) ≤ -Real.log (1000000 / 1000399) ∧
    -Real.log (1000000 / 1000399) ≤ (398921 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 2000399)) (n := 12)
    (lo := (9973 / 25000000)) (hi := (398921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000399 / 1000000) = 1/(1000000 / 1000399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11129 : Bounds (9973 / 25000000) (398921 / 1000000000) (Real.log (1000399 / 1000000)) := by
  have h := reflection_log_11129_neg
  have he : Real.log (1000399 / 1000000) = -Real.log (1000000 / 1000399) := by
    rw [show ((1000399 / 1000000) : ℝ) = ((1000000 / 1000399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11130_neg : (399079 / 1000000000) ≤ -Real.log (999601 / 1000000) ∧
    -Real.log (999601 / 1000000) ≤ (9977 / 25000000) := by
  have h := checkLog_sound (w := (399 / 1999601)) (n := 12)
    (lo := (399079 / 1000000000)) (hi := (9977 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999601) = 1/(999601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11130 : Bounds (-9977 / 25000000) (-399079 / 1000000000) (Real.log (999601 / 1000000)) := by
  have h := reflection_log_11130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11131_neg : (186291997 / 1000000000) ≤ -Real.log (500000 / 602387) ∧
    -Real.log (500000 / 602387) ≤ (93145999 / 500000000) := by
  have h := checkLog_sound (w := (102387 / 1102387)) (n := 12)
    (lo := (186291997 / 1000000000)) (hi := (93145999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602387 / 500000) = 1/(500000 / 602387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11131 : Bounds (186291997 / 1000000000) (93145999 / 500000000) (Real.log (602387 / 500000)) := by
  have h := reflection_log_11131_neg
  have he : Real.log (602387 / 500000) = -Real.log (500000 / 602387) := by
    rw [show ((602387 / 500000) : ℝ) = ((500000 / 602387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11132_neg : (229128927 / 1000000000) ≤ -Real.log (397613 / 500000) ∧
    -Real.log (397613 / 500000) ≤ (7160279 / 31250000) := by
  have h := checkLog_sound (w := (102387 / 897613)) (n := 12)
    (lo := (229128927 / 1000000000)) (hi := (7160279 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397613) = 1/(397613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11132 : Bounds (-7160279 / 31250000) (-229128927 / 1000000000) (Real.log (397613 / 500000)) := by
  have h := reflection_log_11132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11133_neg : (93533473 / 500000000) ≤ -Real.log (250000 / 301427) ∧
    -Real.log (250000 / 301427) ≤ (187066947 / 1000000000) := by
  have h := checkLog_sound (w := (51427 / 551427)) (n := 12)
    (lo := (93533473 / 500000000)) (hi := (187066947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301427 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301427 / 250000) = 1/(250000 / 301427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11133 : Bounds (93533473 / 500000000) (187066947 / 1000000000) (Real.log (301427 / 250000)) := by
  have h := reflection_log_11133_neg
  have he : Real.log (301427 / 250000) = -Real.log (250000 / 301427) := by
    rw [show ((301427 / 250000) : ℝ) = ((250000 / 301427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11134_neg : (230304127 / 1000000000) ≤ -Real.log (198573 / 250000) ∧
    -Real.log (198573 / 250000) ≤ (1799251 / 7812500) := by
  have h := checkLog_sound (w := (51427 / 448573)) (n := 12)
    (lo := (230304127 / 1000000000)) (hi := (1799251 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198573) = 1/(198573 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11134 : Bounds (-1799251 / 7812500) (-230304127 / 1000000000) (Real.log (198573 / 250000)) := by
  have h := reflection_log_11134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11135_neg : (2161859 / 50000000) ≤ -Real.log (59855263671 / 62500000000) ∧
    -Real.log (59855263671 / 62500000000) ≤ (43237181 / 1000000000) := by
  have h := checkLog_sound (w := (2644736329 / 122355263671)) (n := 12)
    (lo := (2161859 / 50000000)) (hi := (43237181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59855263671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59855263671) = 1/(59855263671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11135 : Bounds (-43237181 / 1000000000) (-2161859 / 50000000) (Real.log (59855263671 / 62500000000)) := by
  have h := reflection_log_11135_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
