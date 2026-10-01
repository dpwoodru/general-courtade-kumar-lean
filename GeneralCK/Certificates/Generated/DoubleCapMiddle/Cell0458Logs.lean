import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0458
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

theorem reflection_log_1_neg : (186220197 / 1000000000) ≤ -Real.log (640 / 771) ∧
    -Real.log (640 / 771) ≤ (93110099 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1411)) (n := 12)
    (lo := (186220197 / 1000000000)) (hi := (93110099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 640) = 1/(640 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (186220197 / 1000000000) (93110099 / 500000000) (Real.log (771 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (771 / 640) = -Real.log (640 / 771) := by
    rw [show ((771 / 640) : ℝ) = ((640 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (229020159 / 1000000000) ≤ -Real.log (509 / 640) ∧
    -Real.log (509 / 640) ≤ (89461 / 390625) := by
  have h := checkLog_sound (w := (131 / 1149)) (n := 12)
    (lo := (229020159 / 1000000000)) (hi := (89461 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 509) = 1/(509 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-89461 / 390625) (-229020159 / 1000000000) (Real.log (509 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11623561 / 62500000) ≤ -Real.log (10240 / 12333) ∧
    -Real.log (10240 / 12333) ≤ (185976977 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 22573)) (n := 12)
    (lo := (11623561 / 62500000)) (hi := (185976977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12333 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12333 / 10240) = 1/(10240 / 12333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11623561 / 62500000) (185976977 / 1000000000) (Real.log (12333 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12333 / 10240) = -Real.log (10240 / 12333) := by
    rw [show ((12333 / 10240) : ℝ) = ((10240 / 12333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (114325929 / 500000000) ≤ -Real.log (8147 / 10240) ∧
    -Real.log (8147 / 10240) ≤ (228651859 / 1000000000) := by
  have h := checkLog_sound (w := (2093 / 18387)) (n := 12)
    (lo := (114325929 / 500000000)) (hi := (228651859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8147) = 1/(8147 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-228651859 / 1000000000) (-114325929 / 500000000) (Real.log (8147 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343146343 / 1000000000) ≤ -Real.log (320 / 451) ∧
    -Real.log (320 / 451) ≤ (42893293 / 125000000) := by
  have h := checkLog_sound (w := (131 / 771)) (n := 12)
    (lo := (343146343 / 1000000000)) (hi := (42893293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451 / 320) = 1/(320 / 451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343146343 / 1000000000) (42893293 / 125000000) (Real.log (451 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (451 / 320) = -Real.log (320 / 451) := by
    rw [show ((451 / 320) : ℝ) = ((320 / 451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (26328699 / 50000000) ≤ -Real.log (189 / 320) ∧
    -Real.log (189 / 320) ≤ (526573981 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 189) = 1/(189 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-526573981 / 1000000000) (-26328699 / 50000000) (Real.log (189 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171365257 / 500000000) ≤ -Real.log (5120 / 7213) ∧
    -Real.log (5120 / 7213) ≤ (68546103 / 200000000) := by
  have h := checkLog_sound (w := (2093 / 12333)) (n := 12)
    (lo := (171365257 / 500000000)) (hi := (68546103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7213 / 5120) = 1/(5120 / 7213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171365257 / 500000000) (68546103 / 200000000) (Real.log (7213 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7213 / 5120) = -Real.log (5120 / 7213) := by
    rw [show ((7213 / 5120) : ℝ) = ((5120 / 7213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (525582409 / 1000000000) ≤ -Real.log (3027 / 5120) ∧
    -Real.log (3027 / 5120) ≤ (52558241 / 100000000) := by
  have h := checkLog_sound (w := (2093 / 8147)) (n := 12)
    (lo := (525582409 / 1000000000)) (hi := (52558241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3027) = 1/(3027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52558241 / 100000000) (-525582409 / 1000000000) (Real.log (3027 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (255589831 / 1000000000) ≤ -Real.log (1000000 / 1291223) ∧
    -Real.log (1000000 / 1291223) ≤ (31948729 / 125000000) := by
  have h := checkLog_sound (w := (291223 / 2291223)) (n := 12)
    (lo := (255589831 / 1000000000)) (hi := (31948729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291223 / 1000000) = 1/(1000000 / 1291223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (255589831 / 1000000000) (31948729 / 125000000) (Real.log (1291223 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1291223 / 1000000) = -Real.log (1000000 / 1291223) := by
    rw [show ((1291223 / 1000000) : ℝ) = ((1000000 / 1291223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344214329 / 1000000000) ≤ -Real.log (708777 / 1000000) ∧
    -Real.log (708777 / 1000000) ≤ (34421433 / 100000000) := by
  have h := checkLog_sound (w := (291223 / 1708777)) (n := 12)
    (lo := (344214329 / 1000000000)) (hi := (34421433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708777) = 1/(708777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34421433 / 100000000) (-344214329 / 1000000000) (Real.log (708777 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127959461 / 500000000) ≤ -Real.log (15625 / 20182) ∧
    -Real.log (15625 / 20182) ≤ (255918923 / 1000000000) := by
  have h := checkLog_sound (w := (4557 / 35807)) (n := 12)
    (lo := (127959461 / 500000000)) (hi := (255918923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20182 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20182 / 15625) = 1/(15625 / 20182) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127959461 / 500000000) (255918923 / 1000000000) (Real.log (20182 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20182 / 15625) = -Real.log (15625 / 20182) := by
    rw [show ((20182 / 15625) : ℝ) = ((15625 / 20182) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (344814133 / 1000000000) ≤ -Real.log (11068 / 15625) ∧
    -Real.log (11068 / 15625) ≤ (172407067 / 500000000) := by
  have h := checkLog_sound (w := (4557 / 26693)) (n := 12)
    (lo := (344814133 / 1000000000)) (hi := (172407067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11068) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11068) = 1/(11068 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-172407067 / 500000000) (-344814133 / 1000000000) (Real.log (11068 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47836429 / 250000000) ≤ -Real.log (500000 / 605439) ∧
    -Real.log (500000 / 605439) ≤ (191345717 / 1000000000) := by
  have h := checkLog_sound (w := (105439 / 1105439)) (n := 12)
    (lo := (47836429 / 250000000)) (hi := (191345717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605439 / 500000) = 1/(500000 / 605439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47836429 / 250000000) (191345717 / 1000000000) (Real.log (605439 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605439 / 500000) = -Real.log (500000 / 605439) := by
    rw [show ((605439 / 500000) : ℝ) = ((500000 / 605439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (236834343 / 1000000000) ≤ -Real.log (394561 / 500000) ∧
    -Real.log (394561 / 500000) ≤ (29604293 / 125000000) := by
  have h := checkLog_sound (w := (105439 / 894561)) (n := 12)
    (lo := (236834343 / 1000000000)) (hi := (29604293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394561) = 1/(394561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29604293 / 125000000) (-236834343 / 1000000000) (Real.log (394561 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (191612429 / 1000000000) ≤ -Real.log (1000000 / 1211201) ∧
    -Real.log (1000000 / 1211201) ≤ (19161243 / 100000000) := by
  have h := checkLog_sound (w := (211201 / 2211201)) (n := 12)
    (lo := (191612429 / 1000000000)) (hi := (19161243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211201 / 1000000) = 1/(1000000 / 1211201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (191612429 / 1000000000) (19161243 / 100000000) (Real.log (1211201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1211201 / 1000000) = -Real.log (1000000 / 1211201) := by
    rw [show ((1211201 / 1000000) : ℝ) = ((1000000 / 1211201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (237243743 / 1000000000) ≤ -Real.log (788799 / 1000000) ∧
    -Real.log (788799 / 1000000) ≤ (7413867 / 31250000) := by
  have h := checkLog_sound (w := (211201 / 1788799)) (n := 12)
    (lo := (237243743 / 1000000000)) (hi := (7413867 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788799) = 1/(788799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-7413867 / 31250000) (-237243743 / 1000000000) (Real.log (788799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (468597 / 781250) ≤ -Real.log (25000000000 / 45544049821) ∧
    -Real.log (25000000000 / 45544049821) ≤ (599804161 / 1000000000) := by
  have h := checkLog_sound (w := (20544049821 / 70544049821)) (n := 12)
    (lo := (468597 / 781250)) (hi := (599804161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45544049821 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45544049821 / 25000000000) = 1/(25000000000 / 45544049821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (468597 / 781250) (599804161 / 1000000000) (Real.log (45544049821 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45544049821 / 25000000000) = -Real.log (25000000000 / 45544049821) := by
    rw [show ((45544049821 / 25000000000) : ℝ) = ((25000000000 / 45544049821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4693227 / 7812500) ≤ -Real.log (500000000000 / 911727502711) ∧
    -Real.log (500000000000 / 911727502711) ≤ (600733057 / 1000000000) := by
  have h := checkLog_sound (w := (411727502711 / 1411727502711)) (n := 12)
    (lo := (4693227 / 7812500)) (hi := (600733057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911727502711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911727502711 / 500000000000) = 1/(500000000000 / 911727502711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4693227 / 7812500) (600733057 / 1000000000) (Real.log (911727502711 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (911727502711 / 500000000000) = -Real.log (500000000000 / 911727502711) := by
    rw [show ((911727502711 / 500000000000) : ℝ) = ((500000000000 / 911727502711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21409003 / 50000000) ≤ -Real.log (250000000000 / 383615587957) ∧
    -Real.log (250000000000 / 383615587957) ≤ (428180061 / 1000000000) := by
  have h := checkLog_sound (w := (133615587957 / 633615587957)) (n := 12)
    (lo := (21409003 / 50000000)) (hi := (428180061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383615587957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383615587957 / 250000000000) = 1/(250000000000 / 383615587957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (21409003 / 50000000) (428180061 / 1000000000) (Real.log (383615587957 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383615587957 / 250000000000) = -Real.log (250000000000 / 383615587957) := by
    rw [show ((383615587957 / 250000000000) : ℝ) = ((250000000000 / 383615587957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (107214043 / 250000000) ≤ -Real.log (500000000000 / 767750085891) ∧
    -Real.log (500000000000 / 767750085891) ≤ (428856173 / 1000000000) := by
  have h := checkLog_sound (w := (267750085891 / 1267750085891)) (n := 12)
    (lo := (107214043 / 250000000)) (hi := (428856173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767750085891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767750085891 / 500000000000) = 1/(500000000000 / 767750085891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (107214043 / 250000000) (428856173 / 1000000000) (Real.log (767750085891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (767750085891 / 500000000000) = -Real.log (500000000000 / 767750085891) := by
    rw [show ((767750085891 / 500000000000) : ℝ) = ((500000000000 / 767750085891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0458
