import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell130
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (282738231 / 1000000000) ≤ -Real.log (5120 / 6793) ∧
    -Real.log (5120 / 6793) ≤ (35342279 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 11913)) (n := 12)
    (lo := (282738231 / 1000000000)) (hi := (35342279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6793 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6793 / 5120) = 1/(5120 / 6793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (282738231 / 1000000000) (35342279 / 125000000) (Real.log (6793 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6793 / 5120) = -Real.log (5120 / 6793) := by
    rw [show ((6793 / 5120) : ℝ) = ((5120 / 6793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (395650151 / 1000000000) ≤ -Real.log (3447 / 5120) ∧
    -Real.log (3447 / 5120) ≤ (49456269 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 8567)) (n := 12)
    (lo := (395650151 / 1000000000)) (hi := (49456269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3447) = 1/(3447 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49456269 / 125000000) (-395650151 / 1000000000) (Real.log (3447 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (141148251 / 500000000) ≤ -Real.log (512 / 679) ∧
    -Real.log (512 / 679) ≤ (282296503 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1191)) (n := 12)
    (lo := (141148251 / 500000000)) (hi := (282296503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 512) = 1/(512 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (141148251 / 500000000) (282296503 / 1000000000) (Real.log (679 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (679 / 512) = -Real.log (512 / 679) := by
    rw [show ((679 / 512) : ℝ) = ((512 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24673763 / 62500000) ≤ -Real.log (345 / 512) ∧
    -Real.log (345 / 512) ≤ (394780209 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 857)) (n := 12)
    (lo := (24673763 / 62500000)) (hi := (394780209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 345) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 345) = 1/(345 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-394780209 / 1000000000) (-24673763 / 62500000) (Real.log (345 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6512557 / 31250000) ≤ -Real.log (250000 / 307927) ∧
    -Real.log (250000 / 307927) ≤ (8336073 / 40000000) := by
  have h := checkLog_sound (w := (57927 / 557927)) (n := 12)
    (lo := (6512557 / 31250000)) (hi := (8336073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307927 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307927 / 250000) = 1/(250000 / 307927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6512557 / 31250000) (8336073 / 40000000) (Real.log (307927 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (307927 / 250000) = -Real.log (250000 / 307927) := by
    rw [show ((307927 / 250000) : ℝ) = ((250000 / 307927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (263585409 / 1000000000) ≤ -Real.log (192073 / 250000) ∧
    -Real.log (192073 / 250000) ≤ (26358541 / 100000000) := by
  have h := checkLog_sound (w := (57927 / 442073)) (n := 12)
    (lo := (263585409 / 1000000000)) (hi := (26358541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192073) = 1/(192073 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26358541 / 100000000) (-263585409 / 1000000000) (Real.log (192073 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (208743567 / 1000000000) ≤ -Real.log (1000000 / 1232129) ∧
    -Real.log (1000000 / 1232129) ≤ (13046473 / 62500000) := by
  have h := checkLog_sound (w := (232129 / 2232129)) (n := 12)
    (lo := (208743567 / 1000000000)) (hi := (13046473 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232129 / 1000000) = 1/(1000000 / 1232129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (208743567 / 1000000000) (13046473 / 62500000) (Real.log (1232129 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1232129 / 1000000) = -Real.log (1000000 / 1232129) := by
    rw [show ((1232129 / 1000000) : ℝ) = ((1000000 / 1232129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33016691 / 125000000) ≤ -Real.log (767871 / 1000000) ∧
    -Real.log (767871 / 1000000) ≤ (264133529 / 1000000000) := by
  have h := checkLog_sound (w := (232129 / 1767871)) (n := 12)
    (lo := (33016691 / 125000000)) (hi := (264133529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767871) = 1/(767871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-264133529 / 1000000000) (-33016691 / 125000000) (Real.log (767871 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153850063 / 1000000000) ≤ -Real.log (250000 / 291579) ∧
    -Real.log (250000 / 291579) ≤ (9615629 / 62500000) := by
  have h := checkLog_sound (w := (41579 / 541579)) (n := 12)
    (lo := (153850063 / 1000000000)) (hi := (9615629 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291579 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291579 / 250000) = 1/(250000 / 291579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153850063 / 1000000000) (9615629 / 62500000) (Real.log (291579 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (291579 / 250000) = -Real.log (250000 / 291579) := by
    rw [show ((291579 / 250000) : ℝ) = ((250000 / 291579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36380169 / 200000000) ≤ -Real.log (208421 / 250000) ∧
    -Real.log (208421 / 250000) ≤ (90950423 / 500000000) := by
  have h := checkLog_sound (w := (41579 / 458421)) (n := 12)
    (lo := (36380169 / 200000000)) (hi := (90950423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208421) = 1/(208421 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-90950423 / 500000000) (-36380169 / 200000000) (Real.log (208421 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4816173 / 31250000) ≤ -Real.log (250000 / 291657) ∧
    -Real.log (250000 / 291657) ≤ (154117537 / 1000000000) := by
  have h := checkLog_sound (w := (41657 / 541657)) (n := 12)
    (lo := (4816173 / 31250000)) (hi := (154117537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291657 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291657 / 250000) = 1/(250000 / 291657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4816173 / 31250000) (154117537 / 1000000000) (Real.log (291657 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (291657 / 250000) = -Real.log (250000 / 291657) := by
    rw [show ((291657 / 250000) : ℝ) = ((250000 / 291657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (182275157 / 1000000000) ≤ -Real.log (208343 / 250000) ∧
    -Real.log (208343 / 250000) ≤ (91137579 / 500000000) := by
  have h := checkLog_sound (w := (41657 / 458343)) (n := 12)
    (lo := (182275157 / 1000000000)) (hi := (91137579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208343) = 1/(208343 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91137579 / 500000000) (-182275157 / 1000000000) (Real.log (208343 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67707671 / 100000000) ≤ -Real.log (250000000000 / 492028985507) ∧
    -Real.log (250000000000 / 492028985507) ≤ (677076711 / 1000000000) := by
  have h := checkLog_sound (w := (242028985507 / 742028985507)) (n := 12)
    (lo := (67707671 / 100000000)) (hi := (677076711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492028985507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492028985507 / 250000000000) = 1/(250000000000 / 492028985507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67707671 / 100000000) (677076711 / 1000000000) (Real.log (492028985507 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (492028985507 / 250000000000) = -Real.log (250000000000 / 492028985507) := by
    rw [show ((492028985507 / 250000000000) : ℝ) = ((250000000000 / 492028985507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (339194191 / 500000000) ≤ -Real.log (100000000000 / 197069915869) ∧
    -Real.log (100000000000 / 197069915869) ≤ (678388383 / 1000000000) := by
  have h := checkLog_sound (w := (97069915869 / 297069915869)) (n := 12)
    (lo := (339194191 / 500000000)) (hi := (678388383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197069915869 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197069915869 / 100000000000) = 1/(100000000000 / 197069915869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (339194191 / 500000000) (678388383 / 1000000000) (Real.log (197069915869 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (197069915869 / 100000000000) = -Real.log (100000000000 / 197069915869) := by
    rw [show ((197069915869 / 100000000000) : ℝ) = ((100000000000 / 197069915869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (471987233 / 1000000000) ≤ -Real.log (250000000000 / 400794229277) ∧
    -Real.log (250000000000 / 400794229277) ≤ (235993617 / 500000000) := by
  have h := checkLog_sound (w := (150794229277 / 650794229277)) (n := 12)
    (lo := (471987233 / 1000000000)) (hi := (235993617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400794229277 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400794229277 / 250000000000) = 1/(250000000000 / 400794229277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (471987233 / 1000000000) (235993617 / 500000000) (Real.log (400794229277 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (400794229277 / 250000000000) = -Real.log (250000000000 / 400794229277) := by
    rw [show ((400794229277 / 250000000000) : ℝ) = ((250000000000 / 400794229277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (59109637 / 125000000) ≤ -Real.log (250000000000 / 401151039693) ∧
    -Real.log (250000000000 / 401151039693) ≤ (472877097 / 1000000000) := by
  have h := checkLog_sound (w := (151151039693 / 651151039693)) (n := 12)
    (lo := (59109637 / 125000000)) (hi := (472877097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401151039693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401151039693 / 250000000000) = 1/(250000000000 / 401151039693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (59109637 / 125000000) (472877097 / 1000000000) (Real.log (401151039693 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (401151039693 / 250000000000) = -Real.log (250000000000 / 401151039693) := by
    rw [show ((401151039693 / 250000000000) : ℝ) = ((250000000000 / 401151039693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (83937727 / 250000000) ≤ -Real.log (500000000000 / 699495252397) ∧
    -Real.log (500000000000 / 699495252397) ≤ (335750909 / 1000000000) := by
  have h := checkLog_sound (w := (199495252397 / 1199495252397)) (n := 12)
    (lo := (83937727 / 250000000)) (hi := (335750909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699495252397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699495252397 / 500000000000) = 1/(500000000000 / 699495252397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (83937727 / 250000000) (335750909 / 1000000000) (Real.log (699495252397 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (699495252397 / 500000000000) = -Real.log (500000000000 / 699495252397) := by
    rw [show ((699495252397 / 500000000000) : ℝ) = ((500000000000 / 699495252397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (168196347 / 500000000) ≤ -Real.log (62500000000 / 87493040323) ∧
    -Real.log (62500000000 / 87493040323) ≤ (67278539 / 200000000) := by
  have h := checkLog_sound (w := (24993040323 / 149993040323)) (n := 12)
    (lo := (168196347 / 500000000)) (hi := (67278539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87493040323 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87493040323 / 62500000000) = 1/(62500000000 / 87493040323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (168196347 / 500000000) (67278539 / 200000000) (Real.log (87493040323 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87493040323 / 62500000000) = -Real.log (62500000000 / 87493040323) := by
    rw [show ((87493040323 / 62500000000) : ℝ) = ((62500000000 / 87493040323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28157621 / 1000000000) ≤ -Real.log (60764694351 / 62500000000) ∧
    -Real.log (60764694351 / 62500000000) ≤ (14078811 / 500000000) := by
  have h := checkLog_sound (w := (1735305649 / 123264694351)) (n := 12)
    (lo := (28157621 / 1000000000)) (hi := (14078811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60764694351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60764694351) = 1/(60764694351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-14078811 / 500000000) (-28157621 / 1000000000) (Real.log (60764694351 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14025391 / 500000000) ≤ -Real.log (60771186759 / 62500000000) ∧
    -Real.log (60771186759 / 62500000000) ≤ (28050783 / 1000000000) := by
  have h := checkLog_sound (w := (1728813241 / 123271186759)) (n := 12)
    (lo := (14025391 / 500000000)) (hi := (28050783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60771186759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60771186759) = 1/(60771186759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28050783 / 1000000000) (-14025391 / 500000000) (Real.log (60771186759 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell130
