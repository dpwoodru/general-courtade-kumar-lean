import GeneralCK.Certificates.LogBounds

/-! Generated rational witnesses for the retained diagonal contact pilot. -/
namespace GeneralCK.Certificates.PilotData

theorem log_two :
    (34657359 / 50000000) ≤ Real.log (2 / 1) ∧
    Real.log (2 / 1) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_left :
    (262151201 / 500000000) ≤ Real.log (5279 / 3125) ∧
    Real.log (5279 / 3125) ≤ (524302403 / 1000000000) := by
  have h := checkLog_sound (w := (1077 / 4202)) (n := 12)
    (lo := (262151201 / 500000000)) (hi := (524302403 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_right :
    (262245907 / 500000000) ≤ Real.log (1056 / 625) ∧
    Real.log (1056 / 625) ≤ (104898363 / 200000000) := by
  have h := checkLog_sound (w := (431 / 1681)) (n := 12)
    (lo := (262245907 / 500000000)) (hi := (104898363 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_left :
    (54234457 / 1000000000) ≤ Real.log (100000 / 94721) ∧
    Real.log (100000 / 94721) ≤ (27117229 / 500000000) := by
  have h := checkLog_sound (w := (5279 / 194721)) (n := 12)
    (lo := (54234457 / 1000000000)) (hi := (27117229 / 500000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_right :
    (27122507 / 500000000) ≤ Real.log (625 / 592) ∧
    Real.log (625 / 592) ≤ (10849003 / 200000000) := by
  have h := checkLog_sound (w := (33 / 1217)) (n := 12)
    (lo := (27122507 / 500000000)) (hi := (10849003 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.PilotData
