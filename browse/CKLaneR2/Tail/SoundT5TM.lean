import CKLaneR2.Tail.SoundT5

/-!
# Lane R2 — tail checker soundness, part 4: TM containment of the fifth-block pieces
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## `g1` bounds and `g1Of` -/

theorem g1_bounds {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) : 1 - v ≤ g1 v ∧ g1 v ≤ 1 := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp [g1]
  unfold g1; rw [if_neg h.ne']
  have h1v : 0 < 1 - v := by linarith
  have hl1 := Real.log_le_sub_one_of_pos h1v
  have hl2 := Real.one_sub_inv_le_log_of_pos h1v
  have hinv : (1 - v)⁻¹ = 1 / (1 - v) := by ring
  constructor
  · rw [le_div_iff₀ h]; nlinarith
  · rw [div_le_iff₀ h]
    have : 1 - (1 - v)⁻¹ = -v / (1 - v) := by field_simp; ring
    rw [this] at hl2
    have h3 : -v ≤ (1 - v) * Real.log (1 - v) := by
      have := mul_le_mul_of_nonneg_left hl2 h1v.le
      rw [mul_div_cancel₀ _ h1v.ne'] at this; linarith
    linarith

theorem g1Of_contains (F : Front) {v omv cv : TM} {vf : ℝ → ℝ → ℝ → ℝ} (hv : Contains one v vf)
    (homv : Contains one omv (fun x y z => 1 - vf x y z))
    (hcv : Contains one cv (fun x y z => -Real.log (1 - vf x y z)))
    (hnn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ vf x y z) :
    Contains one (g1Of F v omv cv) (fun x y z => g1 (vf x y z)) := by
  unfold g1Of
  by_cases hl : F.lim = true
  · rw [if_pos hl]
    intro hok x y z hx hy hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hvok, hup⟩ := hok
    have h0 := hnn x y z hx hy hz
    have hle := Contains.le_upper hone hv hvok x y z hx hy hz
    have hone' := CKLaneR2.Cell.hone'
    have hup' : (v.upper : ℝ) / one < 1 / 2 := by
      rw [div_lt_iff₀ hone']
      have : (v.upper : ℝ) < (((one / 2 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hup
      have h2 : (((one / 2 : ℕ) : ℤ) : ℝ) * 2 ≤ one := by
        have : (one / 2) * 2 ≤ one := Nat.div_mul_le_self one 2
        rw [Int.cast_natCast]; exact_mod_cast this
      linarith
    obtain ⟨gl, gu⟩ := g1_bounds h0 (by linarith)
    have hup0 : (0 : ℤ) ≤ v.upper := by
      have : (0 : ℝ) ≤ (v.upper : ℝ) := by
        have := mul_le_mul_of_nonneg_right (h0.trans hle) hone'.le
        rwa [div_mul_cancel₀ _ hone'.ne', zero_mul] at this
      exact_mod_cast this
    set h : ℤ := (v.upper + 1) / 2 with hh
    have hh0 : 0 ≤ h := Int.ediv_nonneg (by linarith) (by norm_num)
    have hh2 : v.upper ≤ 2 * h := by omega
    have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
      have : ((h.toNat : ℤ)) = h := Int.toNat_of_nonneg hh0
      exact_mod_cast this
    have e : evalP 0 [[[ONEi - h]]] x y z = ((ONEi - h : ℤ) : ℝ) := by simp [evalP, evalC, evalR]
    simp only
    rw [e, hcast, abs_le]
    have hO := ONEi_div
    have hh2' : (v.upper : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hh2
    have hvu : vf x y z ≤ 2 * (h : ℝ) / one := by
      calc vf x y z ≤ (v.upper : ℝ) / one := hle
        _ ≤ 2 * (h : ℝ) / one := div_le_div_of_nonneg_right hh2' hone'.le
    push_cast
    rw [sub_div, hO]
    constructor
    · have : g1 (vf x y z) - (1 - (h : ℝ) / one) ≥ -((h : ℝ) / one) := by
        have : 1 - vf x y z ≥ 1 - 2 * (h : ℝ) / one := by linarith
        have e2 : 2 * (h : ℝ) / one = (h : ℝ) / one + (h : ℝ) / one := by ring
        linarith
      linarith
    · have : (0 : ℝ) ≤ (h : ℝ) / one := div_nonneg (by exact_mod_cast hh0) hone'.le
      linarith
  · rw [if_neg hl]
    by_cases hs : v.upper ≤ ((one / 8 : ℕ) : Int)
    · rw [if_pos (by simpa using hs)]
      exact g1Series_contains hv homv hnn
    · rw [if_neg (by simpa using hs)]
      have hm := C_mul (C_mul homv hcv) (C_recip hv)
      intro hok x y z hx hy hz
      have hrok : (recip v).ok = true := mul_ok_right hok
      -- vf > 0 from the reciprocal's positivity check
      have hpos : 0 < vf x y z := by
        simp only [recip, TM.recip, Bool.and_eq_true, decide_eq_true_eq] at hrok
        have hl := Contains.lower_le hone hv hrok.1.1.1 x y z hx hy hz
        have h0 : (0 : ℝ) < (v.lower : ℝ) / one := div_pos (by exact_mod_cast hrok.1.2) CKLaneR2.Cell.hone'
        linarith
      have h := hm hok x y z hx hy hz
      have e : (1 - vf x y z) * -Real.log (1 - vf x y z) * (vf x y z)⁻¹ = g1 (vf x y z) := by
        unfold g1; rw [if_neg hpos.ne']; field_simp
      simp only at h
      rw [e] at h
      exact h

/-! ## The residual TM -/

theorem t5Resid_contains (F : Front) {s3 rhoT : TM} {s3f uf lamf ggf rf : ℝ → ℝ → ℝ → ℝ}
    (hs3 : Contains one s3 s3f) (hr : Contains one rhoT rf) (hU : Contains one F.U uf)
    (hLam : Contains one F.Lam lamf) (hG1 : Contains one F.G1 ggf)
    (hnn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ uf x y z * rf x y z) :
    Contains one (t5Resid F s3 rhoT).R (fun x y z => residR (s3f x y z) (uf x y z) (lamf x y z) (ggf x y z) (rf x y z))
    ∧ Contains one (t5Resid F s3 rhoT).eta (fun x y z => Real.log (rf x y z))
    ∧ Contains one (t5Resid F s3 rhoT).cv (fun x y z => -Real.log (1 - uf x y z * rf x y z))
    ∧ Contains one (t5Resid F s3 rhoT).v (fun x y z => uf x y z * rf x y z) := by
  have heta := C_log hr
  have hv := C_mul hU hr
  have homv := C_oneSub hv
  have hcv := Contains.neg (C_log homv)
  have hg := g1Of_contains F hv homv hcv hnn
  have hX := C_addOne (Contains.sub (C_mul hLam hg) (C_mul hLam heta))
  have hR := Contains.sub (C_mul (C_mul hs3 hr) hX) (C_mul (C_addOne (Contains.scaleInt hv (-2))) (C_addOne (C_mul hLam hG1)))
  refine ⟨?_, heta, hcv, hv⟩
  refine Contains.congr hR (fun x y z _ _ _ => ?_)
  unfold residR; push_cast; ring

end CKLaneR2.Tail
