import CKLaneN1.EdgeAlg
import CKLaneN1.EdgeCheck
import CKLaneN1.CapTail

set_option autoImplicit false

/-!
# Lane N1: soundness of the leftEdge box checker

`edgeOK_sound`: if `edgeOK B w = true` then for every `(t, z)` in the box with `0 < t < 1`,
`0 < z < 1`, the cutoff-edge value `cPG a (S - a) (H a) (H b)` at `a = m(1-t)`,
`b = m(1 + t(2z-1))` is positive.
-/

namespace CKLaneN1.Edge

open GeneralCK CKLaneE.FP CKLaneN1.Capital Set

/-! ## Elementary helpers -/

theorem rle {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ y := by exact_mod_cast h
theorem rlt {x y : ℚ} (h : x < y) : (x : ℝ) < y := by exact_mod_cast h
theorem rpos {x : ℚ} (h : 0 < x) : (0 : ℝ) < (x : ℝ) := by exact_mod_cast h
theorem rnn {x : ℚ} (h : 0 ≤ x) : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h

/-- A bilinear function `α + β t + γ t z` is bounded below by any common lower bound of its
four corner values. -/
theorem bilin_ge {α β γ t0 t1 z0 z1 t z L : ℝ} (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (hz0 : z0 ≤ z) (hz1 : z ≤ z1)
    (h00 : L ≤ α + β * t0 + γ * t0 * z0) (h01 : L ≤ α + β * t0 + γ * t0 * z1)
    (h10 : L ≤ α + β * t1 + γ * t1 * z0) (h11 : L ≤ α + β * t1 + γ * t1 * z1) :
    L ≤ α + β * t + γ * t * z := by
  have hA : L ≤ α + β * t + γ * t * z0 := by
    rcases le_total 0 (β + γ * z0) with hq | hq
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr ht1)]
  have hB : L ≤ α + β * t + γ * t * z1 := by
    rcases le_total 0 (β + γ * z1) with hq | hq
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr ht1)]
  rcases le_total 0 (γ * t) with hq | hq
  · nlinarith [mul_nonneg hq (sub_nonneg.mpr hz0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr hz1)]

theorem bilin_le {α β γ t0 t1 z0 z1 t z U : ℝ} (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (hz0 : z0 ≤ z) (hz1 : z ≤ z1)
    (h00 : α + β * t0 + γ * t0 * z0 ≤ U) (h01 : α + β * t0 + γ * t0 * z1 ≤ U)
    (h10 : α + β * t1 + γ * t1 * z0 ≤ U) (h11 : α + β * t1 + γ * t1 * z1 ≤ U) :
    α + β * t + γ * t * z ≤ U := by
  have := bilin_ge (α := -α) (β := -β) (γ := -γ) (L := -U) ht0 ht1 hz0 hz1
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

theorem H_sub_le_J {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    H b - H a ≤ J a * (b - a) := by
  have hd : ∀ x, 0 < x → x < 1 → HasDerivAt (fun x => J a * x - H x) (J a - J x) x := by
    intro x hx hx1
    have h1 := ((hasDerivAt_id x).const_mul (J a)).sub (Comparison.hasDerivAt_H hx hx1)
    refine (h1.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    ring
  have hmono : MonotoneOn (fun x => J a * x - H x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x (ha.trans_le hx.1) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (ha.trans hx.1) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (ha.trans hx.1) (by linarith [hx.2])).deriv]
      have := J_anti ha hx.1.le (by linarith [hx.2])
      linarith
  have hm := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at hm
  nlinarith

/-! ## One-time constants -/

theorem Cfun_half_le : Cfun (1 / 2) ≤ ((CHq : ℚ) : ℝ) / 4 := by
  have h3 : ptOk (1 / 3) = true := by decide +kernel
  have h2 : ptOk (1 / 2) = true := by decide +kernel
  have hc : (3 / 2 : ℚ) * (-l1Lo (1 / 3)) + (1 / 2) * lHi (1 / 2) ≤ CHq / 4 := by
    decide +kernel
  have s3 := (ptOk_sound h3).2.2.1
  have s2 := (ptOk_sound h2).2.1
  have hcR : (3 / 2 : ℝ) * (-((l1Lo (1 / 3) : ℚ) : ℝ)) + (1 / 2) * ((lHi (1 / 2) : ℚ) : ℝ) ≤
      ((CHq : ℚ) : ℝ) / 4 := by
    have := rle hc
    push_cast at this ⊢
    linarith
  have e3 : (1 : ℝ) - ((1 / 3 : ℚ) : ℝ) = 2 / 3 := by push_cast; norm_num
  have e2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by push_cast; norm_num
  rw [e3] at s3
  rw [e2] at s2
  have hl32 : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show (3 / 2 : ℝ) = (2 / 3)⁻¹ by norm_num, Real.log_inv]
  unfold Cfun
  norm_num
  rw [show (3 / 2 : ℝ) * Real.log (3 / 2) = (3 / 2) * Real.log (3 / 2) from rfl, hl32]
  nlinarith

/-- `C ρ ≤ ρ² · CH` for `0 < ρ ≤ 1/2`. -/
theorem Cfun_le_CH {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    Cfun r ≤ r ^ 2 * ((CHq : ℚ) : ℝ) := by
  have hm := Chat_mono hr hr2 (by norm_num)
  have hc := Cfun_half_le
  nlinarith [sq_nonneg r]

/-- `C ρ₁ ≤ ρ₁² · Chi1` from certified logarithms. -/
theorem Cfun_le_Chi {r : ℚ} (hr0 : 0 < r) (hr1 : r < 1) (hp1 : ptOk r = true)
    (hp2 : ptOk (r / (1 + r)) = true) :
    Cfun (r : ℝ) ≤ ((1 + (r : ℝ)) * (-((l1Lo (r / (1 + r)) : ℚ) : ℝ)) +
      (1 - (r : ℝ)) * ((l1Hi r : ℚ) : ℝ)) := by
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) < 1 := by exact_mod_cast hr1
  have s1 := (ptOk_sound hp1).2.2.2
  have s2 := (ptOk_sound hp2).2.2.1
  have e : (1 : ℝ) - ((r / (1 + r) : ℚ) : ℝ) = (1 + (r : ℝ))⁻¹ := by
    push_cast
    field_simp
    ring
  rw [e, Real.log_inv] at s2
  unfold Cfun
  have h1 : (1 + (r : ℝ)) * Real.log (1 + r) ≤ (1 + (r : ℝ)) * (-((l1Lo (r / (1 + r)) : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (1 - (r : ℝ)) * Real.log (1 - r) ≤ (1 - (r : ℝ)) * ((l1Hi r : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left s1 (by linarith)
  linarith

/-! ## Pointwise lower bound -/

/-- The cutoff-edge value dominates the ratio term, the interior cost and the two outer
tangent terms. -/
theorem edge_main_lb {S a b X : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < S - a)
    (hc : S - a < 1 / 2) (hX : (S - 2 * a) / (2 * ((H a + H b) / 2)) ≤ X) :
    e8Theta X / X * ((S - 2 * a) ^ 2 - (b - a) ^ 2) / (4 * ((H a + H b) / 2)) +
        interiorCost a b +
        (2 * entropyInverse ((H a + H b) / 2) - S) *
          e8Theta ((1 - 2 * entropyInverse ((H a + H b) / 2)) / (2 * ((H a + H b) / 2))) +
        ((S - a) - b) * e8Theta ((1 - 2 * (S - a)) / (2 * H b)) ≤
      canonicalPureGap a (S - a) (H a) (H b) := by
  rw [cpg_edge_eq ha hab hbc hc.le]
  have hb2 : b < 1 / 2 := by linarith
  have hHb : 0 < H b := H_pos (by linarith) (by linarith)
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hh0 : 0 < (H a + H b) / 2 := by linarith
  have hh1 : (H a + H b) / 2 < 1 := by
    have := H_lt_one ha.le (by linarith : a < 1 / 2)
    have := H_lt_one (by linarith : (0 : ℝ) ≤ b) hb2
    linarith
  have hq2 : entropyInverse ((H a + H b) / 2) < 1 / 2 := entropyInverse_lt_half hh0.le hh1
  have h1 := F_sub_ge_ratio hh0 (sub_pos.mpr hab) (by linarith : b - a ≤ S - 2 * a) hX
  have h2 := F_tangent (h := (H a + H b) / 2) hh0
    (x0 := 1 - 2 * entropyInverse ((H a + H b) / 2)) (x := 1 - S) (by linarith) (by linarith)
  have h3 := F_tangent (h := H b) hHb (x0 := 1 - 2 * (S - a)) (x := 1 - 2 * b)
    (by linarith) (by linarith)
  have e2 : (1 - S) - (1 - 2 * entropyInverse ((H a + H b) / 2)) =
      2 * entropyInverse ((H a + H b) / 2) - S := by ring
  have e3 : (1 - 2 * b) - (1 - 2 * (S - a)) = 2 * ((S - a) - b) := by ring
  rw [e2] at h2
  rw [e3] at h3
  linarith

/-! ## Term bounds -/

theorem T1_bound {y d h h1 X κ : ℝ} (hd : 0 ≤ d) (hdy : d ≤ y) (hh : 0 < h) (hh1 : h ≤ h1)
    (hX : 0 < X) (hκ : κ ≤ e8Theta X) (hκ0 : 0 ≤ κ) :
    κ / X / (4 * h1) * (y ^ 2 - d ^ 2) ≤ e8Theta X / X * (y ^ 2 - d ^ 2) / (4 * h) := by
  have hyd : 0 ≤ y ^ 2 - d ^ 2 := by nlinarith
  have hk1 : κ / X ≤ e8Theta X / X := div_le_div_of_nonneg_right hκ hX.le
  have hk0 : 0 ≤ κ / X := div_nonneg hκ0 hX.le
  have hh1' : 0 < 4 * h1 := by linarith
  have e1 : κ / X / (4 * h1) ≤ κ / X / (4 * h) :=
    div_le_div_of_nonneg_left hk0 (by linarith) (by linarith)
  have e2 : κ / X / (4 * h) ≤ e8Theta X / X / (4 * h) :=
    div_le_div_of_nonneg_right hk1 (by linarith)
  have e3 : e8Theta X / X * (y ^ 2 - d ^ 2) / (4 * h) = e8Theta X / X / (4 * h) * (y ^ 2 - d ^ 2) := by
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_right (e1.trans e2) hyd

/-- Normalized entropy-Jensen bound. -/
theorem jensen_gap_le {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    a + b - 2 * entropyInverse ((H a + H b) / 2) ≤
      ((a + b) / 2 * Cfun ((b - a) / (a + b)) +
        (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) /
        (Real.log 2 * J ((a + b) / 2)) := by
  obtain ⟨-, -, hq, -⟩ := q_facts ha hab.le hb
  have hJ : 0 < J ((a + b) / 2) := J_pos (by linarith) (by linarith)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJH := JH_eq ha hab (by linarith)
  rw [hJH] at hq
  rw [le_div_iff₀ (mul_pos hL hJ)]
  have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * Real.log 2 by linarith)
  have e : 2 * Real.log 2 * (((a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) / (2 * Real.log 2)) =
      (a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2))) := by
    field_simp
  rw [e] at this
  nlinarith

/-! ## Variant term bounds -/

section Terms

variable {a b y z : ℝ}

/-- Interior-cost term. -/
theorem T2_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (ha : 0 < a) (hab : a < b)
    (hb : b < 1 / 2) (hy : 0 < y) (hd : b - a = z * y) (hz : 0 ≤ z)
    (hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ)) (ha1 : a ≤ ((ea1 B : ℚ) : ℝ))
    (ha1' : ((ea1 B : ℚ) : ℝ) < 1) (hb0 : ((eb0 B : ℚ) : ℝ) ≤ b) (hb0' : 0 < ((eb0 B : ℚ) : ℝ))
    (hb0p : ptOk (eb0 B) = true) (hy1 : y ≤ ((ey1 B : ℚ) : ℝ)) :
    y ^ 2 * (((eT2 B w).1 : ℝ) * z + ((eT2 B w).2 : ℝ) * z ^ 2) ≤ interiorCost a b := by
  have hL := log_two_mem
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  cases hk : w.k2
  · simp only [eT2, hk, Bool.false_eq_true, if_false]
    have hj := interiorCost_ge ha hab (by linarith)
    have hden : 0 < (a + b) * Real.log 2 := mul_pos (by linarith) hL0
    have hden2 : (a + b) * Real.log 2 ≤ 2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ) := by
      have h1 : a + b ≤ 2 * ((eM1 B : ℚ) : ℝ) := by linarith
      exact mul_le_mul h1 hL.2 hL0.le (by linarith)
    have hmono : (b - a) ^ 2 / (2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) ≤
        (b - a) ^ 2 / ((a + b) * Real.log 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hden hden2
    have e : y ^ 2 * (((0 : ℚ) : ℝ) * z + ((1 / (2 * eM1 B * LqHi) : ℚ) : ℝ) * z ^ 2) =
        (b - a) ^ 2 / (2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) := by
      rw [hd]
      push_cast
      ring
    rw [e]
    linarith
  · simp only [eT2, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨⟨⟨⟨⟨hpa1, hlam⟩, hD⟩, hy1pos⟩, -⟩, -⟩ := hV
    have hJa : ((lamLo (ea1 B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J a :=
      (J_ge hpa1 hlam).trans (J_anti ha ha1 ha1')
    have hJb : J b ≤ ((lamHi (eb0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
      (J_anti hb0' hb0 (by linarith)).trans (J_le hb0p (by linarith))
    have hDR : (0 : ℝ) ≤ ((eDelta B : ℚ) : ℝ) := by exact_mod_cast hD
    have hDle : ((eDelta B : ℚ) : ℝ) ≤ J a - J b := by
      simp only [eDelta]
      push_cast
      linarith
    have hy1p : (0 : ℝ) < ((ey1 B : ℚ) : ℝ) := by exact_mod_cast hy1pos
    unfold interiorCost
    rw [hd]
    have h1 : z * y * ((eDelta B : ℚ) : ℝ) / 2 ≤ z * y * (J a - J b) / 2 := by
      have := mul_le_mul_of_nonneg_left hDle (mul_nonneg hz hy.le)
      linarith
    have h2 : y ^ 2 * (((eDelta B / (2 * ey1 B) : ℚ) : ℝ) * z + ((0 : ℚ) : ℝ) * z ^ 2) ≤
        z * y * ((eDelta B : ℚ) : ℝ) / 2 := by
      push_cast
      rw [show y ^ 2 * (((eDelta B : ℚ) : ℝ) / (2 * ((ey1 B : ℚ) : ℝ)) * z + 0 * z ^ 2) =
        z * y * ((eDelta B : ℚ) : ℝ) / 2 * (y / ((ey1 B : ℚ) : ℝ)) by field_simp; ring]
      have hr : y / ((ey1 B : ℚ) : ℝ) ≤ 1 := by rw [div_le_one hy1p]; exact hy1
      have hnn : 0 ≤ z * y * ((eDelta B : ℚ) : ℝ) / 2 := by positivity
      nlinarith
    linarith

/-- Algebra of the normalized Jensen variant. -/
theorem jensen_alg_norm {g M ρ ρ' Cρ Cρ' D L JM Chi CH M0 M1 Lq J1 : ℝ}
    (hg : g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM))
    (hCρ : Cρ ≤ ρ ^ 2 * Chi) (hCρ' : Cρ' ≤ ρ' ^ 2 * CH)
    (eρ : M * ρ ^ 2 = D / (4 * M)) (eρ' : (1 - M) * ρ' ^ 2 = D / (4 * (1 - M)))
    (hD : 0 ≤ D) (hM0 : 0 < M0) (hM0M : M0 ≤ M) (hMM1 : M ≤ M1) (hM1 : M1 < 1)
    (hLq : 0 < Lq) (hLqL : Lq ≤ L) (hJ1 : 0 < J1) (hJ1J : J1 ≤ JM)
    (hChi : 0 ≤ Chi) (hCH : 0 ≤ CH) :
    g ≤ D * (Chi / M0 + CH / (1 - M1)) / (4 * (Lq * J1)) := by
  have hMpos : 0 < M := lt_of_lt_of_le hM0 hM0M
  have h1M : 0 < 1 - M := by linarith
  have h1M1 : 0 < 1 - M1 := by linarith
  have hN : M * Cρ + (1 - M) * Cρ' ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 := by
    have a1 : M * Cρ ≤ M * (ρ ^ 2 * Chi) := mul_le_mul_of_nonneg_left hCρ hMpos.le
    have a2 : (1 - M) * Cρ' ≤ (1 - M) * (ρ' ^ 2 * CH) := mul_le_mul_of_nonneg_left hCρ' h1M.le
    have a3 : M * (ρ ^ 2 * Chi) = D / (4 * M) * Chi := by rw [← eρ]; ring
    have a4 : (1 - M) * (ρ' ^ 2 * CH) = D / (4 * (1 - M)) * CH := by rw [← eρ']; ring
    have a5 : D / (4 * M) * Chi ≤ D / (4 * M0) * Chi :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD (by positivity) (by linarith)) hChi
    have a6 : D / (4 * (1 - M)) * CH ≤ D / (4 * (1 - M1)) * CH :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD (by linarith) (by linarith)) hCH
    have a7 : D / (4 * M0) * Chi + D / (4 * (1 - M1)) * CH = D * (Chi / M0 + CH / (1 - M1)) / 4 := by
      field_simp
    linarith
  have hN' : 0 ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 :=
    div_nonneg (mul_nonneg hD (add_nonneg (div_nonneg hChi hM0.le) (div_nonneg hCH h1M1.le)))
      (by norm_num)
  have hLJ : 0 < L * JM := mul_pos (by linarith) (by linarith)
  have hLJ' : Lq * J1 ≤ L * JM := mul_le_mul hLqL hJ1J hJ1.le (by linarith)
  calc g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM) := hg
    _ ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 / (L * JM) := div_le_div_of_nonneg_right hN hLJ.le
    _ ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 / (Lq * J1) :=
        div_le_div_of_nonneg_left hN' (mul_pos hLq hJ1) hLJ'
    _ = D * (Chi / M0 + CH / (1 - M1)) / (4 * (Lq * J1)) := by rw [div_div]

/-- Algebra of the direct Jensen variant. -/
theorem jensen_alg_direct {g M Cρ Cρ' L JM CH M0 M1 Lq Lh J1 R : ℝ}
    (hg : g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM))
    (hCρ : Cρ ≤ 2 * L) (hCρ' : Cρ' ≤ R ^ 2 * CH)
    (hM0M : M0 ≤ M) (hMM1 : M ≤ M1) (hMpos : 0 < M) (hM1 : M < 1)
    (hLq : 0 < Lq) (hLqL : Lq ≤ L) (hLLh : L ≤ Lh) (hJ1 : 0 < J1) (hJ1J : J1 ≤ JM)
    (hCH : 0 ≤ CH) :
    g ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (Lq * J1) := by
  have h1M : 0 < 1 - M := by linarith
  have hN : M * Cρ + (1 - M) * Cρ' ≤ M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH := by
    have a1 : M * Cρ ≤ M1 * (2 * Lh) := by
      calc M * Cρ ≤ M * (2 * L) := mul_le_mul_of_nonneg_left hCρ hMpos.le
        _ ≤ M1 * (2 * Lh) := mul_le_mul hMM1 (by linarith) (by linarith) (by linarith)
    have a2 : (1 - M) * Cρ' ≤ (1 - M0) * R ^ 2 * CH := by
      calc (1 - M) * Cρ' ≤ (1 - M) * (R ^ 2 * CH) := mul_le_mul_of_nonneg_left hCρ' h1M.le
        _ ≤ (1 - M0) * (R ^ 2 * CH) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg R) hCH)
        _ = (1 - M0) * R ^ 2 * CH := by ring
    linarith
  have hN' : 0 ≤ M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH := by
    have : 0 ≤ M1 := by linarith
    have : 0 ≤ Lh := by linarith
    have : 0 ≤ 1 - M0 := by linarith
    positivity
  have hLJ : 0 < L * JM := mul_pos (by linarith) (by linarith)
  have hLJ' : Lq * J1 ≤ L * JM := mul_le_mul hLqL hJ1J hJ1.le (by linarith)
  calc g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM) := hg
    _ ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (L * JM) := div_le_div_of_nonneg_right hN hLJ.le
    _ ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (Lq * J1) :=
        div_le_div_of_nonneg_left hN' (mul_pos hLq hJ1) hLJ'

set_option maxHeartbeats 1000000 in
/-- Entropy-Jensen term. Here `g = a + b - 2q` and `Θq = Θ(X_q)`. -/
theorem T3_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (ha : 0 < a) (hab : a < b)
    (hb : b < 1 / 2) (hy : 0 < y) (hd : b - a = z * y)
    {Θq : ℝ} (hΘ0 : 0 ≤ Θq) (hΘ1 : Θq ≤ ((slopeHi w.v2 : ℚ) : ℝ))
    (hM0 : ((eM0 B : ℚ) : ℝ) ≤ (a + b) / 2) (hM0p : 0 < ((eM0 B : ℚ) : ℝ))
    (hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ)) (hM1l : ((eM1 B : ℚ) : ℝ) < 1 / 2)
    (hJM : ((eJM1 B : ℚ) : ℝ) ≤ J ((a + b) / 2)) (hJMp : 0 < ((eJM1 B : ℚ) : ℝ))
    (hrho : (b - a) / (a + b) ≤ ((erho1 B : ℚ) : ℝ))
    (hrhop : (b - a) / (2 * (1 - (a + b) / 2)) ≤ ((erhop1 B : ℚ) : ℝ))
    (hrhop2 : ((erhop1 B : ℚ) : ℝ) ≤ 1 / 2) (hy0 : ((ey0 B : ℚ) : ℝ) ≤ y) :
    (a + b - 2 * entropyInverse ((H a + H b) / 2)) * Θq ≤
      y ^ 2 * (((eT3 B w).1 : ℝ) + ((eT3 B w).2 : ℝ) * z ^ 2) := by
  have hL := log_two_mem
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLq : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := LqLo_pos
  have hs : 0 < a + b := by linarith
  have hMpos : 0 < (a + b) / 2 := by linarith
  have hM1' : 0 < 1 - (a + b) / 2 := by linarith
  have hρpos : 0 < (b - a) / (a + b) := div_pos (by linarith) hs
  have hρ1 : (b - a) / (a + b) ≤ 1 := by rw [div_le_one hs]; linarith
  have hρ'pos : 0 < (b - a) / (2 * (1 - (a + b) / 2)) := div_pos (by linarith) (by linarith)
  have hq := q_facts ha hab.le hb
  have hg0 : 0 ≤ a + b - 2 * entropyInverse ((H a + H b) / 2) := by linarith [hq.2.1]
  have hJ := jensen_gap_le ha hab hb
  have hCρ' := Cfun_le_CH hρ'pos (hrhop.trans hrhop2)
  have hCH0 : (0 : ℝ) ≤ ((CHq : ℚ) : ℝ) := by norm_num [CHq]
  have hΘ1' : 0 ≤ ((slopeHi w.v2 : ℚ) : ℝ) := hΘ0.trans hΘ1
  have hgΘ : (a + b - 2 * entropyInverse ((H a + H b) / 2)) * Θq ≤
      (a + b - 2 * entropyInverse ((H a + H b) / 2)) * ((slopeHi w.v2 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hΘ1 hg0
  have eMρ : (a + b) / 2 * ((b - a) / (a + b)) ^ 2 = (b - a) ^ 2 / (4 * ((a + b) / 2)) := by
    field_simp; ring
  have eMρ' : (1 - (a + b) / 2) * ((b - a) / (2 * (1 - (a + b) / 2))) ^ 2 =
      (b - a) ^ 2 / (4 * (1 - (a + b) / 2)) := by
    field_simp; ring
  cases hk : w.k3
  · simp only [eT3, hk, Bool.false_eq_true, if_false]
    simp only [eVarOK, hk, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq]
      at hV
    obtain ⟨⟨-, ⟨⟨⟨⟨hr0, hr1⟩, hpr⟩, hpr2⟩, hchi⟩⟩, -⟩ := hV
    have hr0R : (0 : ℝ) < ((erho1 B : ℚ) : ℝ) := by exact_mod_cast hr0
    have hr1R : ((erho1 B : ℚ) : ℝ) < 1 := by exact_mod_cast hr1
    have hchiR : (0 : ℝ) ≤ ((eChi1 B : ℚ) : ℝ) := by exact_mod_cast hchi
    have hCmono := Chat_mono hρpos hrho hr1R
    have hCle := Cfun_le_Chi hr0 hr1 hpr hpr2
    have hChiE : ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 =
        (1 + ((erho1 B : ℚ) : ℝ)) * (-((l1Lo (erho1 B / (1 + erho1 B)) : ℚ) : ℝ)) +
          (1 - ((erho1 B : ℚ) : ℝ)) * ((l1Hi (erho1 B) : ℚ) : ℝ) := by
      simp only [eChi1]
      push_cast
      field_simp
    have hCρ : Cfun ((b - a) / (a + b)) ≤ ((b - a) / (a + b)) ^ 2 * ((eChi1 B : ℚ) : ℝ) := by
      have hr2 : 0 < ((erho1 B : ℚ) : ℝ) ^ 2 := by positivity
      have h1 : Cfun ((b - a) / (a + b)) * ((erho1 B : ℚ) : ℝ) ^ 2 ≤
          ((b - a) / (a + b)) ^ 2 * ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 := by
        have h2 : Cfun (((erho1 B : ℚ) : ℝ)) * ((b - a) / (a + b)) ^ 2 ≤
            ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 * ((b - a) / (a + b)) ^ 2 := by
          rw [hChiE]
          exact mul_le_mul_of_nonneg_right hCle (sq_nonneg _)
        nlinarith
      exact le_of_mul_le_mul_right h1 hr2
    have hg := jensen_alg_norm hJ hCρ hCρ' eMρ eMρ' (sq_nonneg _) hM0p hM0 hM1 (by linarith)
      hLq hL.1 hJMp hJM hchiR hCH0
    have e : y ^ 2 * (((0 : ℚ) : ℝ) + ((slopeHi w.v2 * exi B : ℚ) : ℝ) * z ^ 2) =
        (b - a) ^ 2 * (((eChi1 B : ℚ) : ℝ) / ((eM0 B : ℚ) : ℝ) +
          ((CHq : ℚ) : ℝ) / (1 - ((eM1 B : ℚ) : ℝ))) /
          (4 * (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) * ((slopeHi w.v2 : ℚ) : ℝ) := by
      rw [hd]
      simp only [exi]
      push_cast
      ring
    rw [e]
    exact hgΘ.trans (mul_le_mul_of_nonneg_right hg hΘ1')
  · simp only [eT3, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨⟨-, hy0p⟩, -⟩ := hV
    have hy0R : (0 : ℝ) < ((ey0 B : ℚ) : ℝ) := by exact_mod_cast hy0p
    have hCρ := Cfun_le_two_log_two hρpos.le hρ1
    have hCρ'' : Cfun ((b - a) / (2 * (1 - (a + b) / 2))) ≤
        ((erhop1 B : ℚ) : ℝ) ^ 2 * ((CHq : ℚ) : ℝ) :=
      hCρ'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ'pos.le hrhop 2) hCH0)
    have hg := jensen_alg_direct hJ hCρ hCρ'' hM0 hM1 hMpos (by linarith) hLq hL.1 hL.2 hJMp hJM
      hCH0
    set G := ((eM1 B : ℚ) : ℝ) * (2 * ((LqHi : ℚ) : ℝ)) +
      (1 - ((eM0 B : ℚ) : ℝ)) * ((erhop1 B : ℚ) : ℝ) ^ 2 * ((CHq : ℚ) : ℝ) with hG
    have hGd : 0 ≤ G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ)) := hg0.trans hg
    have hyy : 1 ≤ y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hy0R.le hy0 2
    have e : y ^ 2 * (((slopeHi w.v2 * (eM1 B * (2 * LqHi) + (1 - eM0 B) * erhop1 B ^ 2 * CHq) /
        (LqLo * eJM1 B * ey0 B ^ 2) : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * z ^ 2) =
        y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 * (G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) *
          ((slopeHi w.v2 : ℚ) : ℝ) := by
      have hLqne : ((LqLo : ℚ) : ℝ) ≠ 0 := hLq.ne'
      have hJne : ((eJM1 B : ℚ) : ℝ) ≠ 0 := hJMp.ne'
      have hy0ne : ((ey0 B : ℚ) : ℝ) ≠ 0 := hy0R.ne'
      rw [hG]
      push_cast
      field_simp
      ring
    refine le_of_le_of_eq ?_ e.symm
    have h1 := mul_le_mul_of_nonneg_right hg hΘ1'
    have h2 : G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ)) * ((slopeHi w.v2 : ℚ) : ℝ) ≤
        y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 * (G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) *
          ((slopeHi w.v2 : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hyy (mul_nonneg hGd hΘ1')
      linarith
    linarith

/-- Algebra of the outer tangent term. -/
theorem T4_alg_norm {cb y z Θd c4 g : ℝ} (hcb : cb = y * (1 - z)) (hcb0 : 0 ≤ cb)
    (hΘ : Θd ≤ 81 / 50 * (y * c4 + z * y * g)) :
    cb * Θd ≤ y ^ 2 * (81 / 50 * c4 + 81 / 50 * (g - c4) * z + -(81 / 50 * g) * z ^ 2) := by
  have h := mul_le_mul_of_nonneg_left hΘ hcb0
  have e : cb * (81 / 50 * (y * c4 + z * y * g)) =
      y ^ 2 * (81 / 50 * c4 + 81 / 50 * (g - c4) * z + -(81 / 50 * g) * z ^ 2) := by
    rw [hcb]; ring
  linarith

theorem T4_alg_direct {cb y z Θd c4 Lh y0 : ℝ} (hcb : cb = y * (1 - z)) (hz1 : z ≤ 1)
    (hy0 : 0 < y0) (hyy0 : y0 ≤ y) (hLh : 0 ≤ Lh)
    (hΘ : Θd ≤ 81 / 50 * (y * c4 + Lh)) :
    cb * Θd ≤ y ^ 2 * (81 / 50 * (c4 + Lh / y0) + -(81 / 50 * (c4 + Lh / y0)) * z) := by
  have hy : 0 < y := lt_of_lt_of_le hy0 hyy0
  have hcb0 : 0 ≤ cb := by rw [hcb]; exact mul_nonneg hy.le (by linarith)
  have h := mul_le_mul_of_nonneg_left hΘ hcb0
  have hL : y * Lh ≤ y ^ 2 * (Lh / y0) := by
    rw [show y ^ 2 * (Lh / y0) = y * Lh * (y / y0) by field_simp]
    have : 1 ≤ y / y0 := by rw [le_div_iff₀ hy0]; linarith
    nlinarith [mul_nonneg hy.le hLh]
  have e1 : cb * (81 / 50 * (y * c4 + Lh)) = 81 / 50 * (1 - z) * (y ^ 2 * c4 + y * Lh) := by
    rw [hcb]; ring
  have e2 : y ^ 2 * (81 / 50 * (c4 + Lh / y0) + -(81 / 50 * (c4 + Lh / y0)) * z) =
      81 / 50 * (1 - z) * (y ^ 2 * c4 + y ^ 2 * (Lh / y0)) := by ring
  have h3 : 81 / 50 * (1 - z) * (y ^ 2 * c4 + y * Lh) ≤
      81 / 50 * (1 - z) * (y ^ 2 * c4 + y ^ 2 * (Lh / y0)) := by
    apply mul_le_mul_of_nonneg_left _ (by nlinarith)
    linarith
  linarith

/-- Outer tangent term. -/
theorem T4_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (hab : a < b)
    (hy : 0 < y) (hd : b - a = z * y) (hz1 : z ≤ 1)
    {c q e f : ℝ} (hcb : c - b = y * (1 - z)) (hcq : c - q ≤ y) (hc1 : c ≤ ((ec1 B : ℚ) : ℝ))
    (hc1' : 0 < 1 - 2 * ((ec1 B : ℚ) : ℝ))
    (hq2 : q ≤ c) (he0 : ((ee0 B : ℚ) : ℝ) ≤ e) (he0' : 0 ≤ ((ee0 B : ℚ) : ℝ))
    (hef : e ≤ f) (hf1 : f ≤ ((ef1 B : ℚ) : ℝ)) {h : ℝ} (hh : h = (e + f) / 2)
    (hh0 : ((eh0 B : ℚ) : ℝ) ≤ h) (hh0p : 0 < ((eh0 B : ℚ) : ℝ))
    (hfe : f - e ≤ J a * (b - a)) (hJa : ∀ _ : 0 < ((ea0 B : ℚ) : ℝ), ptOk (ea0 B) = true →
      J a ≤ ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ)) (hJa0 : 0 ≤ J a)
    (hy0 : ((ey0 B : ℚ) : ℝ) ≤ y)
    {Θq Θc : ℝ}
    (hΘ : Θq - Θc ≤ 81 / 50 * Real.log (((1 - 2 * q) / (2 * h)) / ((1 - 2 * c) / (2 * f)))) :
    (c - b) * (Θq - Θc) ≤
      y ^ 2 * (((eT4 B w).1 : ℝ) + ((eT4 B w).2.1 : ℝ) * z + ((eT4 B w).2.2 : ℝ) * z ^ 2) := by
  subst hh
  have hf0 : 0 < f := by linarith
  have hef0 : 0 < e + f := by linarith
  have hhpos : 0 < (e + f) / 2 := by linarith
  have h1c : 0 < 1 - 2 * c := by linarith
  have h1q : 0 < 1 - 2 * q := by linarith
  have hlog : Real.log (((1 - 2 * q) / (2 * ((e + f) / 2))) / ((1 - 2 * c) / (2 * f))) =
      Real.log ((1 - 2 * q) / (1 - 2 * c)) + Real.log (f / ((e + f) / 2)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog] at hΘ
  have hl1 : Real.log ((1 - 2 * q) / (1 - 2 * c)) ≤ y * (2 / (1 - 2 * ((ec1 B : ℚ) : ℝ))) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 - 2 * q) / (1 - 2 * c) by positivity)
    have e1 : (1 - 2 * q) / (1 - 2 * c) - 1 = 2 * (c - q) / (1 - 2 * c) := by
      field_simp; ring
    rw [e1] at this
    have h2 : 2 * (c - q) / (1 - 2 * c) ≤ 2 * y / (1 - 2 * ((ec1 B : ℚ) : ℝ)) := by
      rw [div_le_div_iff₀ h1c hc1']
      nlinarith
    have e2 : 2 * y / (1 - 2 * ((ec1 B : ℚ) : ℝ)) = y * (2 / (1 - 2 * ((ec1 B : ℚ) : ℝ))) := by
      ring
    linarith
  have hcb0 : 0 ≤ c - b := by rw [hcb]; exact mul_nonneg hy.le (by linarith)
  have hc4 : ((ec4 B : ℚ) : ℝ) = 2 / (1 - 2 * ((ec1 B : ℚ) : ℝ)) := by
    simp only [ec4]; push_cast; ring
  have hK : ((Kq : ℚ) : ℝ) = 81 / 50 := by norm_num [Kq]
  cases hk : w.k4
  · simp only [eT4, hk, Bool.false_eq_true, if_false]
    simp only [eVarOK, hk, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq]
      at hV
    obtain ⟨-, ⟨ha0p, hpa0⟩⟩ := hV
    have ha0R : (0 : ℝ) < ((ea0 B : ℚ) : ℝ) := by exact_mod_cast ha0p
    have hJ := hJa ha0R hpa0
    have hl2 : Real.log (f / ((e + f) / 2)) ≤ z * y * ((eg B : ℚ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show 0 < f / ((e + f) / 2) by positivity)
      have e1 : f / ((e + f) / 2) - 1 = (f - e) / (2 * ((e + f) / 2)) := by
        field_simp; ring
      rw [e1] at this
      have hnum : 0 ≤ J a * (b - a) := mul_nonneg hJa0 (by linarith)
      have h3 : (f - e) / (2 * ((e + f) / 2)) ≤ J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) :=
        calc (f - e) / (2 * ((e + f) / 2)) ≤ J a * (b - a) / (2 * ((e + f) / 2)) :=
              div_le_div_of_nonneg_right hfe (by linarith)
          _ ≤ J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) :=
              div_le_div_of_nonneg_left hnum (by linarith) (by linarith)
      have h4 : J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) ≤ z * y * ((eg B : ℚ) : ℝ) := by
        have hg : ((eg B : ℚ) : ℝ) = ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) /
            (2 * ((eh0 B : ℚ) : ℝ)) := by
          simp only [eg]; push_cast; ring
        rw [hd, hg]
        have hzy : 0 ≤ z * y := by rw [← hd]; linarith
        rw [show J a * (z * y) / (2 * ((eh0 B : ℚ) : ℝ)) =
          z * y * (J a / (2 * ((eh0 B : ℚ) : ℝ))) by ring]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hJ (by linarith)) hzy
      linarith
    have htot : Θq - Θc ≤ 81 / 50 * (y * ((ec4 B : ℚ) : ℝ) + z * y * ((eg B : ℚ) : ℝ)) := by
      rw [hc4]; linarith
    have := T4_alg_norm hcb hcb0 htot
    push_cast
    rw [hK]
    linarith
  · simp only [eT4, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨-, ⟨hy0p, hpq4⟩⟩ := hV
    have hy0R : (0 : ℝ) < ((ey0 B : ℚ) : ℝ) := by exact_mod_cast hy0p
    have hq4 := ptOk_pos hpq4
    have hs := (ptOk_sound hpq4).2.2.1
    have hf1p : 0 < ((ef1 B : ℚ) : ℝ) := by linarith
    have hq4e : ((eq4 B : ℚ) : ℝ) = (((ef1 B : ℚ) : ℝ) - ((ee0 B : ℚ) : ℝ)) /
        (2 * ((ef1 B : ℚ) : ℝ)) := by
      simp only [eq4]; push_cast; ring
    have hone : 1 - ((eq4 B : ℚ) : ℝ) = (((ee0 B : ℚ) : ℝ) + ((ef1 B : ℚ) : ℝ)) /
        (2 * ((ef1 B : ℚ) : ℝ)) := by
      rw [hq4e]; field_simp; ring
    have hratio : f / ((e + f) / 2) ≤ (1 - ((eq4 B : ℚ) : ℝ))⁻¹ := by
      rw [hone, inv_div, div_le_div_iff₀ hhpos (by linarith)]
      nlinarith
    have hl2 : Real.log (f / ((e + f) / 2)) ≤ ((eLhi B : ℚ) : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hratio
      rw [Real.log_inv] at h1
      simp only [eLhi]
      push_cast
      linarith
    have hLhi0 : 0 ≤ ((eLhi B : ℚ) : ℝ) := by
      have hq40 : (0 : ℝ) < ((eq4 B : ℚ) : ℝ) := by exact_mod_cast hq4.1
      have hq41 : ((eq4 B : ℚ) : ℝ) < 1 := by exact_mod_cast hq4.2
      have : Real.log (1 - ((eq4 B : ℚ) : ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      simp only [eLhi]
      push_cast
      linarith
    have htot : Θq - Θc ≤ 81 / 50 * (y * ((ec4 B : ℚ) : ℝ) + ((eLhi B : ℚ) : ℝ)) := by
      rw [hc4]; linarith
    have := T4_alg_direct hcb hz1 hy0R hy0 hLhi0 htot
    push_cast
    rw [hK]
    linarith

end Terms


/-! ## Box geometry helpers -/

theorem min4_le_bilin {B : B3} {t z : ℝ} (f : ℚ → ℚ → ℚ) (α β γ : ℝ)
    (hf : ∀ u v : ℚ, ((f u v : ℚ) : ℝ) = α + β * u + γ * u * v)
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ)) :
    ((min (min (f B.a0 B.b0) (f B.a0 B.b1)) (min (f B.a1 B.b0) (f B.a1 B.b1)) : ℚ) : ℝ) ≤
      α + β * t + γ * t * z := by
  apply bilin_ge ht0 ht1 hz0 hz1
  · rw [← hf]; exact rle (le_trans (min_le_left _ _) (min_le_left _ _))
  · rw [← hf]; exact rle (le_trans (min_le_left _ _) (min_le_right _ _))
  · rw [← hf]; exact rle (le_trans (min_le_right _ _) (min_le_left _ _))
  · rw [← hf]; exact rle (le_trans (min_le_right _ _) (min_le_right _ _))

theorem bilin_le_max4 {B : B3} {t z : ℝ} (f : ℚ → ℚ → ℚ) (α β γ : ℝ)
    (hf : ∀ u v : ℚ, ((f u v : ℚ) : ℝ) = α + β * u + γ * u * v)
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ)) :
    α + β * t + γ * t * z ≤
      ((max (max (f B.a0 B.b0) (f B.a0 B.b1)) (max (f B.a1 B.b0) (f B.a1 B.b1)) : ℚ) : ℝ) := by
  apply bilin_le ht0 ht1 hz0 hz1
  · rw [← hf]; exact rle (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [← hf]; exact rle (le_trans (le_max_right _ _) (le_max_left _ _))
  · rw [← hf]; exact rle (le_trans (le_max_left _ _) (le_max_right _ _))
  · rw [← hf]; exact rle (le_trans (le_max_right _ _) (le_max_right _ _))

theorem bAt_cast (u v : ℚ) :
    ((bAt u v : ℚ) : ℝ) = 1 / 20000 + (-(1 / 20000)) * (u : ℝ) + (2 / 20000) * u * v := by
  simp only [bAt, mq]; push_cast; ring

theorem MAt_cast (u v : ℚ) :
    ((MAt u v : ℚ) : ℝ) = 1 / 20000 + (-(1 / 20000)) * (u : ℝ) + (1 / 20000) * u * v := by
  simp only [MAt, mq]; push_cast; ring

theorem eb1_le_half {B : B3} (h1 : 0 ≤ B.a0) (h2 : B.a0 < B.a1) (h3 : B.a1 ≤ 1)
    (_h4 : 0 ≤ B.b0) (h5 : B.b0 < B.b1) (h6 : B.b1 ≤ 1) : eb1 B ≤ 1 / 10000 := by
  simp only [eb1, bAt, mq, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem eM1_le {B : B3} (h1 : 0 ≤ B.a0) (h2 : B.a0 < B.a1) (_h3 : B.a1 ≤ 1)
    (_h4 : 0 ≤ B.b0) (h5 : B.b0 < B.b1) (h6 : B.b1 ≤ 1) : eM1 B ≤ 1 / 20000 := by
  simp only [eM1, MAt, mq, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-! ## Box soundness -/

set_option maxHeartbeats 4000000 in
/-- Soundness of one certified (non-corner) box: positivity of the cutoff-edge value at
`a = m(1-t)`, `b = m(1 + t(2z-1))`, `m = 1/20000`. -/
theorem edgeOK_sound {B : B3} {w : EWit} (hok : edgeOK B w = true) {t z : ℝ}
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ))
    (htpos : 0 < t) (htl : t < 1) (hzpos : 0 < z) (hzl : z < 1) :
    0 < canonicalPureGap (1 / 20000 * (1 - t)) (1 / 10000 - 1 / 20000 * (1 - t))
      (H (1 / 20000 * (1 - t))) (H (1 / 20000 * (1 + t * (2 * z - 1)))) := by
  simp only [edgeOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hS, hL⟩, hT⟩, hV⟩, hQ⟩ := hok
  have hS' := hS
  simp only [eShapeOK, Bool.and_eq_true, decide_eq_true_eq] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩, hs7⟩, hs8⟩ := hS'
  simp only [eLogsOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hla0, hla1⟩, hlb0⟩, hlb1⟩, hlM1⟩, hlh0⟩, hltail⟩, hllam⟩, hlrp⟩ := hL
  simp only [eThetaOK, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨hv1ok, hv1nn⟩, hv1br⟩, hv2ok⟩, hv2br⟩ := hT
  -- shape facts in ℝ
  have hs1R : (0 : ℝ) ≤ (B.a0 : ℝ) := by exact_mod_cast hs1
  have hs2R : (B.a0 : ℝ) < (B.a1 : ℝ) := by exact_mod_cast hs2
  have hs3R : (B.a1 : ℝ) ≤ 1 := by exact_mod_cast hs3
  have hs4R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hs4
  have hs5R : (B.b0 : ℝ) < (B.b1 : ℝ) := by exact_mod_cast hs5
  have hs6R : (B.b1 : ℝ) ≤ 1 := by exact_mod_cast hs6
  have hs7R : (0 : ℝ) < ((eb0 B : ℚ) : ℝ) := by exact_mod_cast hs7
  have hs8R : (0 : ℝ) < ((eM0 B : ℚ) : ℝ) := by exact_mod_cast hs8
  -- the chart
  set a : ℝ := 1 / 20000 * (1 - t) with hadef
  clear_value a
  set b : ℝ := 1 / 20000 * (1 + t * (2 * z - 1)) with hbdef
  clear_value b
  have ha : 0 < a := by rw [hadef]; nlinarith
  have htz : 0 < t * z := mul_pos htpos hzpos
  have htz' : 0 < t * (1 - z) := mul_pos htpos (by linarith)
  have hab : a < b := by rw [hadef, hbdef]; nlinarith
  have hbc : b < 1 / 10000 - a := by rw [hadef, hbdef]; nlinarith
  have hcS : 1 / 10000 - a < 1 / 2 := by rw [hadef]; nlinarith
  have hb2 : b < 1 / 2 := by linarith
  set y : ℝ := 1 / 10000 - 2 * a with hydef
  clear_value y
  have hyt : y = 1 / 10000 * t := by rw [hydef, hadef]; ring
  have hypos : 0 < y := by rw [hyt]; positivity
  have hd : b - a = z * y := by rw [hbdef, hadef, hyt]; ring
  -- box bounds
  have hA0 : ((ea0 B : ℚ) : ℝ) ≤ a := by
    simp only [ea0, mq]; push_cast; rw [hadef]; nlinarith
  have hA0' : (0 : ℝ) ≤ ((ea0 B : ℚ) : ℝ) := by
    simp only [ea0, mq]; push_cast; nlinarith
  have hA1 : a ≤ ((ea1 B : ℚ) : ℝ) := by
    simp only [ea1, mq]; push_cast; rw [hadef]; nlinarith
  have hA1' : ((ea1 B : ℚ) : ℝ) ≤ 1 / 20000 := by
    simp only [ea1, mq]; push_cast; nlinarith
  have hB0 : ((eb0 B : ℚ) : ℝ) ≤ b := by
    have := min4_le_bilin (B := B) bAt (1 / 20000) (-(1 / 20000)) (2 / 20000) bAt_cast ht0 ht1 hz0 hz1
    simp only [eb0]
    rw [hbdef]; linarith
  have hB1 : b ≤ ((eb1 B : ℚ) : ℝ) := by
    have := bilin_le_max4 (B := B) bAt (1 / 20000) (-(1 / 20000)) (2 / 20000) bAt_cast ht0 ht1 hz0 hz1
    simp only [eb1]
    rw [hbdef]; linarith
  have hB1' : ((eb1 B : ℚ) : ℝ) ≤ 1 / 10000 := by
    have := rle (eb1_le_half hs1 hs2 hs3 hs4 hs5 hs6); push_cast at this; linarith
  have hM0 : ((eM0 B : ℚ) : ℝ) ≤ (a + b) / 2 := by
    have := min4_le_bilin (B := B) MAt (1 / 20000) (-(1 / 20000)) (1 / 20000) MAt_cast ht0 ht1 hz0 hz1
    simp only [eM0]
    rw [hadef, hbdef]; linarith
  have hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ) := by
    have := bilin_le_max4 (B := B) MAt (1 / 20000) (-(1 / 20000)) (1 / 20000) MAt_cast ht0 ht1 hz0 hz1
    simp only [eM1]
    rw [hadef, hbdef]; linarith
  have hM1' : ((eM1 B : ℚ) : ℝ) ≤ 1 / 20000 := by
    have := rle (eM1_le hs1 hs2 hs3 hs4 hs5 hs6); push_cast at this; linarith
  have hY0 : ((ey0 B : ℚ) : ℝ) ≤ y := by
    simp only [ey0, Sq]; push_cast; rw [hyt]; nlinarith
  have hY1 : y ≤ ((ey1 B : ℚ) : ℝ) := by
    simp only [ey1, Sq]; push_cast; rw [hyt]; nlinarith
  have hC1 : 1 / 10000 - a ≤ ((ec1 B : ℚ) : ℝ) := by
    simp only [ec1, mq]; push_cast; rw [hadef]; nlinarith
  have hrho : (b - a) / (a + b) ≤ ((erho1 B : ℚ) : ℝ) := by
    have hd1ne : (1 - t + t * z) ≠ 0 := by nlinarith
    have habne : a + b ≠ 0 := by linarith
    have e : (b - a) / (a + b) = t * z / (1 - t + t * z) := by
      rw [div_eq_div_iff habne hd1ne, hbdef, hadef]; ring
    rw [e]
    simp only [erho1]
    push_cast
    have hd1 : 0 < 1 - t + t * z := by nlinarith
    have hz1pos : (0 : ℝ) < B.b1 := by linarith
    have hd2 : (0 : ℝ) < 1 - B.a1 + B.b1 * B.a1 := by nlinarith
    rw [div_le_div_iff₀ hd1 hd2]
    have h1 : t * z * (1 - (B.a1 : ℝ)) ≤ t * B.b1 * (1 - B.a1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz1 htpos.le) (by linarith)
    have h2 : t * (1 - (B.a1 : ℝ)) ≤ B.a1 * (1 - t) := by nlinarith
    have h3 : (B.b1 : ℝ) * (t * (1 - B.a1)) ≤ B.b1 * (B.a1 * (1 - t)) :=
      mul_le_mul_of_nonneg_left h2 hz1pos.le
    nlinarith
  have hrhop : (b - a) / (2 * (1 - (a + b) / 2)) ≤ ((erhop1 B : ℚ) : ℝ) := by
    simp only [erhop1, mq]
    push_cast
    have hden : 0 < 1 - ((eM1 B : ℚ) : ℝ) := by linarith
    rw [div_le_div_iff₀ (by linarith) hden, hd, hyt]
    have hz1pos : (0 : ℝ) ≤ B.b1 := by linarith
    have h1 : z * t ≤ (B.b1 : ℝ) * B.a1 := mul_le_mul hz1 ht1 htpos.le hz1pos
    nlinarith
  have hrhop2 : ((erhop1 B : ℚ) : ℝ) ≤ 1 / 2 := by
    have := rle hlrp; push_cast at this ⊢; linarith
  -- entropies
  have hHa0 : 0 < H a := H_pos ha (by linarith)
  have hHb0 : 0 < H b := H_pos (by linarith) (by linarith)
  have hef : H a ≤ H b := H_mono ha.le hab.le hb2.le
  have hE0 : ((ee0 B : ℚ) : ℝ) ≤ H a := by
    simp only [ee0]
    split_ifs with h0
    · push_cast; exact hHa0.le
    · have hp : ptOk (ea0 B) = true := by
        rcases hla0 with h | h
        · exact absurd h h0
        · exact h
      exact (H_bounds hp).1.trans (H_mono hA0' hA0 (by linarith))
  have hE0' : (0 : ℝ) ≤ ((ee0 B : ℚ) : ℝ) := by
    simp only [ee0]
    split_ifs with h0
    · push_cast; exact le_refl _
    · have hp : ptOk (ea0 B) = true := by
        rcases hla0 with h | h
        · exact absurd h h0
        · exact h
      simp only [Hlo]
      split_ifs with hh
      · have := rle hh
        have hL := log_two_mem
        push_cast at this ⊢
        exact div_nonneg this (by linarith [LqLo_pos])
      · push_cast; exact le_refl _
  have hE1 : H a ≤ ((ee1 B : ℚ) : ℝ) := (H_mono ha.le hA1 (by linarith)).trans (H_bounds hla1).2
  have hF0 : ((ef0 B : ℚ) : ℝ) ≤ H b :=
    (H_bounds hlb0).1.trans (H_mono hs7R.le hB0 hb2.le)
  have hF1 : H b ≤ ((ef1 B : ℚ) : ℝ) :=
    (H_mono (by linarith) hB1 (by linarith)).trans (H_bounds hlb1).2
  set e : ℝ := H a with hedef
  clear_value e
  set f : ℝ := H b with hfdef
  clear_value f
  set h : ℝ := (e + f) / 2 with hhdef
  clear_value h
  have hH0 : ((eh0 B : ℚ) : ℝ) ≤ h := by
    simp only [eh0]; push_cast; rw [hhdef]; linarith
  have hH1 : h ≤ ((eh1 B : ℚ) : ℝ) := by
    simp only [eh1]; push_cast; rw [hhdef]; linarith
  have hH0p : (0 : ℝ) < ((eh0 B : ℚ) : ℝ) := rpos hlh0
  have hhpos : 0 < h := by linarith
  -- Theta at Xbar
  have hXbar : ((eXbar B : ℚ) : ℝ) = ((ey1 B : ℚ) : ℝ) / (2 * ((eh0 B : ℚ) : ℝ)) := by
    simp only [eXbar]; push_cast; ring
  have hY1p : (0 : ℝ) < ((ey1 B : ℚ) : ℝ) := hypos.trans_le hY1
  have hXbarp : (0 : ℝ) < ((eXbar B : ℚ) : ℝ) := by rw [hXbar]; positivity
  have hX : y / (2 * h) ≤ ((eXbar B : ℚ) : ℝ) := by
    rw [hXbar, div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul hY1 (by linarith only [hH0]) (by positivity) hY1p.le
  have hκ : ((slopeLo w.v1 : ℚ) : ℝ) ≤ e8Theta ((eXbar B : ℚ) : ℝ) := by
    apply theta_ge hXbarp hv1ok
    have := rle hv1br; push_cast at this ⊢; linarith
  have hκ0 : (0 : ℝ) ≤ ((slopeLo w.v1 : ℚ) : ℝ) := rnn hv1nn
  -- main pointwise bound
  have hmain := edge_main_lb (S := 1 / 10000) (X := ((eXbar B : ℚ) : ℝ)) ha hab hbc hcS
    (by rw [← hydef, ← hedef, ← hfdef, ← hhdef]; exact hX)
  rw [← hydef, ← hedef, ← hfdef, ← hhdef] at hmain
  obtain ⟨hqa, hqM, -, -⟩ := q_facts ha hab.le hb2
  rw [← hedef, ← hfdef, ← hhdef] at hqa hqM
  set q : ℝ := entropyInverse h with hqdef
  clear_value q
  have hq2 : q < 1 / 2 := by linarith
  -- T1
  have hT1 := T1_bound (y := y) (d := b - a) (sub_pos.mpr hab).le (by linarith) hhpos hH1
    hXbarp hκ hκ0
  -- T2
  have hT2 := T2_sound hV ha hab hb2 hypos hd hzpos.le hM1 hA1 (by linarith) hB0 (rpos hs7) hlb0 hY1
  -- T3
  have hXq : 0 < (1 - 2 * q) / (2 * h) := by
    have : 0 < 1 - 2 * q := by linarith
    positivity
  have hXhat : ((eXhat B : ℚ) : ℝ) = 1 / (2 * ((eh0 B : ℚ) : ℝ)) := by
    simp only [eXhat]; push_cast; ring
  have hXqle : (1 - 2 * q) / (2 * h) ≤ ((eXhat B : ℚ) : ℝ) := by
    rw [hXhat, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq0 : 0 ≤ q := by linarith only [hqa, ha]
    exact mul_le_mul (by linarith only [hq0]) (by linarith only [hH0]) (by positivity)
      (by norm_num)
  have hΘ1 : e8Theta ((1 - 2 * q) / (2 * h)) ≤ ((slopeHi w.v2 : ℚ) : ℝ) := by
    refine (theta_mono hXq hXqle).trans ?_
    apply theta_le (by rw [hXhat]; positivity) hv2ok
    have := rle hv2br; push_cast at this ⊢; linarith
  have hΘ0 : 0 ≤ e8Theta ((1 - 2 * q) / (2 * h)) := (e8Theta_pos hXq).le
  have hJMp : (0 : ℝ) < ((eJM1 B : ℚ) : ℝ) := by
    simp only [eJM1]; push_cast
    exact div_pos (rpos hllam) (by linarith [log_two_mem.2, Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hJM : ((eJM1 B : ℚ) : ℝ) ≤ J ((a + b) / 2) := by
    simp only [eJM1]
    have h1 := J_ge hlM1 (le_of_lt hllam)
    have h2 := J_anti (by linarith) hM1 (by linarith)
    push_cast at h1 ⊢
    linarith
  have hT3 := T3_sound hV ha hab hb2 hypos hd hΘ0 hΘ1 hM0 (rpos hs8) hM1 (by linarith) hJM hJMp
    hrho hrhop hrhop2 hY0
  rw [← hedef, ← hfdef, ← hhdef, ← hqdef] at hT3
  -- T4
  set c : ℝ := 1 / 10000 - a with hcdef
  clear_value c
  have hcb : c - b = y * (1 - z) := by rw [hcdef, hbdef, hyt, hadef]; ring
  have hcq : c - q ≤ y := by rw [hcdef, hydef]; linarith
  have hc1' : 0 < 1 - 2 * ((ec1 B : ℚ) : ℝ) := by
    have := rle hltail; push_cast at this
    have hf1p : 0 < ((ef1 B : ℚ) : ℝ) := hHb0.trans_le hF1
    linarith
  have hqc : q ≤ c := by rw [hcdef]; linarith
  have hXc : 0 < (1 - 2 * c) / (2 * f) := by
    have : 0 < 1 - 2 * c := by linarith
    positivity
  have hXc128 : 128 ≤ (1 - 2 * c) / (2 * f) := by
    have ht := rle hltail; push_cast at ht
    rw [le_div_iff₀ (by positivity)]
    linarith only [ht, hF1, hC1]
  have hXcq : (1 - 2 * c) / (2 * f) ≤ (1 - 2 * q) / (2 * h) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 < 1 - 2 * c := by linarith
    have hhf : h ≤ f := by rw [hhdef]; linarith only [hef]
    exact mul_le_mul (by linarith only [hqc]) (by linarith only [hhf]) (by positivity)
      (by linarith only [hq2])
  have hΘtail := theta_increment_tail hXc128 hXcq
  have hΘmono := theta_mono hXc hXcq
  have hfe : f - e ≤ J a * (b - a) := by
    rw [hedef, hfdef]; exact H_sub_le_J ha hab.le (by linarith)
  have hJa : ∀ _ : 0 < ((ea0 B : ℚ) : ℝ), ptOk (ea0 B) = true →
      J a ≤ ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
    intro h0 hp
    exact (J_anti h0 hA0 (by linarith)).trans (J_le hp (by linarith))
  have hJa0 : 0 ≤ J a := (J_pos ha (by linarith)).le
  have hT4 := T4_sound hV hab hypos hd hzl.le hcb hcq hC1 hc1' hqc hE0 hE0' hef hF1 hhdef hH0 hH0p
    hfe hJa hJa0 hY0 hΘtail
  -- polynomial positivity
  have hP := qposOK_sound hQ hz0 hz1
  have hy2 : 0 < y ^ 2 := by positivity
  have hPy := mul_pos hy2 hP
  have eP : y ^ 2 * (((eP0 B w : ℚ) : ℝ) + ((eP1 B w : ℚ) : ℝ) * z + ((eP2 B w : ℚ) : ℝ) * z ^ 2) =
      ((slopeLo w.v1 : ℚ) : ℝ) / ((eXbar B : ℚ) : ℝ) / (4 * ((eh1 B : ℚ) : ℝ)) *
          (y ^ 2 - (b - a) ^ 2) +
        y ^ 2 * (((eT2 B w).1 : ℝ) * z + ((eT2 B w).2 : ℝ) * z ^ 2) -
        y ^ 2 * (((eT3 B w).1 : ℝ) + ((eT3 B w).2 : ℝ) * z ^ 2) -
        y ^ 2 * (((eT4 B w).1 : ℝ) + ((eT4 B w).2.1 : ℝ) * z + ((eT4 B w).2.2 : ℝ) * z ^ 2) := by
    rw [hd]
    simp only [eP0, eP1, eP2, eA]
    push_cast
    ring
  have hre : (2 * q - 1 / 10000) * e8Theta ((1 - 2 * q) / (2 * h)) +
      (c - b) * e8Theta ((1 - 2 * c) / (2 * f)) =
      -((a + b - 2 * q) * e8Theta ((1 - 2 * q) / (2 * h))) -
        (c - b) * (e8Theta ((1 - 2 * q) / (2 * h)) - e8Theta ((1 - 2 * c) / (2 * f))) := by
    rw [hcdef]; ring
  linarith only [hmain, hT1, hT2, hT3, hT4, hre, eP, hPy]

end CKLaneN1.Edge
