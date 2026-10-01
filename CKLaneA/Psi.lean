import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lane A: the even analytic function `ψ(y) = atanh(y)/y`

`psi y = ∑ y^(2k)/(2k+1)`, with its first two derivatives as explicit series.
It is smooth on `(-1,1)` including `y = 0`, and `2*y*psi y = log(1+y) - log(1-y)`.
-/

namespace CKLaneA
open Real Finset

noncomputable def psiT (k : ℕ) (y : ℝ) : ℝ := y ^ (2 * k) / (2 * k + 1)
noncomputable def psiT1 (k : ℕ) (y : ℝ) : ℝ := ((2 * k : ℕ) : ℝ) * y ^ (2 * k - 1) / (2 * k + 1)
noncomputable def psiT2 (k : ℕ) (y : ℝ) : ℝ :=
  ((2 * k : ℕ) : ℝ) * (((2 * k - 1 : ℕ) : ℝ) * y ^ (2 * k - 1 - 1)) / (2 * k + 1)

noncomputable def psi (y : ℝ) : ℝ := ∑' k : ℕ, psiT k y
noncomputable def psi1 (y : ℝ) : ℝ := ∑' k : ℕ, psiT1 k y
noncomputable def psi2 (y : ℝ) : ℝ := ∑' k : ℕ, psiT2 k y

theorem hasDerivAt_psiT (k : ℕ) (y : ℝ) : HasDerivAt (psiT k) (psiT1 k y) y := by
  have h := (hasDerivAt_pow (2 * k) y).div_const (2 * (k : ℝ) + 1)
  unfold psiT psiT1
  convert h using 1

theorem hasDerivAt_psiT1 (k : ℕ) (y : ℝ) : HasDerivAt (psiT1 k) (psiT2 k y) y := by
  have h := ((hasDerivAt_pow (2 * k - 1) y).const_mul (((2 * k : ℕ) : ℝ))).div_const
    (2 * (k : ℝ) + 1)
  unfold psiT1 psiT2
  convert h using 1

private theorem den_pos (k : ℕ) : (0 : ℝ) < 2 * k + 1 := by positivity

private theorem coef1_le (k : ℕ) : ((2 * k : ℕ) : ℝ) / (2 * k + 1) ≤ 1 := by
  rw [div_le_one (den_pos k)]; push_cast; linarith

/-- geometric-type bound used for all three series -/
private theorem pow_le_geom {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (m k : ℕ)
    (hmk : k ≤ m) : |y| ^ m ≤ r ^ k := by
  calc |y| ^ m ≤ r ^ m := pow_le_pow_left₀ (abs_nonneg y) hy m
    _ ≤ r ^ k := pow_le_pow_of_le_one hr0.le hr1.le hmk

theorem abs_psiT1_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (k : ℕ) :
    |psiT1 k y| ≤ r ^ k / r := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [psiT1]; positivity
  · have h1 : |psiT1 k y| ≤ |y| ^ (2 * k - 1) := by
      unfold psiT1
      rw [abs_div, abs_mul, abs_pow, abs_of_pos (den_pos k),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * k : ℕ) : ℝ))]
      have := coef1_le k
      calc ((2 * k : ℕ) : ℝ) * |y| ^ (2 * k - 1) / (2 * k + 1)
          = (((2 * k : ℕ) : ℝ) / (2 * k + 1)) * |y| ^ (2 * k - 1) := by ring
        _ ≤ 1 * |y| ^ (2 * k - 1) := by gcongr
        _ = |y| ^ (2 * k - 1) := one_mul _
    have h2 : |y| ^ (2 * k - 1) ≤ r ^ (k - 1) := pow_le_geom hr0 hr1 hy _ _ (by omega)
    have h3 : r ^ (k - 1) = r ^ k / r := by
      rw [eq_div_iff hr0.ne', ← pow_succ]; congr 1; omega
    linarith [h3 ▸ h2]

theorem abs_psiT2_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (k : ℕ) :
    |psiT2 k y| ≤ 2 * ((k : ℝ) * r ^ k) / r ^ 2 := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · have : k = 0 := by omega
    subst this; simp [psiT2]
  · have hc1 : (((2 * k - 1 : ℕ) : ℝ)) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (den_pos k)]
      have : ((2 * k - 1 : ℕ) : ℝ) = 2 * k - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; linarith
    have h1 : |psiT2 k y| ≤ 2 * k * |y| ^ (2 * k - 1 - 1) := by
      unfold psiT2
      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos (den_pos k),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * k : ℕ) : ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * k - 1 : ℕ) : ℝ))]
      have e : ((2 * k : ℕ) : ℝ) = 2 * k := by push_cast; ring
      rw [e]
      calc 2 * (k:ℝ) * (((2 * k - 1 : ℕ) : ℝ) * |y| ^ (2 * k - 1 - 1)) / (2 * k + 1)
          = 2 * k * |y| ^ (2 * k - 1 - 1) * ((((2 * k - 1 : ℕ) : ℝ)) / (2 * k + 1)) := by ring
        _ ≤ 2 * k * |y| ^ (2 * k - 1 - 1) * 1 := by gcongr
        _ = _ := mul_one _
    have h2 : |y| ^ (2 * k - 1 - 1) ≤ r ^ (k - 1 - 1) := pow_le_geom hr0 hr1 hy _ _ (by omega)
    have h3 : r ^ (k - 1 - 1) ≤ r ^ k / r ^ 2 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this
        rw [le_div_iff₀ (by positivity)]; simp
        nlinarith [hr0, hr1]
      · rw [le_div_iff₀ (by positivity), ← pow_add]; exact le_of_eq (by congr 1; omega)
    calc |psiT2 k y| ≤ 2 * k * |y| ^ (2 * k - 1 - 1) := h1
      _ ≤ 2 * k * (r ^ k / r ^ 2) := by gcongr; exact h2.trans h3
      _ = _ := by ring

theorem summable_bound1 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun k : ℕ => r ^ k / r) :=
  (summable_geometric_of_lt_one hr0.le hr1).div_const r

theorem summable_bound2 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun k : ℕ => 2 * ((k : ℝ) * r ^ k) / r ^ 2) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  simp only [pow_one] at h
  exact (h.mul_left 2).div_const (r ^ 2)

theorem summable_psiT_zero : Summable (fun k : ℕ => psiT k 0) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  have : k ≠ 0 := by simpa using hk
  simp [psiT, this]

theorem summable_psiT1_zero : Summable (fun k : ℕ => psiT1 k 0) := by
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have : 2 * k - 1 ≠ 0 := by omega
  simp [psiT1, zero_pow this]

private theorem abs_lt_one_mid {y : ℝ} (hy : |y| < 1) :
    0 < (|y| + 1) / 2 ∧ (|y| + 1) / 2 < 1 ∧ |y| < (|y| + 1) / 2 := by
  have := abs_nonneg y
  refine ⟨by linarith, by linarith, by linarith⟩

theorem hasDerivAt_psi {y : ℝ} (hy : |y| < 1) : HasDerivAt psi (psi1 y) y := by
  obtain ⟨hr0, hr1, hyr⟩ := abs_lt_one_mid hy
  set r := (|y| + 1) / 2
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hmem : y ∈ Set.Ioo (-r) r := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have h0 : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr0⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_bound1 hr0 hr1) hopen
    (convex_Ioo (-r) r).isPreconnected (fun k z _ => hasDerivAt_psiT k z)
    (fun k z hz => by
      rw [Real.norm_eq_abs]
      exact abs_psiT1_le hr0 hr1 (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k)
    h0 summable_psiT_zero hmem

theorem hasDerivAt_psi1 {y : ℝ} (hy : |y| < 1) : HasDerivAt psi1 (psi2 y) y := by
  obtain ⟨hr0, hr1, hyr⟩ := abs_lt_one_mid hy
  set r := (|y| + 1) / 2
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hmem : y ∈ Set.Ioo (-r) r := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have h0 : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr0⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_bound2 hr0 hr1) hopen
    (convex_Ioo (-r) r).isPreconnected (fun k z _ => hasDerivAt_psiT1 k z)
    (fun k z hz => by
      rw [Real.norm_eq_abs]
      exact abs_psiT2_le hr0 hr1 (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k)
    h0 summable_psiT1_zero hmem

/-! ## Summability and the logarithm identity -/

theorem abs_psiT_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (k : ℕ) :
    |psiT k y| ≤ r ^ k := by
  unfold psiT
  rw [abs_div, abs_pow, abs_of_pos (den_pos k)]
  have h1 : |y| ^ (2 * k) / (2 * k + 1) ≤ |y| ^ (2 * k) := by
    apply div_le_self (by positivity)
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact h1.trans (pow_le_geom hr0 hr1 hy _ _ (by omega))

theorem summable_psiT {y : ℝ} (hy : |y| < 1) : Summable (fun k => psiT k y) := by
  obtain ⟨hr0, hr1, hyr⟩ := abs_lt_one_mid hy
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one hr0.le hr1)
    (fun k => by rw [Real.norm_eq_abs]; exact abs_psiT_le hr0 hr1 hyr.le k)

theorem summable_psiT1 {y : ℝ} (hy : |y| < 1) : Summable (fun k => psiT1 k y) := by
  obtain ⟨hr0, hr1, hyr⟩ := abs_lt_one_mid hy
  exact Summable.of_norm_bounded (summable_bound1 hr0 hr1)
    (fun k => by rw [Real.norm_eq_abs]; exact abs_psiT1_le hr0 hr1 hyr.le k)

theorem summable_psiT2 {y : ℝ} (hy : |y| < 1) : Summable (fun k => psiT2 k y) := by
  obtain ⟨hr0, hr1, hyr⟩ := abs_lt_one_mid hy
  exact Summable.of_norm_bounded (summable_bound2 hr0 hr1)
    (fun k => by rw [Real.norm_eq_abs]; exact abs_psiT2_le hr0 hr1 hyr.le k)

theorem two_mul_psi {y : ℝ} (hy : |y| < 1) :
    2 * y * psi y = Real.log (1 + y) - Real.log (1 - y) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one hy
  have hs := (summable_psiT hy).hasSum.mul_left (2 * y)
  have heq : (fun k => 2 * y * psiT k y) = (fun k : ℕ => 2 * (1 / (2 * (k:ℝ) + 1)) * y ^ (2 * k + 1)) := by
    funext k; unfold psiT; rw [pow_succ]; field_simp
  rw [heq] at hs
  exact hs.unique h

/-! ## Tail bounds -/

theorem tail_bound {f : ℕ → ℝ} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (hf : ∀ k, |f (k + N)| ≤ C * q ^ k) :
    |∑' k, f (k + N)| ≤ C / (1 - q) := by
  have hC : 0 ≤ C := by
    have := hf 0
    simp at this
    exact (abs_nonneg _).trans this
  have hsum : Summable (fun k => C * q ^ k) := (summable_geometric_of_lt_one hq0 hq1).mul_left C
  have hsf : Summable (fun k => f (k + N)) :=
    Summable.of_norm_bounded hsum (fun k => by rw [Real.norm_eq_abs]; exact hf k)
  have habs : Summable (fun k => |f (k + N)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hf hsum
  calc |∑' k, f (k + N)| ≤ ∑' k, |f (k + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun k => f (k + N)) (by simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k, C * q ^ k := by
        exact hsf.abs.tsum_le_tsum hf hsum
    _ = C / (1 - q) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]; ring

theorem psi_split {y : ℝ} (hy : |y| < 1) (N : ℕ) :
    psi y = (∑ k ∈ range N, psiT k y) + ∑' k, psiT (k + N) y :=
  ((summable_psiT hy).sum_add_tsum_nat_add N).symm

theorem psi1_split {y : ℝ} (hy : |y| < 1) (N : ℕ) :
    psi1 y = (∑ k ∈ range N, psiT1 k y) + ∑' k, psiT1 (k + N) y :=
  ((summable_psiT1 hy).sum_add_tsum_nat_add N).symm

theorem psi2_split {y : ℝ} (hy : |y| < 1) (N : ℕ) :
    psi2 y = (∑ k ∈ range N, psiT2 k y) + ∑' k, psiT2 (k + N) y :=
  ((summable_psiT2 hy).sum_add_tsum_nat_add N).symm

theorem psiT_tail_term {r y : ℝ} (hy : |y| ≤ r) (N k : ℕ) :
    |psiT (k + N) y| ≤ r ^ (2 * N) * (r ^ 2) ^ k := by
  unfold psiT
  rw [abs_div, abs_pow, abs_of_pos (den_pos _)]
  have h1 : |y| ^ (2 * (k + N)) / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ |y| ^ (2 * (k + N)) := by
    apply div_le_self (by positivity)
    have : (0:ℝ) ≤ ((k + N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : |y| ^ (2 * (k + N)) ≤ r ^ (2 * (k + N)) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have h3 : r ^ (2 * (k + N)) = r ^ (2 * N) * (r ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  linarith

theorem psiT1_tail_term {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (N k : ℕ)
    (hN : 1 ≤ N) : |psiT1 (k + N) y| ≤ r ^ (2 * N - 1) * (r ^ 2) ^ k := by
  have h1 : |psiT1 (k + N) y| ≤ |y| ^ (2 * (k + N) - 1) := by
    unfold psiT1
    rw [abs_div, abs_mul, abs_pow, abs_of_pos (den_pos _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * (k + N) : ℕ) : ℝ))]
    have := coef1_le (k + N)
    calc ((2 * (k + N) : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1) / (2 * ((k + N : ℕ) : ℝ) + 1)
        = (((2 * (k + N) : ℕ) : ℝ) / (2 * ((k + N : ℕ) : ℝ) + 1)) * |y| ^ (2 * (k + N) - 1) := by ring
      _ ≤ 1 * |y| ^ (2 * (k + N) - 1) := by gcongr
      _ = _ := one_mul _
  have h2 : |y| ^ (2 * (k + N) - 1) ≤ r ^ (2 * (k + N) - 1) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have h3 : r ^ (2 * (k + N) - 1) = r ^ (2 * N - 1) * (r ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  linarith

theorem psiT2_tail_term {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hy : |y| ≤ r) (N k : ℕ)
    (hN : 1 ≤ N) : |psiT2 (k + N) y| ≤ (2 * N * r ^ (2 * N - 2)) * (2 * r ^ 2) ^ k := by
  have hc1 : (((2 * (k + N) - 1 : ℕ) : ℝ)) / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (den_pos _)]
    have : ((2 * (k + N) - 1 : ℕ) : ℝ) = 2 * ((k + N : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; linarith
  have h1 : |psiT2 (k + N) y| ≤ 2 * ((k + N : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1 - 1) := by
    unfold psiT2
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos (den_pos _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * (k + N) : ℕ) : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * (k + N) - 1 : ℕ) : ℝ))]
    have e : ((2 * (k + N) : ℕ) : ℝ) = 2 * ((k + N : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    calc 2 * ((k + N : ℕ) : ℝ) * (((2 * (k + N) - 1 : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1 - 1)) /
          (2 * ((k + N : ℕ) : ℝ) + 1)
        = 2 * ((k + N : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1 - 1) *
          ((((2 * (k + N) - 1 : ℕ) : ℝ)) / (2 * ((k + N : ℕ) : ℝ) + 1)) := by ring
      _ ≤ 2 * ((k + N : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1 - 1) * 1 := by gcongr
      _ = _ := mul_one _
  have h2 : |y| ^ (2 * (k + N) - 1 - 1) ≤ r ^ (2 * (k + N) - 1 - 1) :=
    pow_le_pow_left₀ (abs_nonneg y) hy _
  have h3 : r ^ (2 * (k + N) - 1 - 1) = r ^ (2 * N - 2) * (r ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have h4 : ((k + N : ℕ) : ℝ) ≤ N * 2 ^ k := by
    have key : ∀ k : ℕ, k + N ≤ N * 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        have : 1 ≤ N * 2 ^ k := by
          have := Nat.one_le_two_pow (n := k)
          nlinarith
        nlinarith
    exact_mod_cast key k
  have hr2 : 0 ≤ r ^ (2 * N - 2) := by positivity
  have hrk : 0 ≤ (r ^ 2) ^ k := by positivity
  calc |psiT2 (k + N) y| ≤ 2 * ((k + N : ℕ) : ℝ) * |y| ^ (2 * (k + N) - 1 - 1) := h1
    _ ≤ 2 * ((k + N : ℕ) : ℝ) * (r ^ (2 * N - 2) * (r ^ 2) ^ k) := by
        gcongr; exact h3 ▸ h2
    _ ≤ 2 * (N * 2 ^ k) * (r ^ (2 * N - 2) * (r ^ 2) ^ k) := by gcongr
    _ = (2 * N * r ^ (2 * N - 2)) * (2 * r ^ 2) ^ k := by rw [mul_pow]; ring

end CKLaneA
