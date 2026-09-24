import GeneralCK.BellmanStatement
import GeneralCK.ProfileBasics

namespace GeneralCK.CubeAnalysis
open scoped BigOperators

noncomputable def mean {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, v x

def slice {n : ℕ} (v : Cube (n+1) → ℝ) (b : Bool) : Cube n → ℝ :=
  fun x => v (Fin.cons b x)

def consEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n+1) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, Fin.tail x)
  left_inv x := by cases x; simp
  right_inv x := by simp

theorem sum_slices {n : ℕ} (v : Cube (n+1) → ℝ) :
    ∑ x, v x = (∑ x, slice v false x) + ∑ x, slice v true x := by
  have h := (consEquiv n).sum_comp v
  simpa [consEquiv, slice, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h.symm

theorem mean_succ {n : ℕ} (v : Cube (n+1) → ℝ) :
    mean v = (mean (slice v false) + mean (slice v true)) / 2 := by
  unfold mean
  rw [sum_slices]
  simp only [zpow_neg, zpow_natCast, pow_succ, mul_inv_rev]
  ring

theorem mean_zero (v : Cube 0 → ℝ) (x : Cube 0) : mean v = v x := by
  have he (y : Cube 0) : v y = v x := congrArg v (Subsingleton.elim _ _)
  simp [mean, he, Cube]

theorem mean_const (n : ℕ) (c : ℝ) : mean (fun _ : Cube n => c) = c := by
  simp [mean, Cube, zpow_neg, zpow_natCast]

theorem mean_mono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x ≤ w x) : mean v ≤ mean w := by
  unfold mean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_strictMono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x < w x) :
    mean v < mean w := by
  unfold mean
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ => h x

theorem mean_interior {n : ℕ} {v : Cube n → ℝ} (h : ∀ x, 0 < v x ∧ v x < 1) :
    0 < mean v ∧ mean v < 1 := by
  constructor
  · simpa only [mean_const] using mean_strictMono (fun x => (h x).1)
  · simpa only [mean_const] using mean_strictMono (fun x => (h x).2)

/-- Recursive edge energy, with the same normalization as manuscript Lemma 1.3. -/
noncomputable def energy : (n : ℕ) → (Cube n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, v => (energy n (slice v false) + energy n (slice v true)) / 2 +
      mean (fun x => interiorCost (slice v false x) (slice v true x))

/-- Reindex the stated Fin-valued Bellman premise along any finite enumeration. -/
theorem bellman_fintype (hB : FiniteHybridBellman) {α : Type*} [Fintype α]
    (w u v : α → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i ∧ u i < 1) (hv : ∀ i, 0 < v i ∧ v i < 1) :
    B (((∑ i, w i * u i) + ∑ i, w i * v i) / 2)
      (((∑ i, w i * H (u i)) + ∑ i, w i * H (v i)) / 2) ≤
    (B (∑ i, w i * u i) (∑ i, w i * H (u i)) +
      B (∑ i, w i * v i) (∑ i, w i * H (v i))) / 2 +
      ∑ i, w i * interiorCost (u i) (v i) := by
  classical
  let e := (Fintype.equivFin α).symm
  have reindex (f : α → ℝ) : (∑ i, f (e i)) = ∑ i, f i := e.sum_comp f
  have hh := hB (Fintype.card α) (w ∘ e) (u ∘ e) (v ∘ e)
    (fun i => hw (e i)) (by simpa only [Function.comp_apply, reindex] using hs)
    (fun i => hu (e i)) (fun i => hv (e i))
  dsimp only [Function.comp_apply] at hh
  rw [reindex (fun i => w i * u i), reindex (fun i => w i * v i),
    reindex (fun i => w i * H (u i)), reindex (fun i => w i * H (v i)),
    reindex (fun i => w i * interiorCost (u i) (v i))] at hh
  exact hh

theorem bellman_uniform (hB : FiniteHybridBellman) {n : ℕ} (u v : Cube n → ℝ)
    (hu : ∀ x, 0 < u x ∧ u x < 1) (hv : ∀ x, 0 < v x ∧ v x < 1) :
    B ((mean u + mean v) / 2) ((mean (H ∘ u) + mean (H ∘ v)) / 2) ≤
      (B (mean u) (mean (H ∘ u)) + B (mean v) (mean (H ∘ v))) / 2 +
      mean (fun x => interiorCost (u x) (v x)) := by
  have hw : (∑ _ : Cube n, (2 : ℝ) ^ (-(n : ℤ))) = 1 := by
    simp [Cube, zpow_neg, zpow_natCast]
  have h := bellman_fintype hB (fun _ => (2 : ℝ) ^ (-(n : ℤ))) u v
      (fun _ => by positivity) hw hu hv
  simpa only [← Finset.mul_sum, mean, Function.comp_apply] using h

/-- Manuscript Lemma 1.3, assuming only its stated hybrid Bellman premise. -/
theorem static_induction (hB : FiniteHybridBellman) (n : ℕ) (v : Cube n → ℝ)
    (hv : ∀ x, 0 < v x ∧ v x < 1) :
    B (mean v) (mean (H ∘ v)) ≤ energy n v := by
  induction n with
  | zero =>
    rw [mean_zero v default, mean_zero (H ∘ v) default]
    simpa [energy] using (B_H (hv default).1 (hv default).2).le
  | succ n ih =>
    have hfalse := ih (slice v false) (fun x => hv (Fin.cons false x))
    have htrue := ih (slice v true) (fun x => hv (Fin.cons true x))
    have hb := bellman_uniform hB (slice v false) (slice v true)
      (fun x => hv (Fin.cons false x)) (fun x => hv (Fin.cons true x))
    rw [mean_succ v, mean_succ (H ∘ v)]
    change B ((mean (slice v false) + mean (slice v true)) / 2)
      ((mean (H ∘ slice v false) + mean (H ∘ slice v true)) / 2) ≤ _
    dsimp only [energy]
    linarith

end GeneralCK.CubeAnalysis
