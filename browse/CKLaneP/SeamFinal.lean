/-
Lane P — seam assembly pieces:

* `tlistOK` / `tlistOK_sound` : a list of T-cells covering `κ = H p/H q ∈ [0, 1]` gives the
  small-scale lemma `∀ p q, 0 < p → p < q → q ≤ qT → SeamAt p q`.
* `seam_exclusion_of_box` : the root box `SeamBox 0 (S/2) 0 2` implies
  `StrictSeamMinimizerExclusion (1/10000)` (the seam field, up to unfolding `retainedCutoff`).
Both are conditional on their hypotheses; the certificates discharge them.
-/
import CKLaneP.SeamTree
import CKLaneP.SeamTCheck
import GeneralCK.SmallMeanPhiRetainedCutoff

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- Consecutive T-cells: the first starts at `k`, each next starts where the previous ends,
the last ends at `≥ 1`; all share `qT`. -/
def tlistOK (qT : ℚ) : ℚ → List (ℕ × TCell) → Bool
  | k, [] => decide (1 ≤ k)
  | k, (kind, c) :: rest => (decide (c.qT = qT ∧ c.k0 = k) && tcheck kind c) && tlistOK qT c.k1 rest

theorem tlistOK_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ) :
    ∀ (L : List (ℕ × TCell)) (k : ℚ), tlistOK qT k L = true →
    ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → ((k : ℚ) : ℝ) ≤ H p / H q → SeamAt p q := by
  intro L
  induction L with
  | nil =>
      intro k h p q hp hpq _ hk ys _ hysq hysS _
      have hk1 : (1 : ℚ) ≤ k := of_decide_eq_true h
      have hk1R : (1 : ℝ) ≤ ((k : ℚ) : ℝ) := by exact_mod_cast hk1
      exfalso
      have hq12 : q ≤ 1 / 2 := by linarith
      have hHpq : H p < H q := H_strictMonoOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, hq12⟩ hpq
      have hHp : 0 < H p := H_pos hp (by linarith)
      have hHq : 0 < H q := hHp.trans hHpq
      have : H p / H q < 1 := by rw [div_lt_one hHq]; exact hHpq
      linarith
  | cons hd rest ih =>
      obtain ⟨kind, c⟩ := hd
      intro k h p q hp hpq hqT hk
      simp only [tlistOK, Bool.and_eq_true] at h
      obtain ⟨⟨hkc, htc⟩, hrest⟩ := h
      obtain ⟨hcq, hck⟩ := of_decide_eq_true hkc
      rcases le_total (H p / H q) ((c.k1 : ℚ) : ℝ) with h1 | h1
      · intro ys hys0 _ hysS hstat
        have hqT' : q ≤ ((c.qT : ℚ) : ℝ) := by rw [hcq]; exact hqT
        have hk' : ((c.k0 : ℚ) : ℝ) ≤ H p / H q := by rw [hck]; exact hk
        exact tcheck_sound hdouble kind c htc hp hpq hqT' hk' h1 hys0 hysS hstat
      · exact ih c.k1 hrest p q hp hpq hqT h1

/-- The small-scale seam lemma from a checked T-list starting at `κ = 0`. -/
theorem seamT_of_list (hdouble : CanonicalDoubleCapEntropyEndpoints) (qT : ℚ)
    (L : List (ℕ × TCell)) (hL : tlistOK qT 0 L = true) :
    ∀ p q : ℝ, 0 < p → p < q → q ≤ ((qT : ℚ) : ℝ) → SeamAt p q := by
  intro p q hp hpq hqT ys hys0 hysq hysS hstat
  have hq1 : q ≤ 1 := by linarith
  have hk : (((0 : ℚ) : ℚ) : ℝ) ≤ H p / H q := by
    push_cast
    exact div_nonneg (H_nonneg hp.le (by linarith)) (H_nonneg (hp.trans hpq).le hq1)
  exact tlistOK_sound hdouble qT L 0 hL p q hp hpq hqT hk ys hys0 hysq hysS hstat

/-- The seam field (with the cutoff unfolded) from the root box. -/
theorem seam_exclusion_of_box (hbox : SeamBox 0 (1 / 20000) 0 2) :
    StrictSeamMinimizerExclusion (1 / 10000) := by
  intro a c e f he hf hef hmem hsum hac hc hea hfc hres hneg
  obtain ⟨⟨ha0, -, hc12, -, -⟩, -⟩ := hmem
  have hHmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → y ≤ 1 / 2 → H x ≤ H y :=
    fun hx hxy hy => H_strictMonoOn.monotoneOn ⟨hx, by linarith⟩ ⟨hx.trans hxy, hy⟩ hxy
  have he1 : e ≤ 1 := le_trans hea.le (H_le_one a)
  have hf1 : f ≤ 1 := le_trans hfc.le (H_le_one c)
  obtain ⟨hp0, hp12, hHp⟩ := entropyInverse_spec he.le he1
  obtain ⟨hq0, hq12, hHq⟩ := entropyInverse_spec hf.le hf1
  set p := entropyInverse e with hpdef
  set q := entropyInverse f with hqdef
  have hp : 0 < p := entropyInverse_pos he he1
  have hpa : p < a := by
    by_contra hcon
    push Not at hcon
    have := hHmono ha0 hcon hp12
    rw [hHp] at this
    linarith
  have hqc : q < c := by
    by_contra hcon
    push Not at hcon
    have := hHmono (ha0.trans hac.le) hcon hq12
    rw [hHq] at this
    linarith
  have hpq : p < q := by
    by_contra hcon
    push Not at hcon
    have := hHmono hq0 hcon hp12
    rw [hHp, hHq] at this
    linarith
  set ys := c - a with hys
  have hys0 : 0 < ys := by rw [hys]; linarith
  have hysq : 2 * q - 1 / 10000 < ys := by rw [hys]; linarith
  have hysS : ys < 1 / 10000 - 2 * p := by rw [hys]; linarith
  have hstat : seamD (1 / 10000) (H p) (H q) ys = 0 := by
    rw [hHp, hHq]
    have e1 : 1 - 1 / 10000 + ys = 1 - 2 * a := by rw [hys]; linarith
    have e2 : 1 - 1 / 10000 - ys = 1 - 2 * c := by rw [hys]; linarith
    unfold seamD
    rw [e1, e2]
    linarith
  have hbox' := hbox p q hp hpq (by push_cast; exact hp.le) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) ys hys0 hysq hysS hstat
  have hcurve : seamCurve (1 / 10000) (H p) (H q) ys = canonicalPureGap a c e f := by
    unfold seamCurve
    rw [hHp, hHq]
    have e1 : (1 / 10000 - ys) / 2 = a := by rw [hys]; linarith
    have e2 : (1 / 10000 + ys) / 2 = c := by rw [hys]; linarith
    rw [e1, e2]
  rw [hcurve] at hbox'
  linarith

end CKLaneP
