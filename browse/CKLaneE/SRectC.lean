import CKLaneE.SRect

/-!
# Lane E: containment form of the rectangle certificates

`leafS_of_rectC`: an archived box whose `(x, b)` rectangle is contained in a certified rectangle `X`
(and whose `t0` is at least the certified floor) satisfies `LeafS` (monotonicity of `2^(-x)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

open GeneralCK

def fitsC (B : SBox) (X : SRect) (t0 : ℚ) : Bool :=
  decide (X.x0 ≤ B.x0 ∧ B.x1 ≤ X.x1 ∧ X.b0 ≤ B.b0 ∧ B.b1 ≤ X.b1 ∧ t0 ≤ B.t0)

theorem leafS_of_rectC (B : SBox) {X : SRect} {t0 : ℚ} (hR : RectOK X t0) (hf : fitsC B X t0 = true) :
    LeafS B := by
  simp only [fitsC, decide_eq_true_eq] at hf
  obtain ⟨e0, e1, e2, e3, ht⟩ := hf
  intro k μ hab hin hact
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hin
  have hx1 : (2 : ℝ) ^ (-(X.x1 : ℝ)) ≤ (2 : ℝ) ^ (-(B.x1 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (B.x1 : ℝ) ≤ X.x1 := by exact_mod_cast e1
    linarith
  have hx0 : (2 : ℝ) ^ (-(B.x0 : ℝ)) ≤ (2 : ℝ) ^ (-(X.x0 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (X.x0 : ℝ) ≤ B.x0 := by exact_mod_cast e0
    linarith
  have hb0 : (X.b0 : ℝ) ≤ μ.b := le_trans (by exact_mod_cast e2) h3
  have hb1 : μ.b ≤ (X.b1 : ℝ) := le_trans h4 (by exact_mod_cast e3)
  have hC : 0 ≤ (H μ.a + H μ.b) / 2 := by
    have := H_nonneg μ.a_interior.1.le μ.a_interior.2.le
    have := H_nonneg μ.b_interior.1.le μ.b_interior.2.le
    linarith
  have htR : (t0 : ℝ) ≤ B.t0 := by exact_mod_cast ht
  have hE : (t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy :=
    (mul_le_mul_of_nonneg_right htR hC).trans h5
  exact hR k μ hab (hx1.trans h1) (h2.trans hx0) hb0 hb1 hE hact

end CKLaneE.S

#print axioms CKLaneE.S.leafS_of_rectC
