/-
Lane C2 — the small-`c` pre-cancellation identity.

With `A = 2c + c^3 a1`, `B = c^2 + c^4 b1` (i.e. `a1 = a1f c`, `b1 = b1f c`), the nested sign
expression factors exactly as
    `Wt c = c^5 · F(c, a1, b1, L)`,   `F = Ex.evalR [c, a1, b1, L] Fex`  (185 monomials).
This is the `k = 3` cancellation carried SYMBOLICALLY: all terms of order `c^0 … c^4` vanish
identically, so `F` is evaluated with no cancellation near `c = 0`.  Pure algebra (`ring`).
-/
import CKLaneC2.Deriv

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

theorem Wt_eq_F {c : ℝ} (h0 : 0 < c) :
    Wt c = c ^ 5 * Ex.evalR [c, a1f c, b1f c, Real.log 2] Fex := by
  have hc : c ≠ 0 := h0.ne'
  have hA : Af c = 2 * c + c ^ 3 * a1f c := by
    unfold a1f; field_simp; ring
  have hB : Bf c = c ^ 2 + c ^ 4 * b1f c := by
    unfold b1f; field_simp; ring
  have hK : Kf c = Real.log 2 + (c ^ 2 + c ^ 4 * b1f c) / 2 := by
    unfold Kf; rw [hB]
  have hE : Ef c = Real.log 2 + (c ^ 2 + c ^ 4 * b1f c) / 2 - c * (2 * c + c ^ 3 * a1f c) / 2 := by
    unfold Ef; rw [hA, hB]
  unfold Wt
  rw [hK, hE, hA]
  generalize a1f c = a
  generalize b1f c = b
  generalize Real.log 2 = L
  simp only [Wex, Fex, Ex.evalR, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

end CKLaneC2
