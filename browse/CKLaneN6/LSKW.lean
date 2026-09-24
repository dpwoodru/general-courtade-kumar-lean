import CKLaneN6.Base
import CKLaneE.CertLSK

/-!
# Lane N6: lane E log-sum kernel `LSK` on the bounding `(a/b, b)` box (`lsk`)

`CKLaneE.LSK.check_sound` (relative entropy floor `E ≥ t0·C0`, enhanced log-sum coefficient
`1/(b(1-a)(2-a))`, tight entropy-drop bounds, concave endpoints) is stated for laws with
`a < b`, `r1 ≤ a/b ≤ r2`, `b1 ≤ b ≤ b2`, `t0·C0 ≤ E`, `phi ≤ psi`.  An archived Thm 3 box
`[a0,a1] × [b0,b1] × [t0,t1]` lies in its bounding box `r ∈ [a0/b1, min 1 (a1/b0)]`, `b ∈ [b0,b1]`,
and `E ≥ EMIN + t0 (C0 - EMIN) ≥ t0·C0`.  `lskCheck_sound : lskCheck B w = true → GapBox B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6.LSKW

open GeneralCK CKLaneN6

/-- Four slope anchors of `CKLaneE.LSK.check`. -/
structure LW where
  v0S : ℚ
  v0I : ℚ
  v1S : ℚ
  v1I : ℚ
  deriving Repr, DecidableEq

/-- The bounding box in lane E coordinates (`E1`, `E2` are not used by `LSK`). -/
def box3Of (B : CKLaneD.Box) : CKLaneE.Chart.Box3 :=
  ⟨B.alo / B.bhi, min 1 (B.ahi / B.blo), B.blo, B.bhi, CKLaneD.EMIN, 1⟩

def lskCheck (B : CKLaneD.Box) (w : LW) : Bool :=
  decide (0 < B.alo ∧ 0 < B.blo ∧ B.blo ≤ B.bhi ∧ 0 ≤ B.t0 ∧ B.t0 ≤ 1) &&
  CKLaneE.LSK.check (box3Of B) B.t0 w.v0S w.v0I w.v1S w.v1I

theorem lskCheck_sound {B : CKLaneD.Box} {w : LW} (h : lskCheck B w = true) : GapBox B := by
  intro k μ hin hab hact
  simp only [lskCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨qa0, qb0, qbb, qt0, qt1⟩, hw⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hin
  have ra0 : (0 : ℝ) < B.alo := by exact_mod_cast qa0
  have rb0 : (0 : ℝ) < B.blo := by exact_mod_cast qb0
  have rt0 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast qt0
  have rt1 : (B.t0 : ℝ) ≤ 1 := by exact_mod_cast qt1
  have hb0 : 0 < μ.b := lt_of_lt_of_le rb0 h3
  have ha0 : 0 < μ.a := lt_of_lt_of_le ra0 h1
  have hbhi : (0 : ℝ) < B.bhi := lt_of_lt_of_le hb0 h4
  have hsnd := CKLaneE.LSK.check_sound (box3Of B) B.t0 w.v0S w.v0I w.v1S w.v1I hw k μ hab
  apply hsnd
  · -- r1 ≤ a/b
    show (((B.alo / B.bhi : ℚ)) : ℝ) ≤ μ.a / μ.b
    push_cast
    rw [div_le_div_iff₀ hbhi hb0]
    have k1 : (B.alo : ℝ) * μ.b ≤ (B.alo : ℝ) * B.bhi := mul_le_mul_of_nonneg_left h4 ra0.le
    have k2 : (B.alo : ℝ) * B.bhi ≤ μ.a * B.bhi := mul_le_mul_of_nonneg_right h1 hbhi.le
    linarith
  · -- a/b ≤ min 1 (a1/b0)
    show μ.a / μ.b ≤ ((min 1 (B.ahi / B.blo) : ℚ) : ℝ)
    rw [Rat.cast_min]
    push_cast
    apply le_min
    · rw [div_le_one hb0]; exact hab.le
    · rw [div_le_div_iff₀ hb0 rb0]
      have k1 : μ.a * B.blo ≤ μ.a * μ.b := mul_le_mul_of_nonneg_left h3 ha0.le
      have k2 : μ.a * μ.b ≤ (B.ahi : ℝ) * μ.b := mul_le_mul_of_nonneg_right h2 hb0.le
      linarith
  · show ((B.blo : ℚ) : ℝ) ≤ μ.b
    exact h3
  · show μ.b ≤ ((B.bhi : ℚ) : ℝ)
    exact h4
  · -- t0 C0 ≤ E
    have hEM : (0 : ℝ) ≤ ((CKLaneD.EMIN : ℚ) : ℝ) := by
      simp only [CKLaneD.EMIN]; push_cast; norm_num
    have k : (1 - (B.t0 : ℝ)) * ((CKLaneD.EMIN : ℚ) : ℝ) ≥ 0 := mul_nonneg (by linarith) hEM
    nlinarith
  · exact hact

/-- Leaf form for the Thm 3 row. -/
theorem leafOK_of_lskCheck {B : CKLaneD.Box} {w : LW} (h : lskCheck B w = true) : LeafOK B :=
  leafOK_of_gapBox (lskCheck_sound h)

end CKLaneN6.LSKW
