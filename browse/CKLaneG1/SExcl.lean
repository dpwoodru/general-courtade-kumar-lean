import CKLaneD.FleetBase
import CKLaneG3.SCover

/-!
# Lane G1: archived same-side (S) leaves in the rows `a + b ≤ 1/16` and `1/10 ≤ a`

Stated over Lane G3's canonical (S) cover definitions `CKLaneG3.SBox / sBox / InS / SLeafOK`
(`CKLaneG3.SCover`, BRIEF §7): root `(x,b,t) ∈ [0,32]×[1/32,1/2]×[0,1]`, exact midpoint halving
(`COVER.reconstruct`), `InS B a b E := 2^(-x1) ≤ a/b ≤ 2^(-x0) ∧ b0 ≤ b ≤ b1 ∧ t0*C0 ≤ E ≤ t1*C0`.

* `sCheck p w = true` certifies `InS (sBox p) a b E → a + b ≤ 1/16` (row `SS_SmallMean`), hence
  `CKLaneG3.SLeafOK (sBox p)` via `CKLaneG3.sLeafOK_of_smallMean`.
* `cCheck p w = true` certifies `InS (sBox p) a b E → 1/10 ≤ a` (row `CentralSquare`), hence
  `CKLaneG3.SLeafOK (sBox p)` under `CKLaneG3.CentralSquareRow` via `CKLaneG3.sLeafOK_of_central`.
Rational enclosures of `2^(-x)` are certified with exact `Nat` powers (`CKLaneD.pow2LowerOK/UpperOK`).
-/

namespace CKLaneG1

open GeneralCK CKLaneD

/-- Small-mean witness: a rational upper bound `rhi ≥ 2^(-x0)`. -/
structure SW where
  rhi : ℚ
  deriving Repr, DecidableEq

def sCheck (p : List ℕ) (w : SW) : Bool :=
  pow2UpperOK w.rhi (CKLaneG3.sBox p).x0 && decide (0 < (CKLaneG3.sBox p).b0) &&
    decide ((CKLaneG3.sBox p).b1 * (1 + w.rhi) ≤ 1 / 16)

theorem sCheck_small {p : List ℕ} {w : SW} (h : sCheck p w = true) {a b E : ℝ}
    (hin : CKLaneG3.InS (CKLaneG3.sBox p) a b E) : a + b ≤ 1 / 16 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  unfold sCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hr, hb0⟩, hs⟩ := h
  have hr' := pow2UpperOK_sound hr
  have hrpos : (0 : ℚ) < w.rhi := by
    unfold pow2UpperOK at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1.1
  have hrpos' : (0 : ℝ) < (w.rhi : ℝ) := by exact_mod_cast hrpos
  have hb0' := (Rat.cast_lt.mpr (of_decide_eq_true hb0) :
    (((0 : ℚ)) : ℝ) < (((CKLaneG3.sBox p).b0 : ℚ) : ℝ))
  push_cast at hb0'
  have hs' := (Rat.cast_le.mpr (of_decide_eq_true hs) :
    ((((CKLaneG3.sBox p).b1 * (1 + w.rhi) : ℚ)) : ℝ) ≤ ((1 / 16 : ℚ) : ℝ))
  push_cast at hs'
  have hb : 0 < b := by linarith only [hb0', h3]
  have hab : a / b ≤ (w.rhi : ℝ) := h2.trans hr'
  have ha : a ≤ (w.rhi : ℝ) * b := (div_le_iff₀ hb).mp hab
  have hm : (w.rhi : ℝ) * b ≤ (w.rhi : ℝ) * ((CKLaneG3.sBox p).b1 : ℝ) :=
    mul_le_mul_of_nonneg_left h4 hrpos'.le
  nlinarith only [ha, hm, hs', h4]

theorem sCheck_sound {p : List ℕ} {w : SW} (h : sCheck p w = true) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  CKLaneG3.sLeafOK_of_smallMean (fun _ _ _ hin => sCheck_small h hin)

theorem sLeaves_of_list (L : List (List ℕ × SW)) (hok : (L.all fun x => sCheck x.1 x.2) = true) :
    ∀ x ∈ L, CKLaneG3.SLeafOK (CKLaneG3.sBox x.1) ∧
      ∀ a b E : ℝ, CKLaneG3.InS (CKLaneG3.sBox x.1) a b E → a + b ≤ 1 / 16 := by
  intro x hx
  rw [List.all_eq_true] at hok
  exact ⟨sCheck_sound (hok x hx), fun a b E hin => sCheck_small (hok x hx) hin⟩

/-- Central witness: a rational lower bound `rlo ≤ 2^(-x1)` with `1/10 ≤ b0 * rlo`. -/
structure CW where
  rlo : ℚ
  deriving Repr, DecidableEq

def cCheck (p : List ℕ) (w : CW) : Bool :=
  pow2LowerOK w.rlo (CKLaneG3.sBox p).x1 && decide (0 < (CKLaneG3.sBox p).b0) &&
    decide (1 / 10 ≤ (CKLaneG3.sBox p).b0 * w.rlo)

/-- A checked (S) leaf lies in `1/10 ≤ a` (owned by the CentralSquare row). -/
theorem cCheck_sound {p : List ℕ} {w : CW} (h : cCheck p w = true) {a b E : ℝ}
    (hin : CKLaneG3.InS (CKLaneG3.sBox p) a b E) : 1 / 10 ≤ a := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  unfold cCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hr, hb0⟩, hs⟩ := h
  have hr' := pow2LowerOK_sound hr
  have hrpos : (0 : ℚ) < w.rlo := by
    unfold pow2LowerOK at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1.1
  have hrpos' : (0 : ℝ) < (w.rlo : ℝ) := by exact_mod_cast hrpos
  have hb0' := (Rat.cast_lt.mpr (of_decide_eq_true hb0) :
    (((0 : ℚ)) : ℝ) < (((CKLaneG3.sBox p).b0 : ℚ) : ℝ))
  push_cast at hb0'
  have hs' := (Rat.cast_le.mpr (of_decide_eq_true hs) :
    (((1 / 10 : ℚ)) : ℝ) ≤ ((((CKLaneG3.sBox p).b0 * w.rlo : ℚ)) : ℝ))
  push_cast at hs'
  have hb : 0 < b := by linarith only [hb0', h3]
  have hab : (w.rlo : ℝ) ≤ a / b := hr'.trans h1
  have ha : (w.rlo : ℝ) * b ≤ a := (le_div_iff₀ hb).mp hab
  have hm : (w.rlo : ℝ) * ((CKLaneG3.sBox p).b0 : ℝ) ≤ (w.rlo : ℝ) * b :=
    mul_le_mul_of_nonneg_left h3 hrpos'.le
  nlinarith only [ha, hm, hs']

/-- A checked central leaf carries the `SS_Compact` obligation, given the CentralSquare row. -/
theorem cCheck_leafOK {p : List ℕ} {w : CW} (h : cCheck p w = true)
    (hcs : CKLaneG3.CentralSquareRow) : CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  CKLaneG3.sLeafOK_of_central (fun _ _ _ hin => cCheck_sound h hin) hcs

theorem cLeaves_of_list (L : List (List ℕ × CW)) (hok : (L.all fun x => cCheck x.1 x.2) = true) :
    ∀ x ∈ L, ∀ a b E : ℝ, CKLaneG3.InS (CKLaneG3.sBox x.1) a b E → 1 / 10 ≤ a := by
  intro x hx a b E hin
  rw [List.all_eq_true] at hok
  exact cCheck_sound (hok x hx) hin

theorem cLeavesOK_of_list (L : List (List ℕ × CW)) (hok : (L.all fun x => cCheck x.1 x.2) = true)
    (hcs : CKLaneG3.CentralSquareRow) : ∀ x ∈ L, CKLaneG3.SLeafOK (CKLaneG3.sBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at hok
  exact cCheck_leafOK (hok x hx) hcs

end CKLaneG1

#check @CKLaneG1.sCheck_small
#print axioms CKLaneG1.sCheck_small
#check @CKLaneG1.sCheck_sound
#print axioms CKLaneG1.sCheck_sound
#check @CKLaneG1.cCheck_sound
#print axioms CKLaneG1.cCheck_sound
#check @CKLaneG1.cCheck_leafOK
#print axioms CKLaneG1.cCheck_leafOK
