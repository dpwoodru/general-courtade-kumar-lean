/-
Lane P — fast certified logarithm bounds of positive rationals via dyadic rounding and `lnDy`.

* `logUpQ x` : `log x ≤ logUpQ x`   (`x > 0`), using `N = ⌈x·2^60⌉`.
* `logDnQ x` : `logDnQ x ≤ log x`   (`⌊x·2^60⌋ ≥ 1`), using `N = ⌊x·2^60⌋`.
-/
import CKLaneP.EvalDy

set_option autoImplicit false

namespace CKLaneP

def logUpQ (x : ℚ) : ℚ :=
  ((lnDy 60 64 20 l2c (⌈x * 2 ^ 60⌉₊)).2 : ℚ) / 2 ^ 64

def logDnQ (x : ℚ) : ℚ :=
  ((lnDy 60 64 20 l2c (⌊x * 2 ^ 60⌋₊)).1 : ℚ) / 2 ^ 64

theorem logUpQ_sound {x : ℚ} (hx : 0 < x) : Real.log (x : ℝ) ≤ ((logUpQ x : ℚ) : ℝ) := by
  set N := ⌈x * 2 ^ 60⌉₊ with hN
  have hxN : x * 2 ^ 60 ≤ (N : ℚ) := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have : 0 < x * 2 ^ 60 := by positivity
    have h := Nat.ceil_pos.mpr this
    omega
  have h := (lnDy_sound (P := 60) (Q := 64) (n := 20) (N := N) l2c_sound hN1).2
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hxN' : (x : ℝ) ≤ (N : ℝ) / 2 ^ 60 := by
    rw [le_div_iff₀ (by positivity)]
    have := (Rat.cast_le (K := ℝ)).mpr hxN
    push_cast at this
    exact this
  have hlog : Real.log (x : ℝ) ≤ Real.log ((N : ℝ) / 2 ^ 60) := Real.log_le_log hxR hxN'
  unfold logUpQ
  rw [← hN]
  push_cast
  rw [le_div_iff₀ (by positivity)]
  have hq : (0 : ℝ) < 2 ^ 64 := by positivity
  nlinarith

theorem logDnQ_sound {x : ℚ} (hx : 1 ≤ ⌊x * 2 ^ 60⌋₊) : ((logDnQ x : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  set N := ⌊x * 2 ^ 60⌋₊ with hN
  have hNx : (N : ℚ) ≤ x * 2 ^ 60 := Nat.floor_le (by
    by_contra hneg
    push Not at hneg
    have : ⌊x * 2 ^ 60⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
    omega)
  have h := (lnDy_sound (P := 60) (Q := 64) (n := 20) (N := N) l2c_sound hx).1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hx
  have hNx' : (N : ℝ) / 2 ^ 60 ≤ (x : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have := (Rat.cast_le (K := ℝ)).mpr hNx
    push_cast at this
    exact this
  have hlog : Real.log ((N : ℝ) / 2 ^ 60) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by positivity) hNx'
  unfold logDnQ
  rw [← hN]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end CKLaneP
