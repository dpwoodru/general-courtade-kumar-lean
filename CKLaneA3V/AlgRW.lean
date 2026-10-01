import Mathlib

/-! Lane A3: algebraic identities for the R and W congr steps (atomic variables). -/

namespace CKLaneA3V

theorem R_alg (c d E B A : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (_h1 : 1 - c * c ≠ 0) (hB : B ≠ 0) :
    c / d * (((2 : ℚ) : ℝ) * (A / c) + ((2 : ℚ) : ℝ) * (E * (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c))) * (1 / B))) =
      (2 * A + E * c / ((1 - c ^ 2) / 4 * (2 * B))) / d := by
  have e1 : ((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c) = 1 - c * c := by push_cast; ring
  have e2 : (1 : ℝ) - c ^ 2 = 1 - c * c := by ring
  rw [e1, e2]
  push_cast
  field_simp
  ring

theorem W_alg (c E B S : ℝ) (_h1 : 1 - c * c ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    ((8 : ℚ) : ℝ) * (E * E * E * (((2 : ℚ) : ℝ) * B + ((-1 : ℚ) : ℝ) * (c * c)) * (1 / S) *
      (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c)) * (1 / (((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c)))) *
      (1 / B * (1 / B) * (1 / B))) =
    2 * (2 * E ^ 3 * (2 * B - c ^ 2) / (S * ((1 - c ^ 2) / 4) ^ 2 * (2 * B) ^ 3)) := by
  have e1 : ((1 : ℚ) : ℝ) + ((-1 : ℚ) : ℝ) * (c * c) = 1 - c * c := by push_cast; ring
  have e2 : (1 : ℝ) - c ^ 2 = 1 - c * c := by ring
  have e3 : (2 : ℝ) * B - c ^ 2 = 2 * B - c * c := by ring
  rw [e1, e2, e3]
  push_cast
  field_simp
  ring

end CKLaneA3V
