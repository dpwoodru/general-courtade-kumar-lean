import CKLaneC2R.CompactCover.S00
import CKLaneC2R.CompactCover.S01
import CKLaneC2R.CompactCover.S02
import CKLaneC2R.CompactCover.S03
import CKLaneC2R.CompactCover.S04
import CKLaneC2R.CompactCover.S05

/-!
# Lane C2: the compact reflection rectangle `[3/20, 999/1000] × [43/500, 999/1000]`

Union of the six certified strips (5,079 reflective cells).
-/

namespace CKLaneC2R

theorem compact_all_certified {a z : ℝ} (ha1 : (3 / 20 : ℝ) ≤ a) (ha2 : a ≤ 999 / 1000)
    (hz1 : (43 / 500 : ℝ) ≤ z) (hz2 : z ≤ 999 / 1000) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  have q0 : ((3 / 20 : ℚ) : ℝ) = 3 / 20 := by norm_num
  have q1 : ((1 / 5 : ℚ) : ℝ) = 1 / 5 := by norm_num
  have q2 : ((3 / 10 : ℚ) : ℝ) = 3 / 10 := by norm_num
  have q3 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have q4 : ((7 / 10 : ℚ) : ℝ) = 7 / 10 := by norm_num
  have q5 : ((9 / 10 : ℚ) : ℝ) = 9 / 10 := by norm_num
  have q6 : ((999 / 1000 : ℚ) : ℝ) = 999 / 1000 := by norm_num
  have qz : ((43 / 500 : ℚ) : ℝ) = 43 / 500 := by norm_num
  have hz1' : ((43 / 500 : ℚ) : ℝ) ≤ z := by rw [qz]; exact hz1
  have hz2' : z ≤ ((999 / 1000 : ℚ) : ℝ) := by rw [q6]; exact hz2
  rcases le_or_gt a (1 / 5) with h1 | h1
  · exact CompactCover.strip0 (by rw [q0]; exact ha1) (by rw [q1]; exact h1) hz1' hz2'
  rcases le_or_gt a (3 / 10) with h2 | h2
  · exact CompactCover.strip1 (by rw [q1]; exact h1.le) (by rw [q2]; exact h2) hz1' hz2'
  rcases le_or_gt a (1 / 2) with h3 | h3
  · exact CompactCover.strip2 (by rw [q2]; exact h2.le) (by rw [q3]; exact h3) hz1' hz2'
  rcases le_or_gt a (7 / 10) with h4 | h4
  · exact CompactCover.strip3 (by rw [q3]; exact h3.le) (by rw [q4]; exact h4) hz1' hz2'
  rcases le_or_gt a (9 / 10) with h5 | h5
  · exact CompactCover.strip4 (by rw [q4]; exact h4.le) (by rw [q5]; exact h5) hz1' hz2'
  · exact CompactCover.strip5 (by rw [q5]; exact h5.le) (by rw [q6]; exact ha2) hz1' hz2'

end CKLaneC2R
