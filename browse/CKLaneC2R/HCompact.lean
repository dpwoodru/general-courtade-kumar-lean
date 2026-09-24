import CKLaneC2R.CompactAll
import CKLaneC2R.EndpointCover

/-!
# Lane C2: `hcompact` at the exact consumer type

`GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band` takes
`hcompact : ∀ a z, a ∈ Icc (3/20) (999/1000) → z ∈ Ioo (43/500) 1 → 0 ≤ curvature a (a*z)`.
The compact part `z ≤ 999/1000` is `compact_all_certified` (5,079 reflective compact cells);
the endpoint part `999/1000 ≤ z < 1` is `EndpointCover.cover` (regular expression cells).
-/

namespace CKLaneC2R

theorem endpoint_all_certified {a z : ℝ} (ha1 : (3 / 20 : ℝ) ≤ a) (ha2 : a ≤ 999 / 1000)
    (hz1 : (999 / 1000 : ℝ) ≤ z) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  have q0 : ((3 / 20 : ℚ) : ℝ) = 3 / 20 := by norm_num
  have q6 : ((999 / 1000 : ℚ) : ℝ) = 999 / 1000 := by norm_num
  have q7 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  exact EndpointCover.cover (by rw [q0]; exact ha1) (by rw [q6]; exact ha2)
    (by rw [q6]; exact hz1) (by rw [q7]; exact hz.le) hz

theorem hcompact_certified : ∀ a z : ℝ, a ∈ Set.Icc (3 / 20 : ℝ) (999 / 1000) →
    z ∈ Set.Ioo (43 / 500 : ℝ) 1 → 0 ≤ GeneralCK.Reflection.curvature a (a * z) := by
  intro a z ha hz
  rcases le_or_gt z (999 / 1000) with h | h
  · exact (compact_all_certified ha.1 ha.2 hz.1.le h).le
  · exact (endpoint_all_certified ha.1 ha.2 h.le hz.2).le

end CKLaneC2R
