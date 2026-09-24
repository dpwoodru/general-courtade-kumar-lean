import CKLaneC.RSCell.SoundCell

/-! Lane C, RA-stat interior: real-coordinate API for certified cells. -/

namespace CKLaneC.RSCell

/-- Every point of `[(c0 - h)/one, (c0 + h)/one]` is `(c0 + h x)/one` for some `|x| ≤ 1`. -/
theorem cell_coord (c0 h : ℤ) (hh : 0 < h) (v : ℝ) (hlo : ((c0 - h : ℤ) : ℝ) / one ≤ v)
    (hhi : v ≤ ((c0 + h : ℤ) : ℝ) / one) :
    ∃ x : ℝ, |x| ≤ 1 ∧ ((c0 : ℝ) + h * x) / one = v := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  refine ⟨(v * one - c0) / h, ?_, ?_⟩
  · rw [div_le_iff₀ hone'] at hlo
    rw [le_div_iff₀ hone'] at hhi
    push_cast at hlo hhi
    rw [abs_le]; constructor
    · rw [le_div_iff₀ hh']; linarith
    · rw [div_le_iff₀ hh']; linarith
  · have hh0 : (h : ℝ) ≠ 0 := hh'.ne'
    have := hne
    field_simp
    ring

end CKLaneC.RSCell
