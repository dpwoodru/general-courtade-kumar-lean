import CKLaneC.RSTail.Region
import CKLaneR2.Cell.Defs

/-! Lane C: bridge from R2b's leaf conclusions (stated with `CKLaneR2.Cell.one`) to `TailPosI` (`CKLaneC.RSCell.one`). -/

namespace CKLaneC.RSTail

theorem ofR2 {b0 b1 t0 t1 s0 s1 : Int}
    (h : ∀ b t σ : ℝ, (b0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ b → b ≤ (b1 : ℝ) / (CKLaneR2.Cell.one : ℝ) →
      (t0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ t → t ≤ (t1 : ℝ) / (CKLaneR2.Cell.one : ℝ) →
      (s0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ σ → σ ≤ (s1 : ℝ) / (CKLaneR2.Cell.one : ℝ) → 0 < σ →
      0 < CKLaneN23.RS.rayGamma b t (b - b * σ)) :
    TailPosI b0 b1 t0 t1 s0 s1 := h

end CKLaneC.RSTail
