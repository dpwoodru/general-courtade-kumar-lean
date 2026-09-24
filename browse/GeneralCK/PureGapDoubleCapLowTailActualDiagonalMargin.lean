import GeneralCK.PureGapDoubleCapLowTailYThreeQuarters
import GeneralCK.PureGapDoubleCapLowTailLinearSeparation

/-! The actual inverse-entropy bias of the low double-cap tail has a
positive coincident-contact margin. Contact displacement remains open. -/

namespace GeneralCK

theorem doubleCapLowTail_actual_diagonal_margin_pos {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    0 < doubleCapDiagonalMargin (doubleCapLowTailY m) := by
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  exact doubleCapDiagonalMargin_pos_three_quarters
    (doubleCapLowTailY_ge_three_quarters hm hmq) hy1

#print axioms doubleCapLowTail_actual_diagonal_margin_pos

end GeneralCK
