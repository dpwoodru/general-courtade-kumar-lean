import GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsActualSign

/-! Exact 256-cell dyadic coverage and a sound per-cell derivative-sign
interface for the remaining `x∈[1/8,1/5]` high-cap slope bridge.
The individual derivative cells and derivative formula are separate obligations. -/

namespace GeneralCK

noncomputable def doubleCapBridgeStep : ℝ := 3 / 10240

noncomputable def doubleCapBridgeLo (i : Fin 256) : ℝ :=
  1 / 8 + (i.val : ℝ) * doubleCapBridgeStep

noncomputable def doubleCapBridgeHi (i : Fin 256) : ℝ :=
  1 / 8 + ((i.val + 1 : ℕ) : ℝ) * doubleCapBridgeStep

theorem doubleCapBridge_complete_256_cover {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    ∃ i : Fin 256, x ∈ Set.Icc (doubleCapBridgeLo i)
      (doubleCapBridgeHi i) := by
  have hδ : 0 < doubleCapBridgeStep := by norm_num [doubleCapBridgeStep]
  let t : ℝ := (x - 1 / 8) / doubleCapBridgeStep
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hx.1]) hδ.le
  have ht256 : t ≤ 256 := by
    change (x - 1 / 8) / doubleCapBridgeStep ≤ 256
    apply (div_le_iff₀ hδ).2
    norm_num [doubleCapBridgeStep]
    linarith [hx.2]
  have hxEq : x = 1 / 8 + t * doubleCapBridgeStep := by
    dsimp [t]
    field_simp [hδ.ne'] <;> ring
  by_cases ht : t < 256
  · let n : ℕ := Nat.floor t
    have hn : n < 256 := (Nat.floor_lt ht0).2 ht
    have hlo : (n : ℝ) ≤ t := Nat.floor_le ht0
    have hhi : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
    refine ⟨⟨n, hn⟩, ?_⟩
    constructor
    · dsimp [doubleCapBridgeLo]
      rw [hxEq]
      have hm := mul_le_mul_of_nonneg_right hlo hδ.le
      linarith
    · dsimp [doubleCapBridgeHi]
      rw [hxEq]
      have hm := mul_lt_mul_of_pos_right hhi hδ
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        (add_le_add_left hm.le (1 / 8 : ℝ))
  · have htEq : t = 256 := by linarith [ht256]
    refine ⟨⟨255, by decide⟩, ?_⟩
    constructor
    · dsimp [doubleCapBridgeLo]
      rw [hxEq, htEq]
      norm_num [doubleCapBridgeStep]
    · dsimp [doubleCapBridgeHi]
      rw [hxEq, htEq] <;> norm_num [doubleCapBridgeStep]

structure DoubleCapBridgeDerivativeCellCertificate (i : Fin 256)
    (derivativeExpression : ℝ → ℝ) : Prop where
  positive : ∀ x : ℝ, x ∈ Set.Icc (doubleCapBridgeLo i)
    (doubleCapBridgeHi i) → 0 < derivativeExpression x

theorem doubleCapBridge_derivative_pos_of_256_cells
    {derivativeExpression : ℝ → ℝ}
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i derivativeExpression)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ)) :
    0 < derivativeExpression x := by
  obtain ⟨i, hCell⟩ := doubleCapBridge_complete_256_cover hx
  exact (hCells i).positive x hCell

#print axioms doubleCapBridge_complete_256_cover
#print axioms doubleCapBridge_derivative_pos_of_256_cells

end GeneralCK
