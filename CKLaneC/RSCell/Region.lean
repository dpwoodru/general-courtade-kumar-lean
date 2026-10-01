import CKLaneC.RSCell.Union
import CKLaneC.RSCell.CellAPI

/-!
# Lane C, RA-stat interior: box predicate `RegionPos`, split-tree lemmas, and the bulk piece

`RegionPos blo bhi tlo thi slo shi` says that `rayGamma b t (b - bσ) > 0` at every point of the box with
`σ < 1` and `bσ ≤ 9/20` (the non-corner condition for `εc = 1/20`).

The cover proof is a tree of three constructors:
* `RegionPos.split_b`, `split_t` and `split_s` split a box at a midpoint;
* `RegionPos.excl` closes leaves that lie wholly inside the corner;
* the cell theorems close the certified leaves.
-/

namespace CKLaneC.RSCell

def RegionPos (blo bhi tlo thi slo shi : ℝ) : Prop :=
  ∀ b t σ : ℝ, blo ≤ b → b ≤ bhi → tlo ≤ t → t ≤ thi → slo ≤ σ → σ ≤ shi → σ < 1 → b * σ ≤ 9 / 20 →
    0 < CKLaneN23.RS.rayGamma b t (b - b * σ)

theorem RegionPos.split_b {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo m tlo thi slo shi)
    (h2 : RegionPos m bhi tlo thi slo shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total b m with h | h
  · exact h1 b t σ hb0 h ht0 ht1 hs0 hs1 hs hu
  · exact h2 b t σ h hb1 ht0 ht1 hs0 hs1 hs hu

theorem RegionPos.split_t {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo bhi tlo m slo shi)
    (h2 : RegionPos blo bhi m thi slo shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total t m with h | h
  · exact h1 b t σ hb0 hb1 ht0 h hs0 hs1 hs hu
  · exact h2 b t σ hb0 hb1 h ht1 hs0 hs1 hs hu

theorem RegionPos.split_s {blo bhi tlo thi slo shi : ℝ} (m : ℝ) (h1 : RegionPos blo bhi tlo thi slo m)
    (h2 : RegionPos blo bhi tlo thi m shi) : RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs hu
  rcases le_total σ m with h | h
  · exact h1 b t σ hb0 hb1 ht0 ht1 hs0 h hs hu
  · exact h2 b t σ hb0 hb1 ht0 ht1 h hs1 hs hu

/-- A box wholly inside the corner (`blo · slo > 9/20`) has no admissible points. -/
theorem RegionPos.excl {blo bhi tlo thi slo shi : ℝ} (hb : 0 ≤ blo) (hs : 0 ≤ slo) (h : 9 / 20 < blo * slo) :
    RegionPos blo bhi tlo thi slo shi := by
  intro b t σ hb0 _ _ _ hs0 _ _ hu
  exfalso
  have : blo * slo ≤ b * σ := mul_le_mul hb0 hs0 hs (le_trans hb hb0)
  linarith

/-- A certified cell closes a leaf. -/
theorem RegionPos.of_cell {blo bhi tlo thi slo shi : ℝ}
    (h : ∀ b t σ : ℝ, blo ≤ b → b ≤ bhi → tlo ≤ t → t ≤ thi → slo ≤ σ → σ ≤ shi → σ < 1 →
      0 < CKLaneN23.RS.rayGamma b t (b - b * σ)) : RegionPos blo bhi tlo thi slo shi :=
  fun b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs _ => h b t σ hb0 hb1 ht0 ht1 hs0 hs1 hs

/-- The bulk piece from a `RegionPos` on the root box `[b1,1/2] × [0,1] × [σ0,1]`. -/
theorem gammaBulk_of_region {S b1 σ0 : ℝ} (hσ0 : 0 ≤ σ0) (h : RegionPos b1 (1 / 2) 0 1 σ0 1) :
    GammaBulk S (1 / 20) b1 σ0 := by
  intro b t d ht0 ht1 hd0 hdb hb12 _ hεc hb1 hσ
  have hb0 : 0 < b := lt_trans hd0 hdb
  set σ := (b - d) / b with hσdef
  have hbσ : b * σ = b - d := by rw [hσdef]; field_simp
  have hd : b - b * σ = d := by rw [hbσ]; ring
  have hs0 : σ0 ≤ σ := by rw [hσdef, le_div_iff₀ hb0]; linarith
  have hs1 : σ < 1 := by rw [hσdef, div_lt_one hb0]; linarith
  have hu : b * σ ≤ 9 / 20 := by rw [hbσ]; linarith
  have := h b t σ hb1 hb12 ht0 ht1 hs0 hs1.le hs1 hu
  rw [hd] at this
  exact this.le

end CKLaneC.RSCell
