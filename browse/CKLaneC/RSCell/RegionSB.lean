import CKLaneC.RSCell.Region

/-!
# Lane C, RA-stat: the small-`b` piece from a box cover

`gammaSmallB_of_region` turns a `RegionPos` on the root box `[b0, b1] × [0, 1] × [σ0, 1]` into
`GammaSmallB S εc b1 σ0`, provided `2 · b0 ≤ S` (every admissible point has `b > S/2 ≥ b0`, because
`S < 2b - t d ≤ 2b`) and `b1 ≤ 9/20` (so the non-corner side condition `bσ ≤ 9/20` of `RegionPos` is automatic).
-/

namespace CKLaneC.RSCell

theorem gammaSmallB_of_region {S εc b0 b1 σ0 : ℝ} (hσ0 : 0 ≤ σ0) (hb1 : b1 ≤ 9 / 20) (hS : 2 * b0 ≤ S)
    (h : RegionPos b0 b1 0 1 σ0 1) : GammaSmallB S εc b1 σ0 := by
  intro b t d ht0 ht1 hd0 hdb _ hS' _ hbb1 hσ
  have hb0 : 0 < b := lt_trans hd0 hdb
  set σ := (b - d) / b with hσdef
  have hbσ : b * σ = b - d := by rw [hσdef]; field_simp
  have hd : b - b * σ = d := by rw [hbσ]; ring
  have hs0 : σ0 ≤ σ := by rw [hσdef, le_div_iff₀ hb0]; linarith
  have hs1 : σ < 1 := by rw [hσdef, div_lt_one hb0]; linarith
  have hu : b * σ ≤ 9 / 20 := by rw [hbσ]; linarith
  have htd : 0 ≤ t * d := mul_nonneg ht0 hd0.le
  have hbl : b0 ≤ b := by linarith
  have := h b t σ hbl hbb1 ht0 ht1 hs0 hs1.le hs1 hu
  rw [hd] at this
  exact this.le

end CKLaneC.RSCell
