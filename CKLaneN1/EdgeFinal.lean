import CKLaneN1.EdgeShard.E00
import CKLaneN1.EdgeShard.E01
import CKLaneN1.EdgeShard.E02
import CKLaneN1.EdgeShard.E03
import CKLaneN1.EdgeShard.E04
import CKLaneN1.EdgeShard.E05
import CKLaneN1.EdgeShard.E06
import CKLaneN1.EdgeShard.E07
import CKLaneN1.EdgeShard.E08
import CKLaneN1.EdgeShard.E09
import CKLaneN1.EdgeShard.E10
import CKLaneN1.EdgeShard.E11
import CKLaneN1.EdgeShard.E12
import CKLaneN1.EdgeShard.E13
import CKLaneN1.EdgeShard.E14
import CKLaneN1.EdgeShard.E15
import CKLaneN1.EdgeShard.E16
import CKLaneN1.EdgeShard.E17
import CKLaneN1.EdgeShard.E18
import CKLaneN1.EdgeShard.E19
import CKLaneN1.EdgeShard.E20
import CKLaneN1.EdgeShard.E21
import CKLaneN1.EdgeShard.E22
import CKLaneN1.EdgeShard.E23
import CKLaneN1.EdgeShard.E24
import CKLaneN1.EdgeShard.E25
import CKLaneN1.EdgeShard.E26
import CKLaneN1.EdgeShard.E27
import CKLaneN1.EdgeShard.E28
import CKLaneN1.EdgeShard.E29
import CKLaneN1.EdgeShard.E30
import CKLaneN1.EdgeShard.E31
import CKLaneN1.EdgeShard.E32
import CKLaneN1.EdgeShard.E33
import CKLaneN1.EdgeShard.E34
import CKLaneN1.EdgeShard.E35
import CKLaneN1.EdgeShard.E36
import CKLaneN1.EdgeShard.E37
import CKLaneN1.EdgeShard.E38
import CKLaneN1.EdgeShard.E39
import CKLaneN1.EdgeShard.E40
import CKLaneN1.EdgeShard.E41
import CKLaneN1.EdgeShard.E42
import CKLaneN1.EdgeShard.E43
import CKLaneN1.EdgeShard.E44
import CKLaneN1.EdgeShard.E45
import CKLaneN1.EdgeShard.E46
import CKLaneN1.EdgeShard.E47
import CKLaneN1.EdgeShard.E48
import CKLaneN1.EdgeShard.E49
import CKLaneN1.EdgeShard.E50
import CKLaneN1.EdgeShard.E51
import CKLaneN1.EdgeShard.E52
import CKLaneN1.EdgeShard.E53
import CKLaneN1.EdgeShard.E54
import CKLaneN1.EdgeShard.E55
import CKLaneN1.EdgeShard.E56
import CKLaneN1.EdgeShard.E57
import CKLaneN1.EdgeShard.E58
import CKLaneN1.EdgeShard.E59
import CKLaneN1.EdgeShard.E60
import CKLaneN1.Chunks
import CKLaneN1.EdgeCorner

set_option autoImplicit false

/-!
# Lane N1: capFibers cutoff edge (`leftEdge`) — CLOSED from the kernel-checked box tree

`edgeTree_ok`: all 3006 leaves of `edgeTree` pass `edgeLeafOK` (fleet shards `EdgeShard.E00..E60`,
`decide +kernel`).  With `edgeOK_sound` (certified boxes) and `corner_pos` (the corner box) this
gives positivity of the cutoff-edge value on the whole strict edge `0 < a < b < S - a`,
`S = retainedCutoff = 1/10000`.
-/

namespace CKLaneN1.Edge

open GeneralCK SmallMeanPhiCutoff

theorem edgeTree_length : edgeTree.leaves.length = 3006 := by decide +kernel

/-- Every leftEdge leaf passes the kernel check. -/
theorem edgeTree_ok : edgeTree.allLeaves (fun p w => edgeLeafOK (edgeRoot.ofPath p) w) = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) 50 61 edgeTree.leaves
    (by rw [edgeTree_length]; decide)
  intro k hk
  interval_cases k
  · exact EdgeShard.E00
  · exact EdgeShard.E01
  · exact EdgeShard.E02
  · exact EdgeShard.E03
  · exact EdgeShard.E04
  · exact EdgeShard.E05
  · exact EdgeShard.E06
  · exact EdgeShard.E07
  · exact EdgeShard.E08
  · exact EdgeShard.E09
  · exact EdgeShard.E10
  · exact EdgeShard.E11
  · exact EdgeShard.E12
  · exact EdgeShard.E13
  · exact EdgeShard.E14
  · exact EdgeShard.E15
  · exact EdgeShard.E16
  · exact EdgeShard.E17
  · exact EdgeShard.E18
  · exact EdgeShard.E19
  · exact EdgeShard.E20
  · exact EdgeShard.E21
  · exact EdgeShard.E22
  · exact EdgeShard.E23
  · exact EdgeShard.E24
  · exact EdgeShard.E25
  · exact EdgeShard.E26
  · exact EdgeShard.E27
  · exact EdgeShard.E28
  · exact EdgeShard.E29
  · exact EdgeShard.E30
  · exact EdgeShard.E31
  · exact EdgeShard.E32
  · exact EdgeShard.E33
  · exact EdgeShard.E34
  · exact EdgeShard.E35
  · exact EdgeShard.E36
  · exact EdgeShard.E37
  · exact EdgeShard.E38
  · exact EdgeShard.E39
  · exact EdgeShard.E40
  · exact EdgeShard.E41
  · exact EdgeShard.E42
  · exact EdgeShard.E43
  · exact EdgeShard.E44
  · exact EdgeShard.E45
  · exact EdgeShard.E46
  · exact EdgeShard.E47
  · exact EdgeShard.E48
  · exact EdgeShard.E49
  · exact EdgeShard.E50
  · exact EdgeShard.E51
  · exact EdgeShard.E52
  · exact EdgeShard.E53
  · exact EdgeShard.E54
  · exact EdgeShard.E55
  · exact EdgeShard.E56
  · exact EdgeShard.E57
  · exact EdgeShard.E58
  · exact EdgeShard.E59
  · exact EdgeShard.E60

/-- Positivity of the cutoff-edge value in the `(t, z)` chart. -/
theorem edge_pos_tz {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < canonicalPureGap (1 / 20000 * (1 - t)) (1 / 10000 - 1 / 20000 * (1 - t))
      (H (1 / 20000 * (1 - t))) (H (1 / 20000 * (1 + t * (2 * z - 1)))) := by
  have hroot : edgeRoot.Mem t z 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [edgeRoot] <;> push_cast <;> linarith
  obtain ⟨q, hq, hmem⟩ := PT.cover edgeRoot edgeTree hroot
  have hok := PT.allLeaves_sound edgeTree_ok q hq
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hmem
  unfold edgeLeafOK at hok
  split_ifs at hok with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hT, -⟩, -⟩, hZ⟩ := hok
    have hTR : (1023 / 1024 : ℝ) ≤ t := by
      have := rle hT
      simp only [TCq] at this
      push_cast at this
      linarith
    have hZR : z ≤ 1 / 2048 := by
      have := rle hZ
      simp only [ZCq] at this
      push_cast at this
      linarith
    exact corner_pos hTR ht1 hz0 hZR
  · exact edgeOK_sound hok h1 h2 h3 h4 ht0 ht1 hz0 hz1

/-- **leftEdge (CLOSED)**: the cutoff-edge value is nonnegative (indeed positive) on the strict
edge `0 < a < b < S - a` for `S = retainedCutoff`. -/
theorem leftEdge_retained : ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 / 2 →
    b < retainedCutoff - a → retainedCutoff - a ≤ 1 / 2 →
    0 ≤ canonicalPureGap a (retainedCutoff - a) (H a) (H b) := by
  intro a b ha hab _ hbc _
  have hS : retainedCutoff = 1 / 10000 := rfl
  rw [hS] at hbc ⊢
  have hy : 0 < 1 / 10000 - 2 * a := by linarith
  set t : ℝ := (1 / 10000 - 2 * a) / (1 / 10000) with htdef
  set z : ℝ := (b - a) / (1 / 10000 - 2 * a) with hzdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t < 1 := by rw [htdef, div_lt_one (by norm_num)]; linarith
  have hz0 : 0 < z := by rw [hzdef]; exact div_pos (by linarith) hy
  have hz1 : z < 1 := by rw [hzdef, div_lt_one hy]; linarith
  have key := edge_pos_tz ht0 ht1 hz0 hz1
  have ht' : t = 10000 * (1 / 10000 - 2 * a) := by rw [htdef]; ring
  have hz' : z * (1 / 10000 - 2 * a) = b - a := by rw [hzdef]; exact div_mul_cancel₀ _ hy.ne'
  have htz : t * z = 10000 * (b - a) := by
    calc t * z = 10000 * (z * (1 / 10000 - 2 * a)) := by rw [ht']; ring
      _ = 10000 * (b - a) := by rw [hz']
  have ea : 1 / 20000 * (1 - t) = a := by rw [ht']; ring
  have eb : 1 / 20000 * (1 + t * (2 * z - 1)) = b := by
    have e1 : 1 / 20000 * (1 + t * (2 * z - 1)) = 1 / 20000 * (1 + 2 * (t * z) - t) := by ring
    rw [e1, htz, ht']
    ring
  rw [ea, eb] at key
  exact key.le

end CKLaneN1.Edge
