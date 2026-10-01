import CKLaneN1.SRShard.C00
import CKLaneN1.SRShard.C01
import CKLaneN1.SRShard.C02
import CKLaneN1.SRShard.C03
import CKLaneN1.SRShard.C04
import CKLaneN1.SRShard.C05
import CKLaneN1.SRShard.T00
import CKLaneN1.SRShard.T01
import CKLaneN1.SRShard.T02
import CKLaneN1.SRShard.T03
import CKLaneN1.SRShard.T04
import CKLaneN1.SRShard.T05
import CKLaneN1.SRShard.T06
import CKLaneN1.SRShard.T07
import CKLaneN1.SRShard.T08
import CKLaneN1.SRShard.T09
import CKLaneN1.SRShard.T10
import CKLaneN1.SRShard.T11
import CKLaneN1.SRShard.T12
import CKLaneN1.SRShard.T13
import CKLaneN1.SRShard.T14
import CKLaneN1.SRShard.T15
import CKLaneN1.Chunks

/-!
# Lane N1: SMALL_RATIO Thm 1 cover, Thm 4 cover, and the rows they close

* `row_smallRatioT1Cover : SmallRatioT1Cover` — NORMALIZED_COLLAR, all 205 archived leaves.
* `thm4_cover` — CENTRAL_SMALL_RATIO, all 611 archived leaves (572 `normalized` by the kernel check,
  39 `small_ratio` delegated to Thm 1 exactly as archived).
* `row_smallRatioT4Rest : SmallRatioT4Rest`, `row_SR_SmallRatio : SR_SmallRatio`.

`SmallRatioT1Cover` / `SmallRatioT4Rest` are verbatim copies of lane N23's rows
(`N23/src/CKLaneN23/SameSideHalf.lean`); `SR_SmallRatio` is `N1/SUBROWS.lean`.
-/

namespace CKLaneN1

open GeneralCK

/-- Theorem 1 cover root `[10^-6, 11/200] × [0,4]` (NORMALIZED_COLLAR, 205 leaves).
(Verbatim copy of `CKLaneN23.SmallRatioT1Cover`.) -/
def SmallRatioT1Cover : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
    1 - μ.a - μ.b ≤ μ.meanEntropy → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Thm 4 cover (root `E ∈ [10^-6, 11/200]`) outside the Thm 1 boxes: the 572 `normalized`
leaves (they satisfy `E < q` wherever Thm 1 is not used).
(Verbatim copy of `CKLaneN23.SmallRatioT4Rest`.) -/
def SmallRatioT4Rest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → 1 / 1000000 ≤ μ.meanEntropy →
    μ.meanEntropy ≤ 11 / 200 → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    μ.meanEntropy < 1 - μ.a - μ.b → PsiActive μ → μ.gap ≤ μ.cost

theorem collarTree_length : collarTree.leaves.length = 205 := by decide +kernel
theorem centralTree_length : centralTree.leaves.length = 611 := by decide +kernel

/-- Every archived NORMALIZED_COLLAR leaf passes the kernel check. -/
theorem collarTree_ok : collarTree.allLeaves leafOKC = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => leafOKC q.1 q.2) 40 6 collarTree.leaves
    (by rw [collarTree_length]; decide)
  intro k hk
  interval_cases k
  · exact SRShard.C00
  · exact SRShard.C01
  · exact SRShard.C02
  · exact SRShard.C03
  · exact SRShard.C04
  · exact SRShard.C05

/-- Every archived CENTRAL_SMALL_RATIO leaf passes the kernel check. -/
theorem centralTree_ok : centralTree.allLeaves leafOK4 = true := by
  unfold PT.allLeaves
  apply all_of_chunks (fun q => leafOK4 q.1 q.2) 40 16 centralTree.leaves
    (by rw [centralTree_length]; decide)
  intro k hk
  interval_cases k
  · exact SRShard.T00
  · exact SRShard.T01
  · exact SRShard.T02
  · exact SRShard.T03
  · exact SRShard.T04
  · exact SRShard.T05
  · exact SRShard.T06
  · exact SRShard.T07
  · exact SRShard.T08
  · exact SRShard.T09
  · exact SRShard.T10
  · exact SRShard.T11
  · exact SRShard.T12
  · exact SRShard.T13
  · exact SRShard.T14
  · exact SRShard.T15

/-- Row 1 (N23): SMALL_RATIO Theorem 1 on its archived cover root. -/
theorem row_smallRatioT1Cover : SmallRatioT1Cover :=
  collar_of_tree collarTree_ok

/-- SMALL_RATIO Theorem 4 on its archived cover root (`E ≥ 10^-6`), all 611 leaves. -/
theorem thm4_cover : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
    μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost :=
  central_of_tree centralTree_ok row_smallRatioT1Cover

/-- Row 2 (N23): the Thm 4 cover outside the Thm 1 boxes. -/
theorem row_smallRatioT4Rest : SmallRatioT4Rest := by
  intro k μ hab hsum ha _hb hE0 hE1 hd4 _hq hact
  exact thm4_cover k μ hab hsum ha hE0 hE1 hd4 hact

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≤ 4E` of the central square (`N1/SUBROWS.lean`). -/
theorem row_SR_SmallRatio : SR_SmallRatio := by
  intro k μ hab hsum ha _hb2 _hb hd hE1 hd4 hact
  have hE0 : 1 / 1000000 ≤ μ.meanEntropy := by linarith
  exact thm4_cover k μ hab hsum ha hE0 hE1 hd4 hact

end CKLaneN1
