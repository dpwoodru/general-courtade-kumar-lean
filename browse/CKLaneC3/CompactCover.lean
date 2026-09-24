import CKLaneC3.CompactCell
import GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel

/-!
# Lane C3 — exact rational cover of a rectangle by certified cells and origin cells

A binary split tree over a rational domain (`qValid`, checked by `decide`) whose leaves,
in traversal order, are the rectangles of a list of tags.  A tag is either an origin
rectangle (`s1 + t1 ≤ 2/25`, owned by the origin owner) or a cubic cell certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.CompactCover

open Set GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry E8TAxisRationalTreeBridgeKernel
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.CompactCell

abbrev Tag := RatRect ⊕ CellW

def tagRect : Tag → RatRect
  | .inl q => q
  | .inr w => ⟨w.s0, w.s1, w.t0, w.t1⟩

def tagOK (T : List (List Piece)) : Tag → Bool
  | .inl q => decide (q.s1 + q.t1 ≤ 2 / 25)
  | .inr w => w.check T

theorem qcover : ∀ (tree : Tree) (r : RatRect), qValid tree r →
    ∀ s t : ℝ, r.real.Covers s t → ∃ q ∈ qLeaves tree r, q.real.Covers s t := by
  intro tree
  induction tree with
  | leaf =>
    intro r _ s t h
    exact ⟨r, by simp [qLeaves], h⟩
  | splitS x left right ihl ihr =>
    intro r hv s t h
    rcases hv with ⟨_, _, hvl, hvr⟩
    by_cases hs : s ≤ (x : ℝ)
    · obtain ⟨q, hq, hc⟩ := ihl (qLeftS r x) hvl s t ⟨h.1, hs, h.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inl hq, hc⟩
    · obtain ⟨q, hq, hc⟩ := ihr (qRightS r x) hvr s t ⟨le_of_lt (lt_of_not_ge hs), h.2.1, h.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inr hq, hc⟩
  | splitT x lower upper ihl ihu =>
    intro r hv s t h
    rcases hv with ⟨_, _, hvl, hvu⟩
    by_cases ht : t ≤ (x : ℝ)
    · obtain ⟨q, hq, hc⟩ := ihl (qLowerT r x) hvl s t ⟨h.1, h.2.1, h.2.2.1, ht⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inl hq, hc⟩
    · obtain ⟨q, hq, hc⟩ := ihu (qUpperT r x) hvu s t
        ⟨h.1, h.2.1, le_of_lt (lt_of_not_ge ht), h.2.2.2⟩
      exact ⟨q, by simp only [qLeaves, List.mem_append]; exact Or.inr hq, hc⟩

theorem positive_of_cover {T : List (List Piece)} (hT : TableValid T) {tree : Tree} {D : RatRect}
    {L : List Tag}
    (horigin : E8PositiveOn fun s t => s + t ≤ 2 / 25)
    (hv : qValid tree D) (hleaves : qLeaves tree D = L.map tagRect)
    (hok : L.all (tagOK T) = true) :
    ∀ s t : ℝ, E8Admissible s t → D.real.Covers s t → 0 < e8Delta e8Q s t := by
  intro s t hadm hcov
  obtain ⟨q, hq, hqc⟩ := qcover tree D hv s t hcov
  rw [hleaves] at hq
  obtain ⟨tag, htag, hrect⟩ := List.mem_map.mp hq
  have htok := List.all_eq_true.mp hok tag htag
  cases tag with
  | inl q' =>
    simp only [tagRect] at hrect
    subst hrect
    simp only [tagOK, decide_eq_true_eq] at htok
    apply horigin s t hadm
    have h1 : ((q'.s1 + q'.t1 : ℚ) : ℝ) ≤ ((2 / 25 : ℚ) : ℝ) := by exact_mod_cast htok
    push_cast at h1
    have hs := hqc.2.1
    have ht := hqc.2.2.2
    simp only [RatRect.real] at hs ht
    linarith
  | inr w =>
    simp only [tagRect] at hrect
    subst hrect
    simp only [tagOK] at htok
    apply CellW.check_sound hT htok s t
    simp only [RatRect.real, Rect.Covers] at hqc
    exact hqc

#print axioms qcover
#print axioms positive_of_cover

end CKLaneC3.CompactCover
