import GeneralCK.PureGapCompactMean

/-!
# Fixed-entropy closure of the retained pure-gap argument

This packages the compact-minimum argument of the manuscript.  Once each
boundary face is owned and E8 excludes a negative smooth-interior local
minimum, no negative value can remain on the retained chamber.
-/

namespace GeneralCK
open Set

/-- The fixed-entropy retained gap is nonnegative once its six boundary
faces and its smooth-interior local minima are ruled out. -/
theorem canonicalPureGap_nonneg_on_retained_of_owners
    {S e f : ℝ} (hS : S ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hseam : ∀ p ∈ retainedMeanSet S e f,
      p.1 + p.2 = S → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hequal : ∀ p ∈ retainedMeanSet S e f,
      p.1 = p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hleftHalf : ∀ p ∈ retainedMeanSet S e f,
      p.1 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hrightHalf : ∀ p ∈ retainedMeanSet S e f,
      p.2 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hleftCap : ∀ p ∈ retainedMeanSet S e f,
      e = H p.1 → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hrightCap : ∀ p ∈ retainedMeanSet S e f,
      f = H p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f)
    (hinterior : ∀ p ∈ retainedMeanInteriorSet S e f,
      IsLocalMin (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) p →
      0 ≤ canonicalPureGap p.1 p.2 e f) :
    ∀ p ∈ retainedMeanSet S e f, 0 ≤ canonicalPureGap p.1 p.2 e f := by
  intro p hp
  by_contra hpnonneg
  have hpneg : canonicalPureGap p.1 p.2 e f < 0 := lt_of_not_ge hpnonneg
  have he₁ : e ≤ 1 := hp.1.2.2.2.1.trans (H_le_one p.1)
  have hf₁ : f ≤ 1 := hp.1.2.2.2.2.trans (H_le_one p.2)
  obtain ⟨q, hq, hmin, hcase⟩ :=
    exists_retained_min_boundary_or_localMin hS he hf he₁ hf₁
  have hqneg : canonicalPureGap q.1 q.2 e f < 0 :=
    lt_of_le_of_lt (hmin hp) hpneg
  rcases hcase with hsum | heq | haHalf | hcHalf | hecap | hfcap | hlocal
  · exact (not_lt_of_ge (hseam q hq hsum)) hqneg
  · exact (not_lt_of_ge (hequal q hq heq)) hqneg
  · exact (not_lt_of_ge (hleftHalf q hq haHalf)) hqneg
  · exact (not_lt_of_ge (hrightHalf q hq hcHalf)) hqneg
  · exact (not_lt_of_ge (hleftCap q hq hecap)) hqneg
  · exact (not_lt_of_ge (hrightCap q hq hfcap)) hqneg
  · have hstrict := retainedMeanSet_boundary_or_interior he hq
    rcases hstrict with hsum | heq | haHalf | hcHalf | hecap | hfcap | hstrict
    · exact (not_lt_of_ge (hseam q hq hsum)) hqneg
    · exact (not_lt_of_ge (hequal q hq heq)) hqneg
    · exact (not_lt_of_ge (hleftHalf q hq haHalf)) hqneg
    · exact (not_lt_of_ge (hrightHalf q hq hcHalf)) hqneg
    · exact (not_lt_of_ge (hleftCap q hq hecap)) hqneg
    · exact (not_lt_of_ge (hrightCap q hq hfcap)) hqneg
    · exact (not_lt_of_ge (hinterior q hstrict hlocal)) hqneg

/-- The exact collection of value owners and the E8 exclusion needed after
canonicalizing and entropy-ordering the retained pure gap. -/
structure CanonicalPureGapOwners (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → 0 ≤ canonicalPureGap p.1 p.2 e f
  equal : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 = p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.2 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    e = H p.1 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    f = H p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  interior : ∀ e f p, 0 < e → 0 < f → e ≤ f →
    p ∈ retainedMeanInteriorSet S e f →
    IsLocalMin (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) p →
    0 ≤ canonicalPureGap p.1 p.2 e f

/-- The manuscript's fixed-entropy owner ledger implies the global positive-
entropy pure-gap theorem. -/
theorem pureGap_nonneg_of_canonicalPureGapOwners {S : ℝ} (hS : S ≤ 1)
    (howners : CanonicalPureGapOwners S)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f := by
  apply pureGap_nonneg_of_canonicalPureGap _ ha₀ ha₁ hb₀ hb₁ he hf hecap hfcap
  intro x y g h hx hxy hy hg hgh hgcap hhcap
  let p : ℝ × ℝ := (x, y)
  have hpCanonical : p ∈ canonicalMeanSet g h :=
    ⟨hx, hxy, hy, hgcap, hhcap⟩
  by_cases hsmall : x + y < S
  · exact howners.small g h p hg (hg.trans_le hgh) hgh hpCanonical hsmall
  have hpRetained : p ∈ retainedMeanSet S g h :=
    ⟨hpCanonical, le_of_not_gt hsmall⟩
  apply canonicalPureGap_nonneg_on_retained_of_owners hS hg (hg.trans_le hgh)
    (fun q hq hsum => howners.seam g h q hg (hg.trans_le hgh) hgh hq hsum)
    (fun q hq heq => howners.equal g h q hg (hg.trans_le hgh) hgh hq heq)
    (fun q hq heq => howners.leftHalf g h q hg (hg.trans_le hgh) hgh hq heq)
    (fun q hq heq => howners.rightHalf g h q hg (hg.trans_le hgh) hgh hq heq)
    (fun q hq heq => howners.leftCap g h q hg (hg.trans_le hgh) hgh hq heq)
    (fun q hq heq => howners.rightCap g h q hg (hg.trans_le hgh) hgh hq heq)
    (fun q hq hmin => howners.interior g h q hg (hg.trans_le hgh) hgh hq hmin)
    p hpRetained

end GeneralCK
