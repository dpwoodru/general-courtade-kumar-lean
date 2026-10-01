import GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor
import GeneralCK.Certificates.E8TAxisPartitionKernel

/-!
# Reusable certificate schema for positive-t E8 t-axis cells

This separates the analytic Taylor argument from generated cell data.  A
generated cell supplies exact geometry, displacement enclosures, mixed
coefficient enclosures, and one closed positivity check.
-/

namespace GeneralCK.Certificates.E8TAxisCellCertificateSchema

open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients E8TAxisGeneralCenteredTaylor
open E8TAxisPartitionKernel

set_option maxHeartbeats 1000000

/-- Every segment from a point inside a rectangle to another point inside it
stays in that rectangle. -/
theorem segment_covers {r : Rect} {s0 t0 s t u : ℝ}
    (hc : r.Covers s0 t0) (h : r.Covers s t) (hu : u ∈ Icc (0 : ℝ) 1) :
    r.Covers (s0 + (s - s0) * u) (t0 + (t - t0) * u) := by
  have segment {a b c x : ℝ} (hc' : c ∈ Icc a b) (hx : x ∈ Icc a b) :
      c + (x - c) * u ∈ Icc a b := by
    have hh := (convex_Icc a b) hc' hx (sub_nonneg.mpr hu.2) hu.1
      (show (1 - u) + u = 1 by ring)
    convert hh using 1 <;> simp only [smul_eq_mul] <;> ring
  have hs := segment ⟨hc.1, hc.2.1⟩ ⟨h.1, h.2.1⟩
  have ht := segment ⟨hc.2.2.1, hc.2.2.2⟩ ⟨h.2.2.1, h.2.2.2⟩
  exact ⟨hs.1, hs.2, ht.1, ht.2⟩

structure Certificate (p : ℕ) where
  rectangle : Rect
  centerS : ℝ
  centerT : ℝ
  data : Data p

namespace Certificate

/-- The common semantic assembly theorem for every generated positive-t
cell.  All expensive work is confined to the five certificate premises. -/
theorem replay_contains {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hrange : ∀ s t, c.rectangle.Covers s t → InputsInRange s t)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed qJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed qJet s t))
    {s t : ℝ} (h : c.rectangle.Covers s t) :
    c.data.replay.Contains (e8RegularDeltaT s t) := by
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1,
      InputsInRange (c.centerS + (s - c.centerS) * u)
        (c.centerT + (t - c.centerT) * u) := by
    intro u hu
    exact hrange _ _ (segment_covers hcenter h hu)
  have hrem : ∀ u ∈ Ioo (0 : ℝ) 1,
      c.data.RemainderEnclosed
        (mixed qJet (c.centerS + (s - c.centerS) * u)
          (c.centerT + (t - c.centerT) * u)) := by
    intro u hu
    exact hr _ _ (segment_covers hcenter h ⟨hu.1.le, hu.2.le⟩)
  have hh := Data.replay_contains hseg hc hrem (hds _ _ h) (hdt _ _ h)
  simpa only [show c.centerS + (s - c.centerS) = s by ring,
    show c.centerT + (t - c.centerT) = t by ring] using hh

theorem cellPositive {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hrange : ∀ s t, c.rectangle.Covers s t → InputsInRange s t)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed qJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed qJet s t))
    (hp : c.data.replay.positiveCheck = true) : CellPositive c.rectangle := by
  intro s t _ h
  exact positiveCheck_sound hp (c.replay_contains hcenter hrange hds hdt hc hr h)

end Certificate

#print axioms segment_covers
#print axioms Certificate.replay_contains
#print axioms Certificate.cellPositive

end GeneralCK.Certificates.E8TAxisCellCertificateSchema
