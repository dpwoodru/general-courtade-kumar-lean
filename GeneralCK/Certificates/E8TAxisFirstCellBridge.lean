import GeneralCK.Certificates.E8TAxisBivariateTaylor
import GeneralCK.Certificates.E8TAxisOneCellGeometry

/-!
# Exact remaining certificate interface for the first historical E8 cell

Differentiation, mixed-derivative weights, Taylor's theorem, rectangle
geometry, range membership, and dyadic arithmetic are all discharged.
The remaining input is exactly containment of the ten center coefficients
and five fourth-order remainder coefficients in the saved derivative boxes.
-/

namespace GeneralCK.Certificates.E8TAxisFirstCellBridge

open GeneralCK E8TAxisOneCellGeometry E8TAxisMixedCoefficients
open E8TAxisDeltaDirectionalJet E8TAxisCenteredReplaySoundness
open E8TAxisOneCellArithmetic DyadicInterval

/-- The precise remaining coefficient enclosure statement. It contains no
Taylor formula, derivative-matching hypothesis, or positivity conclusion. -/
def MixedBounds : Prop :=
  CenterEnclosed (mixed qJet centerS centerT) ∧
    ∀ s t, InFirstCell s t → RemainderEnclosed (mixed qJet s t)

theorem centeredReplay_contains_of_mixedBounds (hb : MixedBounds)
    {s t : ℝ} (h : InFirstCell s t) :
    centeredReplay.Contains (e8RegularDeltaT s t) := by
  have hd := displacement_mem h
  have hh := E8TAxisBivariateTaylor.centeredReplay_contains
    (segment_inputsInRange h) hb.1
    (fun u hu => hb.2 _ _ (segment_mem h ⟨hu.1.le, hu.2.le⟩)) hd.1 hd.2
  simpa only [show centerS + (s - centerS) = s by ring,
    show centerT + (t - centerT) = t by ring] using hh

theorem positive_of_mixedBounds (hb : MixedBounds)
    {s t : ℝ} (h : InFirstCell s t) : 0 < e8RegularDeltaT s t :=
  positiveCheck_sound centeredReplay_positive (centeredReplay_contains_of_mixedBounds hb h)

/-- Four raw inverse-jet boxes, ordered by the actual inverse arguments. -/
structure InverseBoxes (p : ℕ) where
  a : DyadicJet5Enclosure p
  b : DyadicJet5Enclosure p
  c : DyadicJet5Enclosure p
  d : DyadicJet5Enclosure p

def InverseBoxes.ContainsAt {p : ℕ} (b : InverseBoxes p) (s t : ℝ) : Prop :=
  b.a.Contains qJet t ∧ b.b.Contains qJet (2*s+t) ∧
    b.c.Contains qJet (s+t) ∧ b.d.Contains qJet s

def InverseBoxes.coeff {p : ℕ} (b : InverseBoxes p) (i j : ℕ) : DyadicInterval p :=
  mixedBox b.a b.b b.c b.d i j

theorem InverseBoxes.coeff_sound {p : ℕ} {b : InverseBoxes p} {s t : ℝ}
    (h : b.ContainsAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed qJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

def CenterAccepted (b : InverseBoxes precision) : Prop :=
  (b.coeff 0 1).subsetCheck initial = true ∧
  (b.coeff 0 2).subsetCheck der_0_2 = true ∧
  (b.coeff 1 1).subsetCheck der_1_1 = true ∧
  (b.coeff 0 3).subsetCheck der_0_3 = true ∧
  (b.coeff 1 2).subsetCheck der_1_2 = true ∧
  (b.coeff 2 1).subsetCheck der_2_1 = true ∧
  (b.coeff 0 4).subsetCheck der_0_4 = true ∧
  (b.coeff 1 3).subsetCheck der_1_3 = true ∧
  (b.coeff 2 2).subsetCheck der_2_2 = true ∧
  (b.coeff 3 1).subsetCheck der_3_1 = true

def RemainderAccepted (b : InverseBoxes precision) : Prop :=
  (b.coeff 0 5).subsetCheck der_0_5 = true ∧
  (b.coeff 1 4).subsetCheck der_1_4 = true ∧
  (b.coeff 2 3).subsetCheck der_2_3 = true ∧
  (b.coeff 3 2).subsetCheck der_3_2 = true ∧
  (b.coeff 4 1).subsetCheck der_4_1 = true

theorem centerAccepted_sound {b : InverseBoxes precision} {s t : ℝ}
    (ha : CenterAccepted b) (h : b.ContainsAt s t) :
    CenterEnclosed (mixed qJet s t) := by
  rcases ha with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨subsetCheck_sound h0 (InverseBoxes.coeff_sound h 0 1),
    subsetCheck_sound h1 (InverseBoxes.coeff_sound h 0 2),
    subsetCheck_sound h2 (InverseBoxes.coeff_sound h 1 1),
    subsetCheck_sound h3 (InverseBoxes.coeff_sound h 0 3),
    subsetCheck_sound h4 (InverseBoxes.coeff_sound h 1 2),
    subsetCheck_sound h5 (InverseBoxes.coeff_sound h 2 1),
    subsetCheck_sound h6 (InverseBoxes.coeff_sound h 0 4),
    subsetCheck_sound h7 (InverseBoxes.coeff_sound h 1 3),
    subsetCheck_sound h8 (InverseBoxes.coeff_sound h 2 2),
    subsetCheck_sound h9 (InverseBoxes.coeff_sound h 3 1)⟩

theorem remainderAccepted_sound {b : InverseBoxes precision} {s t : ℝ}
    (ha : RemainderAccepted b) (h : b.ContainsAt s t) :
    RemainderEnclosed (mixed qJet s t) := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨subsetCheck_sound h0 (InverseBoxes.coeff_sound h 0 5),
    subsetCheck_sound h1 (InverseBoxes.coeff_sound h 1 4),
    subsetCheck_sound h2 (InverseBoxes.coeff_sound h 2 3),
    subsetCheck_sound h3 (InverseBoxes.coeff_sound h 3 2),
    subsetCheck_sound h4 (InverseBoxes.coeff_sound h 4 1)⟩

theorem mixedBounds_of_inverse_boxes {center whole : InverseBoxes precision}
    (hcenter : center.ContainsAt centerS centerT)
    (hwhole : ∀ s t, InFirstCell s t → whole.ContainsAt s t)
    (hc : CenterAccepted center) (hr : RemainderAccepted whole) : MixedBounds :=
  ⟨centerAccepted_sound hc hcenter,
    fun s t h => remainderAccepted_sound hr (hwhole s t h)⟩

/-- The complete semantic implication needed by a first-cell inverse-jet
replay. No analytic smoothness or Taylor premise remains in this theorem. -/
theorem centeredReplay_contains_of_inverse_boxes {center whole : InverseBoxes precision}
    (hcenter : center.ContainsAt centerS centerT)
    (hwhole : ∀ s t, InFirstCell s t → whole.ContainsAt s t)
    (hc : CenterAccepted center) (hr : RemainderAccepted whole)
    {s t : ℝ} (h : InFirstCell s t) :
    centeredReplay.Contains (e8RegularDeltaT s t) :=
  centeredReplay_contains_of_mixedBounds (mixedBounds_of_inverse_boxes hcenter hwhole hc hr) h

#print axioms centeredReplay_contains_of_mixedBounds
#print axioms positive_of_mixedBounds
#print axioms centeredReplay_contains_of_inverse_boxes

end GeneralCK.Certificates.E8TAxisFirstCellBridge
