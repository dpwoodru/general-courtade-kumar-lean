import GeneralCK.Certificates.E8CompactAnchorDeltaJet
import GeneralCK.Certificates.E8TAxisStableInterval
import GeneralCK.Certificates.E8TAxisMixedCoefficients

/-! Exact dyadic enclosures for the actual compact-anchor directional jets. -/

namespace GeneralCK.Certificates.E8CompactAnchorInterval

open E8TAxisDeltaDirectionalJet E8CompactAnchorDeltaJet
open E8TAxisStableInterval E8TAxisMixedCoefficients DyadicInterval

def slopeBox {p : ℕ} (b : DyadicJet5Enclosure p) (m : ℤ) : DyadicJet5Enclosure p :=
  ⟨b.d0, b.d1.mul (ofInt p m), b.d2.mul (ofInt p (m ^ 2)),
    b.d3.mul (ofInt p (m ^ 3)), b.d4.mul (ofInt p (m ^ 4)),
    b.d5.mul (ofInt p (m ^ 5))⟩

theorem slopeBox_contains {p : ℕ} {b : DyadicJet5Enclosure p} {j : Jet5}
    {c u : ℝ} (m : ℤ) (h : b.Contains j (c + (m : ℝ) * u)) :
    (slopeBox b m).Contains (affine j c m) u := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  refine ⟨h0, mul_sound h1 (ofInt_sound p m), ?_, ?_, ?_, ?_⟩
  · have hterm := mul_sound h2 (ofInt_sound p (m ^ 2))
    have hpow : ((m ^ 2 : ℤ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h3 (ofInt_sound p (m ^ 3))
    have hpow : ((m ^ 3 : ℤ) : ℝ) = (m : ℝ) ^ 3 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h4 (ofInt_sound p (m ^ 4))
    have hpow : ((m ^ 4 : ℤ) : ℝ) = (m : ℝ) ^ 4 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h5 (ofInt_sound p (m ^ 5))
    have hpow : ((m ^ 5 : ℤ) : ℝ) = (m : ℝ) ^ 5 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm

def graphBox {p : ℕ} (a b c d : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ((b.add (negative d)).mul (c.add (negative a))).add
    (negative ((b.add (negative c)).mul (d.add a)))

theorem graphBox_contains {p : ℕ} {a b c d : DyadicJet5Enclosure p}
    {A B C D : Jet5} {u : ℝ}
    (ha : a.Contains A u) (hb : b.Contains B u)
    (hc : c.Contains C u) (hd : d.Contains D u) :
    (graphBox a b c d).Contains (deltaGraph A B C D) u :=
  ((hb.add (negative_sound hd)).mul (hc.add (negative_sound ha))).add
    (negative_sound ((hb.add (negative_sound hc)).mul (hd.add ha)))

structure Boxes (p : ℕ) where
  a : DyadicJet5Enclosure p
  b : DyadicJet5Enclosure p
  c : DyadicJet5Enclosure p
  d : DyadicJet5Enclosure p

def Boxes.ContainsAt {p : ℕ} (b : Boxes p) (s t : ℝ) : Prop :=
  b.a.Contains qJet t ∧ b.b.Contains qJet (2 * s + t) ∧
    b.c.Contains qJet (s + t) ∧ b.d.Contains qJet s

def Boxes.direction {p : ℕ} (b : Boxes p) (ds dt : ℤ) : DyadicJet5Enclosure p :=
  graphBox (slopeBox b.a dt) (slopeBox b.b (2 * ds + dt))
    (slopeBox b.c (ds + dt)) (slopeBox b.d ds)

theorem Boxes.direction_contains {p : ℕ} {b : Boxes p} {s0 t0 u : ℝ}
    (ds dt : ℤ) (h : b.ContainsAt (s0 + (ds : ℝ) * u) (t0 + (dt : ℝ) * u)) :
    (b.direction ds dt).Contains (deltaJet s0 t0 ds dt) u := by
  apply graphBox_contains
  · exact slopeBox_contains dt h.1
  · have heq : (2 * s0 + t0) + ((2 * ds + dt : ℤ) : ℝ) * u =
        2 * (s0 + (ds : ℝ) * u) + (t0 + (dt : ℝ) * u) := by push_cast; ring
    have hb : b.b.Contains qJet ((2 * s0 + t0) + ((2 * ds + dt : ℤ) : ℝ) * u) := by
      rw [heq]
      exact h.2.1
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using slopeBox_contains (2 * ds + dt) hb
  · have heq : (s0 + t0) + ((ds + dt : ℤ) : ℝ) * u =
        (s0 + (ds : ℝ) * u) + (t0 + (dt : ℝ) * u) := by push_cast; ring
    have hc : b.c.Contains qJet ((s0 + t0) + ((ds + dt : ℤ) : ℝ) * u) := by
      rw [heq]
      exact h.2.2.1
    simpa only [Int.cast_add] using slopeBox_contains (ds + dt) hc
  · exact slopeBox_contains ds h.2.2.2

theorem Boxes.directionAt_contains {p : ℕ} {b : Boxes p} {s t : ℝ}
    (ds dt : ℤ) (h : b.ContainsAt s t) :
    (b.direction ds dt).Contains (deltaJet s t ds dt) 0 := by
  apply Boxes.direction_contains
  simpa only [mul_zero, add_zero] using h

def Boxes.coeff {p : ℕ} (b : Boxes p) (i j : ℕ) : DyadicInterval p :=
  mixedBox b.a b.b b.c b.d i j

theorem Boxes.coeff_contains {p : ℕ} {b : Boxes p} {s t : ℝ}
    (h : b.ContainsAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed qJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

#print axioms slopeBox_contains
#print axioms graphBox_contains
#print axioms Boxes.direction_contains
#print axioms Boxes.directionAt_contains
#print axioms Boxes.coeff_contains

end GeneralCK.Certificates.E8CompactAnchorInterval
