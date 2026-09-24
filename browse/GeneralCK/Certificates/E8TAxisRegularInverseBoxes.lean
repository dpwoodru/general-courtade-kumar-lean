import GeneralCK.Certificates.E8TAxisFirstCellBridge
import GeneralCK.Certificates.E8TAxisRegularGermJet

/-! The existing four-box arithmetic interpreted through the regular jet. -/
namespace GeneralCK.Certificates.E8TAxisFirstCellBridge

open E8TAxisRegularGermJet E8TAxisMixedCoefficients

def InverseBoxes.ContainsRegularAt {p : ℕ} (b : InverseBoxes p) (s t : ℝ) : Prop :=
  b.a.Contains regularQJet t ∧ b.b.Contains regularQJet (2*s+t) ∧
    b.c.Contains regularQJet (s+t) ∧ b.d.Contains regularQJet s

theorem InverseBoxes.coeff_regular_sound {p : ℕ} {b : InverseBoxes p} {s t : ℝ}
    (h : b.ContainsRegularAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed regularQJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

#print axioms InverseBoxes.coeff_regular_sound
end GeneralCK.Certificates.E8TAxisFirstCellBridge
