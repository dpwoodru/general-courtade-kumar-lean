import GeneralCK.Certificates.BivariateJetProgram
import GeneralCK.Certificates.BivariateJetTaylor
import GeneralCK.Certificates.JetProgramTaylor

namespace GeneralCK.Certificates
open Set

namespace DyadicBivariateJetEnclosure

theorem contains_affineA_zero {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) :
    (coordinateA value).Contains (BivariateJet2.affineA c x) 0 := by
  apply contains_coordinateA
  simpa using hc

theorem contains_affineZ_zero {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) :
    (coordinateZ value).Contains (BivariateJet2.affineZ c x) 0 := by
  apply contains_coordinateZ
  simpa using hc

theorem containsOn_affineA {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) (hx : value.Contains x) :
    (coordinateA value).ContainsOn (BivariateJet2.affineA c x) (Icc (0:ℝ) 1) := by
  intro t ht
  exact contains_coordinateA (DyadicInterval.contains_segment hc hx ht)

theorem containsOn_affineZ {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) (hx : value.Contains x) :
    (coordinateZ value).ContainsOn (BivariateJet2.affineZ c x) (Icc (0:ℝ) 1) := by
  intro t ht
  exact contains_coordinateZ (DyadicInterval.contains_segment hc hx ht)

/-- Convert separately checked coordinate enclosures to the real Taylor rule.
The center and uniform enclosures may use different dyadic precisions. -/
theorem value_pos_of_separate_taylor {p q : ℕ}
    {center : DyadicBivariateJetEnclosure p} {whole : DyadicBivariateJetEnclosure q}
    {j : BivariateJet2} {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower center.toReal whole.toReal ra rz) :
    0<j.value 1 :=
  BivariateJetEnclosure.value_pos_of_taylor hs (contains_toReal_iff.mpr hc)
    (containsOn_toReal_iff.mpr hw) hra hrz hda hdz ht

end DyadicBivariateJetEnclosure

namespace BivariateJetProgram

/-- Accepted programs of exactly the same witness-free shape prove positivity
of their actual output. Nonlinear derivative domains follow from the checker;
the only soundness premises concern the initial affine/constant inputs. -/
theorem value_pos_of_checked_taylor {p q : ℕ}
    (center : List (Instruction p)) (whole : List (Instruction q))
    {centerInputs : List (DyadicBivariateJetEnclosure p)}
    {wholeInputs : List (DyadicBivariateJetEnclosure q)} {jets : List BivariateJet2}
    (i : ℕ) {da dz ra rz : ℝ}
    (hshape : shapes center=shapes whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hcc : check center centerInputs=true) (hwc : check whole wholeInputs=true)
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower
      ((finalBoxes center centerInputs).getD i (zeroBox p)).toReal
      ((finalBoxes whole wholeInputs).getD i (zeroBox q)).toReal ra rz) :
    0<((finalJets whole jets).getD i zeroJet).value 1 := by
  have heq := finalJets_eq_of_shapes_eq hshape jets
  have hcenter := (check_encloses center hc hcc).2 i
  rw [heq] at hcenter
  exact DyadicBivariateJetEnclosure.value_pos_of_separate_taylor
    (check_preserves_soundOn whole hw hs hwc i) hcenter
    (fun t ht => (check_encloses whole (hw t ht) hwc).2 i) hra hrz hda hdz ht

end BivariateJetProgram
end GeneralCK.Certificates
