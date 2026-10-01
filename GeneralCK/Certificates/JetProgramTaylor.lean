import GeneralCK.Certificates.JetProgramShape
import GeneralCK.Certificates.ReflectionTaylor

namespace GeneralCK.Certificates
open Set

namespace DyadicInterval

theorem contains_segment {p : ℕ} {box : DyadicInterval p} {c x t : ℝ}
    (hc : box.Contains c) (hx : box.Contains x) (ht : t ∈ Icc (0:ℝ) 1) :
    box.Contains ((Jet2.segment c x).value t) := by
  apply contains_toReal_iff.mp
  have hh := convex_Icc (𝕜 := ℝ) box.toReal.lo box.toReal.hi
    (contains_toReal_iff.mpr hc) (contains_toReal_iff.mpr hx)
    (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
  simpa only [smul_eq_mul,Jet2.segment,JetBounds.Interval.Contains,Reflection.Bounds,Set.mem_Icc,
    show (1-t)*c+t*x=c+t*(x-c) by ring] using hh

end DyadicInterval

namespace DyadicJetEnclosure

def segmentBox {p : ℕ} (value slope : DyadicInterval p) : DyadicJetEnclosure p :=
  ⟨value,slope,DyadicInterval.ofInt p 0⟩

theorem contains_segment_zero {p : ℕ} {value slope : DyadicInterval p} {c x : ℝ}
    (hv : value.Contains c) (hd : slope.Contains (x-c)) :
    (segmentBox value slope).Contains (Jet2.segment c x) 0 := by
  refine ⟨?_,hd,?_⟩
  · simpa only [segmentBox,Jet2.segment_value_zero] using hv
  · simpa only [segmentBox,Jet2.segment,Int.cast_zero] using DyadicInterval.ofInt_sound p 0

theorem containsOn_segment {p : ℕ} {value slope : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) (hx : value.Contains x) (hd : slope.Contains (x-c)) :
    (segmentBox value slope).ContainsOn (Jet2.segment c x) (Icc (0:ℝ) 1) := by
  intro t ht
  refine ⟨DyadicInterval.contains_segment hc hx ht,hd,?_⟩
  simpa only [segmentBox,Jet2.segment,Int.cast_zero] using DyadicInterval.ofInt_sound p 0

/-- A center enclosure and a separate uniform remainder enclosure describe one jet. -/
theorem value_pos_of_separate_taylor {p : ℕ} {center whole : DyadicJetEnclosure p}
    {j : Jet2} (hs : j.SoundOn (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (ht : ReflectionExpression.dyadicTaylorCheck center whole=true) : 0 < j.value 1 := by
  have hn : 0 < 2*center.value.lo+2*center.first.lo+whole.second.lo := by
    simpa only [ReflectionExpression.dyadicTaylorCheck,decide_eq_true_eq] using ht
  have hr : (0:ℝ) < 2*(center.value.lo:ℝ)+2*(center.first.lo:ℝ)+(whole.second.lo:ℝ) := by
    exact_mod_cast hn
  have hc' := contains_toReal_iff.mpr hc
  have hw' := containsOn_toReal_iff.mpr hw
  apply Jet2.value_pos_of_taylor hs (L := center.toReal.value.lo)
    (A := -center.toReal.first.lo) (M := -whole.toReal.second.lo)
  · exact hc'.1.1
  · simpa only [neg_neg] using hc'.2.1.1
  · intro t ht
    simpa only [neg_neg] using (hw' t ⟨ht.1.le,ht.2.le⟩).2.2.1
  · simp only [neg_div,sub_neg_eq_add]
    change 0 < (center.value.lo:ℝ)/(DyadicInterval.scale p:ℝ)+
      (center.first.lo:ℝ)/(DyadicInterval.scale p:ℝ)+
      (whole.second.lo:ℝ)/(DyadicInterval.scale p:ℝ)/2
    have hscale := DyadicInterval.scale_cast_pos p
    apply (mul_pos_iff_of_pos_left hscale).mp
    field_simp
    linarith

end DyadicJetEnclosure

namespace JetProgram

theorem RegistersContain.nil (p : ℕ) (t : ℝ) :
    RegistersContain ([] : List (DyadicJetEnclosure p)) [] t := by
  refine ⟨rfl,?_⟩
  intro i
  simpa only [List.getD_nil,zeroBox,zeroJet,Int.cast_zero] using DyadicJetEnclosure.contains_const p 0 t

theorem RegistersSound.nil (t : ℝ) : RegistersSound [] t := by
  intro i
  simpa only [List.getD_nil,zeroJet] using Jet2.soundAt_const (0:ℝ) t

/-- Both programs must be accepted and have exactly the same expression. This proves
positivity of their actual output, with no derivative or nonlinear-domain premises. -/
theorem value_pos_of_checked_taylor {p : ℕ} (center whole : List (Instruction p))
    {centerInputs wholeInputs : List (DyadicJetEnclosure p)} {jets : List Jet2} (i : ℕ)
    (hshape : programShape center=programShape whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).SoundOn (Icc (0:ℝ) 1))
    (hcc : check center centerInputs=true) (hwc : check whole wholeInputs=true)
    (ht : ReflectionExpression.dyadicTaylorCheck
      ((finalBoxes center centerInputs).getD i (zeroBox p))
      ((finalBoxes whole wholeInputs).getD i (zeroBox p))=true) :
    0 < ((finalJets whole jets).getD i zeroJet).value 1 := by
  have heq := finalJets_eq_of_programShape center whole hshape jets
  have hcenter := (check_encloses center hc hcc).2 i
  rw [heq] at hcenter
  exact DyadicJetEnclosure.value_pos_of_separate_taylor
    (check_preserves_soundOn whole hw hs hwc i) hcenter
    (fun t ht => (check_encloses whole (hw t ht) hwc).2 i) ht

end JetProgram
end GeneralCK.Certificates
