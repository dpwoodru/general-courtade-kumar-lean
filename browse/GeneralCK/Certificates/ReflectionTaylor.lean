import GeneralCK.ReflectionNormalized
import GeneralCK.Certificates.Jet2Bounds
import GeneralCK.Certificates.DyadicJetBounds

namespace GeneralCK.Certificates
open Set

namespace Jet2

/-- The exact jet along a segment, with parameter zero at `c` and one at `x`. -/
def segment (c x : ℝ) : Jet2 :=
  ⟨fun t => c+t*(x-c),fun _ => x-c,fun _ => 0⟩

theorem soundOn_segment (c x : ℝ) (s : Set ℝ) : (segment c x).SoundOn s := by
  intro t _
  constructor
  · convert! ((hasDerivAt_id t).mul_const (x-c)).const_add c using 1
    simp [segment]
  · exact hasDerivAt_const t (x-c)

@[simp] theorem segment_value_zero (c x : ℝ) : (segment c x).value 0 = c := by
  simp [segment]

@[simp] theorem segment_value_one (c x : ℝ) : (segment c x).value 1 = x := by
  simp [segment]

theorem segment_mem_Ioo {c x t : ℝ} (hc : c ∈ Ioo (0:ℝ) 1)
    (hx : x ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    (segment c x).value t ∈ Ioo (0:ℝ) 1 := by
  have hh := convex_Ioo (𝕜 := ℝ) (0:ℝ) 1 hc hx
    (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
  simpa only [smul_eq_mul,segment,show (1-t)*c+t*x=c+t*(x-c) by ring] using hh

end Jet2

namespace ReflectionExpression

/-- The full normalized curvature restricted to a line through a proposed certificate box. -/
noncomputable def segmentJet (ac zc a z : ℝ) : Jet2 :=
  normalized (Jet2.segment ac a) (Jet2.segment zc z)

theorem segmentJet_sound {ac zc a z : ℝ}
    (hac : ac ∈ Ioo (0:ℝ) 1) (hzc : zc ∈ Ioo (0:ℝ) 1)
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : z ∈ Ioo (0:ℝ) 1) :
    (segmentJet ac zc a z).SoundOn (Icc (0:ℝ) 1) :=
  normalized_soundOn (Jet2.soundOn_segment _ _ _) (Jet2.soundOn_segment _ _ _)
    (fun _ ht => Jet2.segment_mem_Ioo hac ha ht)
    (fun _ ht => Jet2.segment_mem_Ioo hzc hz ht)

@[simp] theorem segmentJet_value_zero (ac zc a z : ℝ) :
    (segmentJet ac zc a z).value 0 = normalizedValue ac zc := by
  simp [segmentJet,normalized_value]

@[simp] theorem segmentJet_value_one (ac zc a z : ℝ) :
    (segmentJet ac zc a z).value 1 = normalizedValue a z := by
  simp [segmentJet,normalized_value]

/-- A center value, directional slope, and uniform second-derivative enclosure
certify the actual reflection curvature. All three numerical premises remain explicit. -/
theorem curvature_pos_of_taylor {ac zc a z L A M : ℝ}
    (hac : ac ∈ Ioo (0:ℝ) 1) (hzc : zc ∈ Ioo (0:ℝ) 1)
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : z ∈ Ioo (0:ℝ) 1)
    (hvalue : L ≤ normalizedValue ac zc)
    (hslope : -A ≤ (segmentJet ac zc a z).first 0)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ (segmentJet ac zc a z).second t)
    (haccept : 0 < L-A-M/2) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  apply GeneralCK.Reflection.curvature_pos_of_normalizedValue_pos ha.1 ha.2 hz.1 hz.2
  have hv : L ≤ (segmentJet ac zc a z).value 0 := by simpa using hvalue
  simpa using Jet2.value_pos_of_taylor (segmentJet_sound hac hzc ha hz) hv hslope hsecond haccept

/-- Separate center and whole-segment enclosures preserve the sharper center bounds. -/
theorem curvature_pos_of_jet_enclosures {ac zc a z : ℝ}
    {center whole : JetBounds.JetEnclosure}
    (hac : ac ∈ Ioo (0:ℝ) 1) (hzc : zc ∈ Ioo (0:ℝ) 1)
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : z ∈ Ioo (0:ℝ) 1)
    (hc : center.Contains (segmentJet ac zc a z) 0)
    (hw : whole.ContainsOn (segmentJet ac zc a z) (Icc (0:ℝ) 1))
    (haccept : 0 < center.value.lo+center.first.lo+whole.second.lo/2) :
    0 < GeneralCK.Reflection.curvature a (a*z) := by
  apply curvature_pos_of_taylor hac hzc ha hz
    (L := center.value.lo) (A := -center.first.lo) (M := -whole.second.lo)
  · simpa using hc.1.1
  · simpa using hc.2.1.1
  · intro t ht
    simpa using (hw t ⟨ht.1.le,ht.2.le⟩).2.2.1
  · linarith

/-- Integer acceptance using center value/slope and a whole-segment remainder. -/
def dyadicTaylorCheck {p : ℕ} (center whole : DyadicJetEnclosure p) : Bool :=
  decide (0 < 2*center.value.lo+2*center.first.lo+whole.second.lo)

theorem curvature_pos_of_dyadic_taylor {p : ℕ} {ac zc a z : ℝ}
    {center whole : DyadicJetEnclosure p}
    (hac : ac ∈ Ioo (0:ℝ) 1) (hzc : zc ∈ Ioo (0:ℝ) 1)
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : z ∈ Ioo (0:ℝ) 1)
    (hc : center.Contains (segmentJet ac zc a z) 0)
    (hw : whole.ContainsOn (segmentJet ac zc a z) (Icc (0:ℝ) 1))
    (hcheck : dyadicTaylorCheck center whole=true) :
    0 < GeneralCK.Reflection.curvature a (a*z) := by
  have hn : 0 < 2*center.value.lo+2*center.first.lo+whole.second.lo := by
    simpa [dyadicTaylorCheck] using hcheck
  have hr : (0:ℝ) < 2*(center.value.lo:ℝ)+2*(center.first.lo:ℝ)+(whole.second.lo:ℝ) := by
    exact_mod_cast hn
  apply curvature_pos_of_jet_enclosures hac hzc ha hz
    (DyadicJetEnclosure.contains_toReal_iff.mpr hc)
    (DyadicJetEnclosure.containsOn_toReal_iff.mpr hw)
  change 0 < (center.value.lo:ℝ)/(DyadicInterval.scale p:ℝ)+
    (center.first.lo:ℝ)/(DyadicInterval.scale p:ℝ)+
    (whole.second.lo:ℝ)/(DyadicInterval.scale p:ℝ)/2
  have hs := DyadicInterval.scale_cast_pos p
  apply (mul_pos_iff_of_pos_left hs).mp
  field_simp
  linarith

end ReflectionExpression
end GeneralCK.Certificates
