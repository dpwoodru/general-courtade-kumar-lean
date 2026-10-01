import GeneralCK.Certificates.BivariateJet2
import GeneralCK.Certificates.Jet2Bounds

namespace GeneralCK.Certificates
open JetBounds

/-- Coordinate coefficients are enclosed before contracting with a segment direction. -/
structure BivariateJetEnclosure where
  value : Interval
  firstA : Interval
  firstZ : Interval
  secondAA : Interval
  secondAZ : Interval
  secondZZ : Interval

namespace BivariateJetEnclosure

def Contains (b : BivariateJetEnclosure) (j : BivariateJet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.firstA.Contains (j.firstA t) ∧
  b.firstZ.Contains (j.firstZ t) ∧ b.secondAA.Contains (j.secondAA t) ∧
  b.secondAZ.Contains (j.secondAZ t) ∧ b.secondZZ.Contains (j.secondZZ t)

def ContainsOn (b : BivariateJetEnclosure) (j : BivariateJet2) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, b.Contains j t

def const (c : ℝ) : BivariateJetEnclosure :=
  ⟨.point c,.point 0,.point 0,.point 0,.point 0,.point 0⟩

def add (b c : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.add c.value,b.firstA.add c.firstA,b.firstZ.add c.firstZ,
    b.secondAA.add c.secondAA,b.secondAZ.add c.secondAZ,b.secondZZ.add c.secondZZ⟩

def neg (b : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.neg,b.firstA.neg,b.firstZ.neg,b.secondAA.neg,b.secondAZ.neg,b.secondZZ.neg⟩

noncomputable def mul (b c : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.mul c.value,
    (b.firstA.mul c.value).add (b.value.mul c.firstA),
    (b.firstZ.mul c.value).add (b.value.mul c.firstZ),
    ((b.secondAA.mul c.value).add (((Interval.point 2).mul b.firstA).mul c.firstA)).add
      (b.value.mul c.secondAA),
    (((b.secondAZ.mul c.value).add (b.firstA.mul c.firstZ)).add (b.firstZ.mul c.firstA)).add
      (b.value.mul c.secondAZ),
    ((b.secondZZ.mul c.value).add (((Interval.point 2).mul b.firstZ).mul c.firstZ)).add
      (b.value.mul c.secondZZ)⟩

/-- The outer Jet2 enclosure is evaluated at the actual inner value. -/
noncomputable def outerCompose (outer : JetEnclosure) (b : BivariateJetEnclosure) :
    BivariateJetEnclosure :=
  ⟨outer.value,outer.first.mul b.firstA,outer.first.mul b.firstZ,
    ((outer.second.mul b.firstA).mul b.firstA).add (outer.first.mul b.secondAA),
    ((outer.second.mul b.firstA).mul b.firstZ).add (outer.first.mul b.secondAZ),
    ((outer.second.mul b.firstZ).mul b.firstZ).add (outer.first.mul b.secondZZ)⟩

theorem contains_const (c t : ℝ) : (const c).Contains (BivariateJet2.const c) t := by
  exact ⟨Interval.contains_point _,Interval.contains_point _,Interval.contains_point _,
    Interval.contains_point _,Interval.contains_point _,Interval.contains_point _⟩

theorem Contains.add {b c : BivariateJetEnclosure} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.1.add hk.2.2.1,
    hj.2.2.2.1.add hk.2.2.2.1,hj.2.2.2.2.1.add hk.2.2.2.2.1,
    hj.2.2.2.2.2.add hk.2.2.2.2.2⟩

theorem Contains.neg {b : BivariateJetEnclosure} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨hj.1.neg,hj.2.1.neg,hj.2.2.1.neg,hj.2.2.2.1.neg,hj.2.2.2.2.1.neg,hj.2.2.2.2.2.neg⟩

theorem Contains.mul {b c : BivariateJetEnclosure} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo := Interval.contains_point (2:ℝ)
  exact ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    (hj.2.2.1.mul hk.1).add (hj.1.mul hk.2.2.1),
    ((hj.2.2.2.1.mul hk.1).add ((htwo.mul hj.2.1).mul hk.2.1)).add (hj.1.mul hk.2.2.2.1),
    (((hj.2.2.2.2.1.mul hk.1).add (hj.2.1.mul hk.2.2.1)).add
      (hj.2.2.1.mul hk.2.1)).add (hj.1.mul hk.2.2.2.2.1),
    ((hj.2.2.2.2.2.mul hk.1).add ((htwo.mul hj.2.2.1).mul hk.2.2.1)).add
      (hj.1.mul hk.2.2.2.2.2)⟩

theorem Contains.outerCompose {outer : JetEnclosure} {b : BivariateJetEnclosure}
    {f : Jet2} {j : BivariateJet2} {t : ℝ} (hf : outer.Contains f (j.value t))
    (hj : b.Contains j t) : (outerCompose outer b).Contains (BivariateJet2.outerCompose f j) t := by
  exact ⟨hf.1,hf.2.1.mul hj.2.1,hf.2.1.mul hj.2.2.1,
    by simpa only [BivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.1).mul hj.2.1).add (hf.2.1.mul hj.2.2.2.1),
    ((hf.2.2.mul hj.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.1),
    by simpa only [BivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.2)⟩

end BivariateJetEnclosure
end GeneralCK.Certificates
