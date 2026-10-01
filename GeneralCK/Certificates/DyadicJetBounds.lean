import GeneralCK.Certificates.DyadicInterval
import GeneralCK.Certificates.Jet2Bounds

namespace GeneralCK.Certificates

namespace DyadicInterval

noncomputable def toReal {p : ℕ} (a : DyadicInterval p) : JetBounds.Interval :=
  ⟨(a.lo:ℝ)/(scale p:ℝ),(a.hi:ℝ)/(scale p:ℝ)⟩

theorem contains_toReal_iff {p : ℕ} {a : DyadicInterval p} {x : ℝ} :
    a.toReal.Contains x ↔ a.Contains x := by
  change (a.lo:ℝ)/(scale p:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)/(scale p:ℝ) ↔ _
  rw [div_le_iff₀ (scale_cast_pos p),le_div_iff₀ (scale_cast_pos p)]
  simp only [Contains,mul_comm]

theorem toReal_positive_iff {p : ℕ} {a : DyadicInterval p} :
    0 < a.toReal.lo ↔ 0 < a.lo := by
  change 0 < (a.lo:ℝ)/(scale p:ℝ) ↔ _
  rw [div_pos_iff_of_pos_right (scale_cast_pos p)]
  exact Int.cast_pos

end DyadicInterval

/-- Computable fixed-scale enclosures of the three explicit jet components. -/
structure DyadicJetEnclosure (p : ℕ) where
  value : DyadicInterval p
  first : DyadicInterval p
  second : DyadicInterval p
  deriving DecidableEq, Repr

namespace DyadicJetEnclosure
open DyadicInterval

noncomputable def toReal {p : ℕ} (b : DyadicJetEnclosure p) : JetBounds.JetEnclosure :=
  ⟨b.value.toReal,b.first.toReal,b.second.toReal⟩

def Contains {p : ℕ} (b : DyadicJetEnclosure p) (j : Jet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.first.Contains (j.first t) ∧ b.second.Contains (j.second t)

def ContainsOn {p : ℕ} (b : DyadicJetEnclosure p) (j : Jet2) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, b.Contains j t

theorem contains_toReal_iff {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2} {t : ℝ} :
    b.toReal.Contains j t ↔ b.Contains j t := by
  simp only [toReal,JetBounds.JetEnclosure.Contains,Contains,DyadicInterval.contains_toReal_iff]

theorem containsOn_toReal_iff {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2} {s : Set ℝ} :
    b.toReal.ContainsOn j s ↔ b.ContainsOn j s := by
  simp only [JetBounds.JetEnclosure.ContainsOn,ContainsOn,contains_toReal_iff]

def const (p : ℕ) (z : ℤ) : DyadicJetEnclosure p := ⟨ofInt p z,ofInt p 0,ofInt p 0⟩
def variableJet {p : ℕ} (i : DyadicInterval p) : DyadicJetEnclosure p := ⟨i,ofInt p 1,ofInt p 0⟩
def add {p : ℕ} (b c : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  ⟨b.value.add c.value,b.first.add c.first,b.second.add c.second⟩
def neg {p : ℕ} (b : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  ⟨b.value.neg,b.first.neg,b.second.neg⟩
def mul {p : ℕ} (b c : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  ⟨b.value.mul c.value,
   (b.first.mul c.value).add (b.value.mul c.first),
   ((b.second.mul c.value).add (((ofInt p 2).mul b.first).mul c.first)).add (b.value.mul c.second)⟩
def inv {p : ℕ} (b : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  let r := b.value.recip
  let r2 := r.mul r
  let r3 := r2.mul r
  ⟨r,b.first.neg.mul r2,
   (((ofInt p 2).mul (b.first.mul b.first)).mul r3).sub (b.second.mul r2)⟩
def comp {p : ℕ} (b c : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  ⟨b.value,b.first.mul c.first,
   (b.second.mul (c.first.mul c.first)).add (b.first.mul c.second)⟩

theorem contains_const (p : ℕ) (z : ℤ) (t : ℝ) : (const p z).Contains (Jet2.const z) t :=
  ⟨ofInt_sound p z,by simpa [const,Jet2.const] using ofInt_sound p 0,
    by simpa [const,Jet2.const] using ofInt_sound p 0⟩

theorem contains_variable {p : ℕ} {i : DyadicInterval p} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet2.variableJet t :=
  ⟨ht,by simpa [variableJet,Jet2.variableJet] using ofInt_sound p 1,
    by simpa [variableJet,Jet2.variableJet] using ofInt_sound p 0⟩

theorem Contains.add {p : ℕ} {b c : DyadicJetEnclosure p} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨add_sound hj.1 hk.1,add_sound hj.2.1 hk.2.1,add_sound hj.2.2 hk.2.2⟩

theorem Contains.neg {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨neg_sound hj.1,neg_sound hj.2.1,neg_sound hj.2.2⟩

theorem Contains.mul {p : ℕ} {b c : DyadicJetEnclosure p} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact ⟨mul_sound hj.1 hk.1,add_sound (mul_sound hj.2.1 hk.1) (mul_sound hj.1 hk.2.1),
    add_sound (add_sound (mul_sound hj.2.2 hk.1) (mul_sound (mul_sound htwo hj.2.1) hk.2.1))
      (mul_sound hj.1 hk.2.2)⟩

theorem Contains.inv {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hb : 0 < b.value.lo) : b.inv.Contains j.inv t := by
  have hr := recip_sound hb hj.1
  have hr2 := mul_sound hr hr
  have hr3 := mul_sound hr2 hr
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  refine ⟨hr,?_,?_⟩
  · simpa only [DyadicJetEnclosure.inv,Jet2.inv,div_eq_mul_inv,pow_two,mul_inv_rev] using
      mul_sound (neg_sound hj.2.1) hr2
  · convert! sub_sound (mul_sound (mul_sound htwo (mul_sound hj.2.1 hj.2.1)) hr3)
      (mul_sound hj.2.2 hr2) using 1
    simp only [Jet2.inv,div_eq_mul_inv]
    ring

theorem Contains.comp {p : ℕ} {b c : DyadicJetEnclosure p} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j (k.value t)) (hk : c.Contains k t) :
    (b.comp c).Contains (j.comp k) t := by
  refine ⟨hj.1,mul_sound hj.2.1 hk.2.1,?_⟩
  simpa only [DyadicJetEnclosure.comp,Jet2.comp,pow_two] using
    add_sound (mul_sound hj.2.2 (mul_sound hk.2.1 hk.2.1)) (mul_sound hj.2.1 hk.2.2)

def subsetCheck {p : ℕ} (b out : DyadicJetEnclosure p) : Bool :=
  b.value.subsetCheck out.value && b.first.subsetCheck out.first && b.second.subsetCheck out.second
def invCheck {p : ℕ} (b out : DyadicJetEnclosure p) : Bool :=
  b.value.positiveCheck && b.inv.subsetCheck out

theorem subsetCheck_sound {p : ℕ} {b out : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (h : b.subsetCheck out=true) (hj : b.Contains j t) : out.Contains j t := by
  have hh := Bool.and_eq_true_iff.mp h
  have hvf := Bool.and_eq_true_iff.mp hh.1
  exact ⟨DyadicInterval.subsetCheck_sound hvf.1 hj.1,
    DyadicInterval.subsetCheck_sound hvf.2 hj.2.1,DyadicInterval.subsetCheck_sound hh.2 hj.2.2⟩

theorem invCheck_sound {p : ℕ} {b out : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (h : b.invCheck out=true) (hj : b.Contains j t) : out.Contains j.inv t := by
  have hh := Bool.and_eq_true_iff.mp h
  have hp : 0 < b.value.lo := by simpa [positiveCheck] using hh.1
  exact subsetCheck_sound hh.2 (hj.inv hp)

def taylorCheck {p : ℕ} (b : DyadicJetEnclosure p) : Bool :=
  decide (0 < 2*b.value.lo+2*b.first.lo+b.second.lo)

/-- A kernel-computable integer acceptance test implies the real Taylor conclusion. -/
theorem taylorCheck_sound {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2}
    (hj : j.SoundOn (Set.Icc (0:ℝ) 1)) (hb : b.ContainsOn j (Set.Icc (0:ℝ) 1))
    (h : b.taylorCheck=true) : 0 < j.value 1 := by
  have hz : 0 < 2*b.value.lo+2*b.first.lo+b.second.lo := by simpa [taylorCheck] using h
  have hr : (0:ℝ) < 2*(b.value.lo:ℝ)+2*(b.first.lo:ℝ)+(b.second.lo:ℝ) := by exact_mod_cast hz
  apply JetBounds.JetEnclosure.value_pos_of_taylor hj (containsOn_toReal_iff.mpr hb)
  change 0 < (b.value.lo:ℝ)/(scale p:ℝ)+(b.first.lo:ℝ)/(scale p:ℝ)+(b.second.lo:ℝ)/(scale p:ℝ)/2
  have hs := scale_cast_pos p
  apply (mul_pos_iff_of_pos_left hs).mp
  field_simp
  linarith

end DyadicJetEnclosure
end GeneralCK.Certificates
