import GeneralCK.Certificates.BivariateJet2
import GeneralCK.Certificates.BivariateJetBounds
import GeneralCK.Certificates.DyadicLogBounds
import GeneralCK.Certificates.DyadicContactBounds

namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains

theorem add {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := add_sound hx hy

theorem neg {p : ℕ} {a : DyadicInterval p} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := neg_sound hx

theorem mul {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := mul_sound hx hy

end DyadicInterval.Contains

/-- Coordinate coefficients are enclosed before contracting with a segment direction. -/
structure DyadicBivariateJetEnclosure (p : ℕ) where
  value : DyadicInterval p
  firstA : DyadicInterval p
  firstZ : DyadicInterval p
  secondAA : DyadicInterval p
  secondAZ : DyadicInterval p
  secondZZ : DyadicInterval p

namespace DyadicBivariateJetEnclosure
variable {p : ℕ}


def Contains (b : DyadicBivariateJetEnclosure p) (j : BivariateJet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.firstA.Contains (j.firstA t) ∧
  b.firstZ.Contains (j.firstZ t) ∧ b.secondAA.Contains (j.secondAA t) ∧
  b.secondAZ.Contains (j.secondAZ t) ∧ b.secondZZ.Contains (j.secondZZ t)

def ContainsOn (b : DyadicBivariateJetEnclosure p) (j : BivariateJet2) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, b.Contains j t

noncomputable def toReal (b : DyadicBivariateJetEnclosure p) : BivariateJetEnclosure :=
  ⟨b.value.toReal,b.firstA.toReal,b.firstZ.toReal,b.secondAA.toReal,b.secondAZ.toReal,b.secondZZ.toReal⟩

theorem contains_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ} :
    b.toReal.Contains j t ↔ b.Contains j t := by
  simp only [toReal,BivariateJetEnclosure.Contains,Contains,DyadicInterval.contains_toReal_iff]

theorem containsOn_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {s : Set ℝ} :
    b.toReal.ContainsOn j s ↔ b.ContainsOn j s := by
  simp only [BivariateJetEnclosure.ContainsOn,ContainsOn,contains_toReal_iff]

def coordinateA (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  ⟨value,ofInt p 1,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0⟩

def coordinateZ (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  ⟨value,ofInt p 0,ofInt p 1,ofInt p 0,ofInt p 0,ofInt p 0⟩

theorem contains_coordinateA {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateA value).Contains (BivariateJet2.coordinateA f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h1,h0,h0,h0,h0⟩

theorem contains_coordinateZ {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateZ value).Contains (BivariateJet2.coordinateZ f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h0,h1,h0,h0,h0⟩

def const (p : ℕ) (c : ℤ) : DyadicBivariateJetEnclosure p :=
  ⟨ofInt p c,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0⟩

def add (b c : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.add c.value,b.firstA.add c.firstA,b.firstZ.add c.firstZ,
    b.secondAA.add c.secondAA,b.secondAZ.add c.secondAZ,b.secondZZ.add c.secondZZ⟩

def neg (b : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.neg,b.firstA.neg,b.firstZ.neg,b.secondAA.neg,b.secondAZ.neg,b.secondZZ.neg⟩

def mul (b c : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.mul c.value,
    (b.firstA.mul c.value).add (b.value.mul c.firstA),
    (b.firstZ.mul c.value).add (b.value.mul c.firstZ),
    ((b.secondAA.mul c.value).add (((ofInt p 2).mul b.firstA).mul c.firstA)).add
      (b.value.mul c.secondAA),
    (((b.secondAZ.mul c.value).add (b.firstA.mul c.firstZ)).add (b.firstZ.mul c.firstA)).add
      (b.value.mul c.secondAZ),
    ((b.secondZZ.mul c.value).add (((ofInt p 2).mul b.firstZ).mul c.firstZ)).add
      (b.value.mul c.secondZZ)⟩

/-- The outer Jet2 enclosure is evaluated at the actual inner value. -/
def outerCompose (outer : DyadicJetEnclosure p) (b : DyadicBivariateJetEnclosure p) :
    DyadicBivariateJetEnclosure p :=
  ⟨outer.value,outer.first.mul b.firstA,outer.first.mul b.firstZ,
    ((outer.second.mul b.firstA).mul b.firstA).add (outer.first.mul b.secondAA),
    ((outer.second.mul b.firstA).mul b.firstZ).add (outer.first.mul b.secondAZ),
    ((outer.second.mul b.firstZ).mul b.firstZ).add (outer.first.mul b.secondZZ)⟩

theorem contains_const (p : ℕ) (c : ℤ) (t : ℝ) :
    (const p c).Contains (BivariateJet2.const c) t := by
  exact ⟨ofInt_sound p c,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,
    by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0⟩

theorem Contains.add {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.1.add hk.2.2.1,
    hj.2.2.2.1.add hk.2.2.2.1,hj.2.2.2.2.1.add hk.2.2.2.2.1,
    hj.2.2.2.2.2.add hk.2.2.2.2.2⟩

theorem Contains.neg {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨hj.1.neg,hj.2.1.neg,hj.2.2.1.neg,hj.2.2.2.1.neg,hj.2.2.2.2.1.neg,hj.2.2.2.2.2.neg⟩

theorem Contains.mul {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    (hj.2.2.1.mul hk.1).add (hj.1.mul hk.2.2.1),
    ((hj.2.2.2.1.mul hk.1).add ((htwo.mul hj.2.1).mul hk.2.1)).add (hj.1.mul hk.2.2.2.1),
    (((hj.2.2.2.2.1.mul hk.1).add (hj.2.1.mul hk.2.2.1)).add
      (hj.2.2.1.mul hk.2.1)).add (hj.1.mul hk.2.2.2.2.1),
    ((hj.2.2.2.2.2.mul hk.1).add ((htwo.mul hj.2.2.1).mul hk.2.2.1)).add
      (hj.1.mul hk.2.2.2.2.2)⟩

theorem Contains.outerCompose {outer : DyadicJetEnclosure p} {b : DyadicBivariateJetEnclosure p}
    {f : Jet2} {j : BivariateJet2} {t : ℝ} (hf : outer.Contains f (j.value t))
    (hj : b.Contains j t) : (outerCompose outer b).Contains (BivariateJet2.outerCompose f j) t := by
  exact ⟨hf.1,hf.2.1.mul hj.2.1,hf.2.1.mul hj.2.2.1,
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.1).mul hj.2.1).add (hf.2.1.mul hj.2.2.2.1),
    ((hf.2.2.mul hj.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.1),
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.2)⟩

def subsetCheck (b out : DyadicBivariateJetEnclosure p) : Bool :=
  b.value.subsetCheck out.value && b.firstA.subsetCheck out.firstA &&
  b.firstZ.subsetCheck out.firstZ && b.secondAA.subsetCheck out.secondAA &&
  b.secondAZ.subsetCheck out.secondAZ && b.secondZZ.subsetCheck out.secondZZ

theorem subsetCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : b.subsetCheck out=true) (hj : b.Contains j t) : out.Contains j t := by
  simp only [subsetCheck,Bool.and_eq_true_iff] at h
  exact ⟨DyadicInterval.subsetCheck_sound h.1.1.1.1.1 hj.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.1.2 hj.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.2 hj.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.2 hj.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.2 hj.2.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.2 hj.2.2.2.2.2⟩

def inv (b : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  outerCompose (DyadicJetEnclosure.variableJet b.value).inv b

theorem Contains.inv {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hpos : 0<b.value.lo) :
    b.inv.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t :=
  Contains.outerCompose (DyadicJetEnclosure.Contains.inv (DyadicJetEnclosure.contains_variable hj.1) hpos) hj

def invCheck (b out : DyadicBivariateJetEnclosure p) : Bool :=
  b.value.positiveCheck && b.inv.subsetCheck out

theorem invCheck_positive {b out : DyadicBivariateJetEnclosure p} (h : invCheck b out=true) :
    0<b.value.lo := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem invCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : invCheck b out=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (hj.inv (of_decide_eq_true hh.1))

def log (b : DyadicBivariateJetEnclosure p) (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  outerCompose (DyadicLog.jetLog (DyadicJetEnclosure.variableJet b.value) value) b

theorem log_sound {b : DyadicBivariateJetEnclosure p} {value : DyadicInterval p}
    {wl wu : DyadicLog.Witness} {j : BivariateJet2} {t : ℝ}
    (h : DyadicLog.check b.value value wl wu=true) (hj : b.Contains j t) :
    (b.log value).Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t :=
  Contains.outerCompose (DyadicLog.jetLog_sound (DyadicJetEnclosure.contains_variable hj.1) h) hj

def logCheck (b out : DyadicBivariateJetEnclosure p) (wl wu : DyadicLog.Witness) : Bool :=
  DyadicLog.check b.value out.value wl wu && (b.log out.value).subsetCheck out

theorem logCheck_positive {b out : DyadicBivariateJetEnclosure p} {wl wu : DyadicLog.Witness}
    (h : logCheck b out wl wu=true) : 0<b.value.lo :=
  DyadicLog.checkEndpoint_pos (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem logCheck_sound {b out : DyadicBivariateJetEnclosure p} {wl wu : DyadicLog.Witness}
    {j : BivariateJet2} {t : ℝ} (h : logCheck b out wl wu=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (log_sound hh.1 hj)

def contactCheck (b out : DyadicBivariateJetEnclosure p) (c B : DyadicInterval p)
    (outer : DyadicJetEnclosure p) (w : DyadicContact.BracketWitness p)
    (bw : DyadicEntropy.BWitness p) : Bool :=
  DyadicContact.jetCheck b.value c B outer w bw && (outerCompose outer b).subsetCheck out

theorem contactCheck_positive {b out : DyadicBivariateJetEnclosure p} {c B : DyadicInterval p}
    {outer : DyadicJetEnclosure p} {w : DyadicContact.BracketWitness p} {bw : DyadicEntropy.BWitness p}
    (h : contactCheck b out c B outer w bw=true) : 0<b.value.lo := by
  have hj := (Bool.and_eq_true_iff.mp h).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hj).1).1).1
  exact DyadicContact.bracketCheck_positive hb

theorem contactCheck_sound {b out : DyadicBivariateJetEnclosure p} {c B : DyadicInterval p}
    {outer : DyadicJetEnclosure p} {w : DyadicContact.BracketWitness p} {bw : DyadicEntropy.BWitness p}
    {j : BivariateJet2} {t : ℝ} (h : contactCheck b out c B outer w bw=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose reflectionContactJet j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (Contains.outerCompose (DyadicContact.jetCheck_sound hh.1 hj.1) hj)

end DyadicBivariateJetEnclosure
end GeneralCK.Certificates
