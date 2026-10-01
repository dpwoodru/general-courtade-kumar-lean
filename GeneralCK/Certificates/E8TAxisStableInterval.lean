import GeneralCK.Certificates.E8TAxisStableJet5
import GeneralCK.Certificates.E8TAxisReparamInterval
import GeneralCK.Certificates.DyadicLogBounds

/-! The stable `xy_jets5` interval graph.  Only primitive exp/log enclosures
and positive denominator checks are supplied by a numerical replay. -/

namespace GeneralCK.Certificates.E8TAxisStableInterval

open DyadicInterval E8TAxisStableJet5 E8TAxisReparamInterval

def constant {p : ℕ} (v : DyadicInterval p) : DyadicJet5Enclosure p :=
  ⟨v, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩

theorem constant_sound {p : ℕ} {v : DyadicInterval p} {r a : ℝ}
    (hv : v.Contains r) : (constant v).Contains (Jet5.const r) a := by
  have hz : (ofInt p 0).Contains (0 : ℝ) := by simpa using ofInt_sound p 0
  exact ⟨hv, hz, hz, hz, hz, hz⟩

def negative {p : ℕ} (v : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨v.d0.neg,v.d1.neg,v.d2.neg,v.d3.neg,v.d4.neg,v.d5.neg⟩

theorem negative_sound {p : ℕ} {v : DyadicJet5Enclosure p} {j : Jet5} {a : ℝ}
    (hv : v.Contains j a) : (negative v).Contains j.neg a :=
  ⟨neg_sound hv.1, neg_sound hv.2.1, neg_sound hv.2.2.1,
    neg_sound hv.2.2.2.1, neg_sound hv.2.2.2.2.1, neg_sound hv.2.2.2.2.2⟩

structure Inputs (p : ℕ) where
  alpha : DyadicInterval p
  expNegTwo : DyadicInterval p
  logOnePlusExp : DyadicInterval p
  logTwo : DyadicInterval p

def zBox {p : ℕ} (i : Inputs p) : DyadicJet5Enclosure p :=
  let e := i.expNegTwo
  ⟨e, e.mul (ofInt p (-2)), e.mul (ofInt p 4), e.mul (ofInt p (-8)),
    e.mul (ofInt p 16), e.mul (ofInt p (-32))⟩

theorem zBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (he : i.expNegTwo.Contains (Real.exp (-2 * a))) :
    (zBox i).Contains zJet a := by
  dsimp only [zBox, zJet, Jet5.expAffine, DyadicJet5Enclosure.Contains]
  simp only [zero_add]
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using mul_sound he (ofInt_sound p (-2))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 4)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-8))
  · norm_num at *
    exact mul_sound he (ofInt_sound p 16)
  · norm_num at *
    simpa using mul_sound he (ofInt_sound p (-32))

def onePlusZBox {p : ℕ} (i : Inputs p) := (DyadicJet5Enclosure.const p 1).add (zBox i)
def rBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 1).add (negative (zBox i))).mul (onePlusZBox i).inv
def qBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 4).mul (zBox i)).mul
    ((onePlusZBox i).mul (onePlusZBox i)).inv
def l1Box {p : ℕ} (i : Inputs p) := (onePlusZBox i).log i.logOnePlusExp
def ellBox {p : ℕ} (i : Inputs p) := (DyadicJet5Enclosure.variableJet i.alpha).add (l1Box i)
def hBox {p : ℕ} (i : Inputs p) :=
  (l1Box i).add ((((DyadicJet5Enclosure.const p 2).mul
    (DyadicJet5Enclosure.variableJet i.alpha)).mul (zBox i)).mul (onePlusZBox i).inv)
def xBox {p : ℕ} (i : Inputs p) :=
  ((constant i.logTwo).mul (rBox i)).mul
    ((DyadicJet5Enclosure.const p 2).mul (hBox i)).inv
def yBox {p : ℕ} (i : Inputs p) :=
  ((DyadicJet5Enclosure.const p 2).mul (constant i.logTwo).inv).mul
    ((DyadicJet5Enclosure.variableJet i.alpha).add
      (((rBox i).mul (hBox i)).mul ((qBox i).mul (ellBox i)).inv))

/-- Every reciprocal in the evaluated graph has a checked positive denominator. -/
def DenominatorsPositive {p : ℕ} (i : Inputs p) : Prop :=
  0 < (onePlusZBox i).d0.lo ∧
  0 < ((onePlusZBox i).mul (onePlusZBox i)).d0.lo ∧
  0 < ((DyadicJet5Enclosure.const p 2).mul (hBox i)).d0.lo ∧
  0 < ((qBox i).mul (ellBox i)).d0.lo ∧ 0 < i.logTwo.lo

theorem xyBox_sound {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i) :
    (xBox i).Contains xJet a ∧ (yBox i).Contains yJet a := by
  have a0 := DyadicJet5Enclosure.contains_variable ha
  have c1 : (DyadicJet5Enclosure.const p 1).Contains (Jet5.const 1) a := by
    simpa using DyadicJet5Enclosure.contains_const p 1 a
  have c2 : (DyadicJet5Enclosure.const p 2).Contains (Jet5.const 2) a := by
    simpa using DyadicJet5Enclosure.contains_const p 2 a
  have c4 : (DyadicJet5Enclosure.const p 4).Contains (Jet5.const 4) a := by
    simpa using DyadicJet5Enclosure.contains_const p 4 a
  have hz := zBox_sound he
  have ho : (onePlusZBox i).Contains onePlusZJet a := c1.add hz
  have hr : (rBox i).Contains rJet a :=
    (c1.add (negative_sound hz)).mul (ho.inv hp.1)
  have hq : (qBox i).Contains qJet a :=
    (c4.mul hz).mul ((ho.mul ho).inv hp.2.1)
  have hlog : (l1Box i).Contains l1Jet a := by
    apply ho.log hp.1
    simpa [onePlusZJet, zJet, Jet5.add, Jet5.const, Jet5.expAffine] using hl
  have hell : (ellBox i).Contains ellJet a := a0.add hlog
  have hh : (hBox i).Contains hJet a :=
    hlog.add (((c2.mul a0).mul hz).mul (ho.inv hp.1))
  have htwo : (constant i.logTwo).Contains log2Jet a := constant_sound hL
  exact ⟨(htwo.mul hr).mul ((c2.mul hh).inv hp.2.2.1),
    (c2.mul (htwo.inv hp.2.2.2.2)).mul
      (a0.add ((hr.mul hh).mul ((hq.mul hell).inv hp.2.2.2.1)))⟩

/-- Stable interval evaluation encloses the concrete inverse derivatives for
every positive parameter in the supplied alpha box. -/
theorem stable_contains_canonical {p : ℕ} {i : Inputs p} {a : ℝ}
    (ha : i.alpha.Contains a) (hapos : 0 < a)
    (he : i.expNegTwo.Contains (Real.exp (-2 * a)))
    (hl : i.logOnePlusExp.Contains (Real.log (1 + Real.exp (-2 * a))))
    (hL : i.logTwo.Contains (Real.log 2)) (hp : DenominatorsPositive i)
    (hyp : 0 < (yBox i).d1.lo) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hxy := xyBox_sound ha he hl hL hp
  have result := eval_contains_canonical isOpen_Ioi xJet_soundOn yJet_soundOn
    (fun b hb => by simpa using Y_mem_e8SlopeRange hb)
    (fun b hb => by simpa using (E8TAxisStableScalar.e8Q_Y hb).symm)
    hapos hxy.1 hxy.2 hyp
  simpa only [yJet_d0] using result

structure FastLogBoxWitness where
  lowerExponent : ℕ
  lowerTerms : ℕ
  upperExponent : ℕ
  upperTerms : ℕ

def logBoxCheck {p : ℕ} (input out : DyadicInterval p) (w : FastLogBoxWitness) : Bool :=
  decide (0 < input.lo) &&
    DyadicFastLog.check (scale p) input.lo w.lowerExponent w.lowerTerms out.neg &&
    DyadicFastLog.check (scale p) input.hi w.upperExponent w.upperTerms out.neg

theorem logBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : FastLogBoxWitness}
    (hc : logBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.log x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hbot := Bool.and_eq_true_iff.mp htop.1
  have hlo : 0 < input.lo := of_decide_eq_true hbot.1
  have hl0 := DyadicFastLog.check_sound hbot.2
  have hu0 := DyadicFastLog.check_sound htop.2
  have hl : out.Contains (-Real.log ((scale p : ℝ) / input.lo)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hl0
  have hu : out.Contains (-Real.log ((scale p : ℝ) / input.hi)) := by
    simpa only [DyadicInterval.neg, neg_neg] using neg_sound hu0
  have hs := scale_cast_pos p
  have hlReal : (0 : ℝ) < input.lo := by exact_mod_cast hlo
  have hiReal : (0 : ℝ) < input.hi := lt_of_lt_of_le hlReal (hx.1.trans hx.2)
  have hscale : (0 : ℝ) < scale p := scale_cast_pos p
  have hlEq : -Real.log ((scale p : ℝ) / input.lo) =
      Real.log ((input.lo : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hlReal.ne', Real.log_div hlReal.ne' hscale.ne']
    ring
  have huEq : -Real.log ((scale p : ℝ) / input.hi) =
      Real.log ((input.hi : ℝ) / scale p) := by
    rw [Real.log_div hscale.ne' hiReal.ne', Real.log_div hiReal.ne' hscale.ne']
    ring
  rw [hlEq] at hl
  rw [huEq] at hu
  have hlow : (input.lo : ℝ) / scale p ≤ x := (div_le_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.1)
  have hupp : x ≤ (input.hi : ℝ) / scale p := (le_div_iff₀ hs).mpr (by
    simpa only [mul_comm] using hx.2)
  have hxpos : 0 < x := (div_pos hlReal hs).trans_le hlow
  exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hlReal hs) hlow) hs.le),
    (mul_le_mul_of_nonneg_left (Real.log_le_log hxpos hupp) hs.le).trans hu.2⟩

structure ExpWitness (p : ℕ) where
  lowerNum : ℤ
  lowerDen : ℤ
  upperNum : ℤ
  upperDen : ℤ
  lowerExponent : ℕ
  lowerTerms : ℕ
  upperExponent : ℕ
  upperTerms : ℕ
  logLower : DyadicInterval p
  logUpper : DyadicInterval p

def expBoxCheck {p : ℕ} (input out : DyadicInterval p) (w : ExpWitness p) : Bool :=
  DyadicExp.check input w.lowerNum w.lowerDen w.upperNum w.upperDen
    w.lowerExponent w.lowerTerms w.upperExponent w.upperTerms w.logLower w.logUpper &&
  (DyadicExp.enclosure p w.lowerNum w.lowerDen w.upperNum w.upperDen).subsetCheck out

theorem expBoxCheck_sound {p : ℕ} {input out : DyadicInterval p} {w : ExpWitness p}
    (hc : expBoxCheck input out w = true) {x : ℝ} (hx : input.Contains x) :
    out.Contains (Real.exp x) := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact subsetCheck_sound hh.2 (DyadicExp.check_sound hh.1 hx)

/-- The primitive assumptions are fully executable checks.  A production
record supplies these witnesses and the five positive denominator checks. -/
theorem checked_stable_contains_canonical {p : ℕ} {i : Inputs p}
    {we : ExpWitness p} {wl wL : FastLogBoxWitness}
    (he : expBoxCheck ((ofInt p (-2)).mul i.alpha) i.expNegTwo we = true)
    (hl : logBoxCheck ((ofInt p 1).add i.expNegTwo) i.logOnePlusExp wl = true)
    (hL : logBoxCheck (ofInt p 2) i.logTwo wL = true)
    (hp : DenominatorsPositive i) (hyp : 0 < (yBox i).d1.lo)
    {a : ℝ} (ha : i.alpha.Contains a) (hapos : 0 < a) :
    (eval (xBox i) (yBox i)).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  have hz : i.expNegTwo.Contains (Real.exp (-2 * a)) := by
    simpa using expBoxCheck_sound he (mul_sound (ofInt_sound p (-2)) ha)
  have hc1 : (ofInt p 1).Contains (1 : ℝ) := by simpa using ofInt_sound p 1
  have hc2 : (ofInt p 2).Contains (2 : ℝ) := by simpa using ofInt_sound p 2
  exact stable_contains_canonical ha hapos hz
    (logBoxCheck_sound hl (add_sound hc1 hz))
    (logBoxCheck_sound hL hc2) hp hyp

#print axioms stable_contains_canonical
#print axioms checked_stable_contains_canonical

end GeneralCK.Certificates.E8TAxisStableInterval
