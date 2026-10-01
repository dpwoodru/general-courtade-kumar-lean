import GeneralCK.Certificates.DyadicLogBounds

namespace GeneralCK.Certificates.DyadicEntropy
open DyadicInterval

/-- Logarithm intervals and witnesses for the natural entropy formula. -/
structure Witness (p : ℕ) where
  logTwo : DyadicInterval p
  logPlus : DyadicInterval p
  logMinus : DyadicInterval p
  two : DyadicLog.Witness
  plusLo : DyadicLog.Witness
  plusHi : DyadicLog.Witness
  minusLo : DyadicLog.Witness
  minusHi : DyadicLog.Witness

def half (p : ℕ) : DyadicInterval p := (ofInt p 2).recip

theorem half_contains (p : ℕ) : (half p).Contains ((2:ℝ)⁻¹) := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact recip_sound (by dsimp [ofInt]; have := scale_pos p; positivity) htwo

def raw {p : ℕ} (c : DyadicInterval p) (w : Witness p) : DyadicInterval p :=
  w.logTwo.sub ((((ofInt p 1).add c).mul w.logPlus).add
    (((ofInt p 1).sub c).mul w.logMinus) |>.mul (half p))

/-- Every logarithm domain and its range-reduction certificate is checked. -/
def check {p : ℕ} (c out : DyadicInterval p) (w : Witness p) : Bool :=
  DyadicLog.check (ofInt p 2) w.logTwo w.two w.two &&
  DyadicLog.check ((ofInt p 1).add c) w.logPlus w.plusLo w.plusHi &&
  DyadicLog.check ((ofInt p 1).sub c) w.logMinus w.minusLo w.minusHi &&
  (raw c w).subsetCheck out

theorem check_sound {p : ℕ} {c out : DyadicInterval p} {w : Witness p}
    (hc : check c out w=true) {x : ℝ} (hx : c.Contains x) :
    out.Contains (Reflection.biasE x) := by
  have h0 := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hp := add_sound hone hx
  have hm := sub_sound hone hx
  have hl2 := DyadicLog.check_sound h2.1 htwo
  have hlp := DyadicLog.check_sound h2.2 hp
  have hlm := DyadicLog.check_sound h1.2 hm
  apply subsetCheck_sound h0.2
  simpa only [raw,Reflection.biasE,div_eq_mul_inv] using
    sub_sound hl2 (mul_sound (add_sound (mul_sound hp hlp) (mul_sound hm hlm)) (half_contains p))

/-- The two logarithms occurring in the positive contact denominator `B(c)`. -/
structure BWitness (p : ℕ) where
  logTwo : DyadicInterval p
  logGap : DyadicInterval p
  two : DyadicLog.Witness
  gapLo : DyadicLog.Witness
  gapHi : DyadicLog.Witness

def rawB {p : ℕ} (w : BWitness p) : DyadicInterval p :=
  w.logTwo.sub (w.logGap.mul (half p))

def checkB {p : ℕ} (c out : DyadicInterval p) (w : BWitness p) : Bool :=
  DyadicLog.check (ofInt p 2) w.logTwo w.two w.two &&
  DyadicLog.check ((ofInt p 1).sub (c.mul c)) w.logGap w.gapLo w.gapHi &&
  (rawB w).subsetCheck out

theorem checkB_sound {p : ℕ} {c out : DyadicInterval p} {w : BWitness p}
    (hc : checkB c out w=true) {x : ℝ} (hx : c.Contains x) :
    out.Contains (Reflection.biasB x) := by
  have h0 := Bool.and_eq_true_iff.mp hc
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hg := sub_sound hone (mul_sound hx hx)
  have hl2 := DyadicLog.check_sound h1.1 htwo
  have hlg := DyadicLog.check_sound h1.2 hg
  apply subsetCheck_sound h0.2
  simpa only [rawB,Reflection.biasB,div_eq_mul_inv] using
    sub_sound hl2 (mul_sound hlg (half_contains p))

end GeneralCK.Certificates.DyadicEntropy
