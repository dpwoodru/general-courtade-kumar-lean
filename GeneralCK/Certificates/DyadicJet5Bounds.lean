import GeneralCK.Certificates.Jet5
import GeneralCK.Certificates.DyadicExpBounds

/-! Fixed-scale enclosures for raw order-five univariate jets. -/

namespace GeneralCK.Certificates

structure DyadicJet5Enclosure (p : ℕ) where
  d0 : DyadicInterval p
  d1 : DyadicInterval p
  d2 : DyadicInterval p
  d3 : DyadicInterval p
  d4 : DyadicInterval p
  d5 : DyadicInterval p
  deriving DecidableEq, Repr

namespace DyadicJet5Enclosure

open DyadicInterval

def Contains {p : ℕ} (b : DyadicJet5Enclosure p) (j : Jet5) (t : ℝ) : Prop :=
  b.d0.Contains (j.d0 t) ∧ b.d1.Contains (j.d1 t) ∧
  b.d2.Contains (j.d2 t) ∧ b.d3.Contains (j.d3 t) ∧
  b.d4.Contains (j.d4 t) ∧ b.d5.Contains (j.d5 t)

def const (p : ℕ) (z : ℤ) : DyadicJet5Enclosure p :=
  ⟨ofInt p z, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩

def variableJet {p : ℕ} (i : DyadicInterval p) : DyadicJet5Enclosure p :=
  ⟨i, ofInt p 1, ofInt p 0, ofInt p 0, ofInt p 0, ofInt p 0⟩

def add {p : ℕ} (b c : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨b.d0.add c.d0, b.d1.add c.d1, b.d2.add c.d2,
    b.d3.add c.d3, b.d4.add c.d4, b.d5.add c.d5⟩

def scale {p : ℕ} (z : ℤ) (b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let c := ofInt p z
  ⟨c.mul b.d0, c.mul b.d1, c.mul b.d2, c.mul b.d3, c.mul b.d4, c.mul b.d5⟩

/-- Faà di Bruno interval propagation for `exp`, using a separately checked
value enclosure `e` for `exp (j.d0 t)`. -/
def exp {p : ℕ} (b : DyadicJet5Enclosure p) (e : DyadicInterval p) :
    DyadicJet5Enclosure p :=
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c5 := ofInt p 5
  let c6 := ofInt p 6
  let c10 := ofInt p 10
  let c15 := ofInt p 15
  let q2 := (b.d1.mul b.d1).add b.d2
  let q3 := ((b.d1.mul b.d1).mul b.d1).add
    ((c3.mul b.d1).mul b.d2) |>.add b.d3
  let q4a := (((b.d1.mul b.d1).mul b.d1).mul b.d1).add
    ((c6.mul (b.d1.mul b.d1)).mul b.d2)
  let q4b := q4a.add ((c3.mul b.d2).mul b.d2)
  let q4c := q4b.add ((c4.mul b.d1).mul b.d3)
  let q4 := q4c.add b.d4
  let q5a := ((((b.d1.mul b.d1).mul b.d1).mul b.d1).mul b.d1).add
    (c10.mul (((b.d1.mul b.d1).mul b.d1).mul b.d2))
  let q5b := q5a.add (c15.mul ((b.d1.mul b.d2).mul b.d2))
  let q5c := q5b.add (c10.mul ((b.d1.mul b.d1).mul b.d3))
  let q5d := q5c.add (c10.mul (b.d2.mul b.d3))
  let q5e := q5d.add (c5.mul (b.d1.mul b.d4))
  let q5 := q5e.add b.d5
  ⟨e, e.mul b.d1, e.mul q2, e.mul q3, e.mul q4, e.mul q5⟩

theorem contains_const (p : ℕ) (z : ℤ) (t : ℝ) :
    (const p z).Contains (Jet5.const z) t := by
  exact ⟨ofInt_sound p z, by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0⟩

theorem contains_variable {p : ℕ} {i : DyadicInterval p} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet5.variableJet t := by
  exact ⟨ht, by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 1,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0⟩

theorem Contains.add {p : ℕ} {b c : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (hb : b.Contains j t) (hc : c.Contains k t) :
    (b.add c).Contains (j.add k) t :=
  ⟨add_sound hb.1 hc.1, add_sound hb.2.1 hc.2.1,
    add_sound hb.2.2.1 hc.2.2.1, add_sound hb.2.2.2.1 hc.2.2.2.1,
    add_sound hb.2.2.2.2.1 hc.2.2.2.2.1, add_sound hb.2.2.2.2.2 hc.2.2.2.2.2⟩

theorem Contains.scale {p : ℕ} {b : DyadicJet5Enclosure p} {j : Jet5} {t : ℝ}
    (hb : b.Contains j t) (z : ℤ) :
    (b.scale z).Contains ((Jet5.const z).mul j) t := by
  have hz := ofInt_sound p z
  simp only [Contains, DyadicJet5Enclosure.scale, Jet5.mul, Jet5.const,
    zero_mul, mul_zero, zero_add]
  exact ⟨mul_sound hz hb.1, mul_sound hz hb.2.1, mul_sound hz hb.2.2.1,
    mul_sound hz hb.2.2.2.1, mul_sound hz hb.2.2.2.2.1,
    mul_sound hz hb.2.2.2.2.2⟩

theorem Contains.exp {p : ℕ} {b : DyadicJet5Enclosure p} {e : DyadicInterval p}
    {j : Jet5} {t : ℝ} (hb : b.Contains j t) (he : e.Contains (Real.exp (j.d0 t))) :
    (b.exp e).Contains j.exp t := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c5 := ofInt_sound p 5
  have c6 := ofInt_sound p 6
  have c10 := ofInt_sound p 10
  have c15 := ofInt_sound p 15
  dsimp only [Contains, DyadicJet5Enclosure.exp, Jet5.exp]
  refine ⟨he, mul_sound he h1, ?_, ?_, ?_, ?_⟩
  · simpa [DyadicJet5Enclosure.exp, Jet5.exp, pow_two] using
      mul_sound he (add_sound (mul_sound h1 h1) h2)
  · simpa [DyadicJet5Enclosure.exp, Jet5.exp, pow_succ] using mul_sound he
      (add_sound (add_sound (mul_sound (mul_sound h1 h1) h1)
        (mul_sound (mul_sound c3 h1) h2)) h3)
  · convert mul_sound he
      (add_sound (add_sound (add_sound (add_sound
        (mul_sound (mul_sound (mul_sound h1 h1) h1) h1)
        (mul_sound (mul_sound c6 (mul_sound h1 h1)) h2))
        (mul_sound (mul_sound c3 h2) h2))
        (mul_sound (mul_sound c4 h1) h3)) h4) using 1 <;> ring
  · convert mul_sound he
      (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound
        (mul_sound (mul_sound (mul_sound (mul_sound h1 h1) h1) h1) h1)
        (mul_sound c10 (mul_sound (mul_sound (mul_sound h1 h1) h1) h2)))
        (mul_sound c15 (mul_sound (mul_sound h1 h2) h2)))
        (mul_sound c10 (mul_sound (mul_sound h1 h1) h3)))
        (mul_sound c10 (mul_sound h2 h3)))
        (mul_sound c5 (mul_sound h1 h4))) h5) using 1 <;> ring

end DyadicJet5Enclosure
end GeneralCK.Certificates
