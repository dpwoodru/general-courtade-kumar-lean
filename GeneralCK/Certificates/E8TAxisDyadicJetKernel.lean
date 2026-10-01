import GeneralCK.Certificates.DyadicJet5ReciprocalLog

/-!
# Missing dyadic product rule for the E8 order-five replay

The retained C++ `BJ5` evaluator multiplies factorial-normalized jets.  Lean's
`Jet5` uses raw derivatives, so the corresponding enclosure uses the binomial
coefficients in the ordinary Leibniz rule.
-/

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval

def mul {p : ℕ} (a b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let c2 := ofInt p 2
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c5 := ofInt p 5
  let c6 := ofInt p 6
  let c10 := ofInt p 10
  ⟨a.d0.mul b.d0,
   (a.d1.mul b.d0).add (a.d0.mul b.d1),
   ((a.d2.mul b.d0).add ((c2.mul a.d1).mul b.d1)).add (a.d0.mul b.d2),
   (((a.d3.mul b.d0).add ((c3.mul a.d2).mul b.d1)).add
      ((c3.mul a.d1).mul b.d2)).add (a.d0.mul b.d3),
   ((((a.d4.mul b.d0).add ((c4.mul a.d3).mul b.d1)).add
      ((c6.mul a.d2).mul b.d2)).add ((c4.mul a.d1).mul b.d3)).add
      (a.d0.mul b.d4),
   (((((a.d5.mul b.d0).add ((c5.mul a.d4).mul b.d1)).add
      ((c10.mul a.d3).mul b.d2)).add ((c10.mul a.d2).mul b.d3)).add
      ((c5.mul a.d1).mul b.d4)).add (a.d0.mul b.d5)⟩

theorem Contains.mul {p : ℕ} {a b : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (ha : a.Contains j t) (hb : b.Contains k t) :
    (a.mul b).Contains (j.mul k) t := by
  rcases ha with ⟨a0,a1,a2,a3,a4,a5⟩
  rcases hb with ⟨b0,b1,b2,b3,b4,b5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c5 := ofInt_sound p 5
  have c6 := ofInt_sound p 6
  have c10 := ofInt_sound p 10
  dsimp only [Contains, DyadicJet5Enclosure.mul, Jet5.mul]
  exact ⟨mul_sound a0 b0,
    add_sound (mul_sound a1 b0) (mul_sound a0 b1),
    add_sound (add_sound (mul_sound a2 b0) (mul_sound (mul_sound c2 a1) b1))
      (mul_sound a0 b2),
    add_sound (add_sound (add_sound (mul_sound a3 b0) (mul_sound (mul_sound c3 a2) b1))
      (mul_sound (mul_sound c3 a1) b2)) (mul_sound a0 b3),
    add_sound (add_sound (add_sound (add_sound (mul_sound a4 b0)
      (mul_sound (mul_sound c4 a3) b1)) (mul_sound (mul_sound c6 a2) b2))
      (mul_sound (mul_sound c4 a1) b3)) (mul_sound a0 b4),
    add_sound (add_sound (add_sound (add_sound (add_sound (mul_sound a5 b0)
      (mul_sound (mul_sound c5 a4) b1)) (mul_sound (mul_sound c10 a3) b2))
      (mul_sound (mul_sound c10 a2) b3)) (mul_sound (mul_sound c5 a1) b4))
      (mul_sound a0 b5)⟩

#print axioms Contains.mul

end DyadicJet5Enclosure
end GeneralCK.Certificates
