import GeneralCK.Certificates.DyadicJet5Bounds
import GeneralCK.Certificates.Jet5ReciprocalLog

/-! Fixed-scale interval propagation for reciprocal and logarithmic order-five jets. -/

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval

def inv {p : ℕ} (b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let r1 := b.d0.recip
  let r2 := r1.mul r1
  let r3 := r2.mul r1
  let r4 := r3.mul r1
  let r5 := r4.mul r1
  let r6 := r5.mul r1
  let c2 := ofInt p 2
  let c6 := ofInt p 6
  let c8 := ofInt p 8
  let c10 := ofInt p 10
  let c20 := ofInt p 20
  let c24 := ofInt p 24
  let c36 := ofInt p 36
  let c60 := ofInt p 60
  let c90 := ofInt p 90
  let c120 := ofInt p 120
  let c240 := ofInt p 240
  ⟨r1,
   b.d1.neg.mul r2,
   (c2.mul (b.d1.mul b.d1)).mul r3 |>.sub (b.d2.mul r2),
   ((c6.mul ((b.d1.mul b.d1).mul b.d1)).neg.mul r4).add
     ((c6.mul (b.d1.mul b.d2)).mul r3) |>.sub (b.d3.mul r2),
   (((c24.mul (((b.d1.mul b.d1).mul b.d1).mul b.d1)).mul r5).sub
     ((c36.mul ((b.d1.mul b.d1).mul b.d2)).mul r4)).add
     ((c6.mul (b.d2.mul b.d2)).mul r3) |>.add
     ((c8.mul (b.d1.mul b.d3)).mul r3) |>.sub (b.d4.mul r2),
   ((((((c120.mul ((((b.d1.mul b.d1).mul b.d1).mul b.d1).mul b.d1)).neg.mul r6).add
     ((c240.mul (((b.d1.mul b.d1).mul b.d1).mul b.d2)).mul r5)).sub
     ((c90.mul ((b.d1.mul b.d2).mul b.d2)).mul r4)).sub
     ((c60.mul ((b.d1.mul b.d1).mul b.d3)).mul r4)).add
     ((c20.mul (b.d2.mul b.d3)).mul r3)).add
     ((c10.mul (b.d1.mul b.d4)).mul r3) |>.sub (b.d5.mul r2)⟩

theorem Contains.inv {p : ℕ} {b : DyadicJet5Enclosure p} {a : Jet5} {t : ℝ}
    (hb : b.Contains a t) (hp : 0 < b.d0.lo) : b.inv.Contains a.inv t := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  have r1 := recip_sound hp h0
  have r2 := mul_sound r1 r1
  have r3 := mul_sound r2 r1
  have r4 := mul_sound r3 r1
  have r5 := mul_sound r4 r1
  have r6 := mul_sound r5 r1
  have c2 := ofInt_sound p 2
  have c6 := ofInt_sound p 6
  have c8 := ofInt_sound p 8
  have c10 := ofInt_sound p 10
  have c20 := ofInt_sound p 20
  have c24 := ofInt_sound p 24
  have c36 := ofInt_sound p 36
  have c60 := ofInt_sound p 60
  have c90 := ofInt_sound p 90
  have c120 := ofInt_sound p 120
  have c240 := ofInt_sound p 240
  dsimp only [Contains, DyadicJet5Enclosure.inv, Jet5.inv]
  refine ⟨r1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv, pow_two] using mul_sound (neg_sound h1) r2
  · convert sub_sound (mul_sound (mul_sound c2 (mul_sound h1 h1)) r3)
      (mul_sound h2 r2) using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound
      (mul_sound (neg_sound (mul_sound c6 (mul_sound (mul_sound h1 h1) h1))) r4)
      (mul_sound (mul_sound c6 (mul_sound h1 h2)) r3)) (mul_sound h3 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (mul_sound (mul_sound c24 (mul_sound (mul_sound (mul_sound h1 h1) h1) h1)) r5)
        (mul_sound (mul_sound c36 (mul_sound (mul_sound h1 h1) h2)) r4))
      (mul_sound (mul_sound c6 (mul_sound h2 h2)) r3))
      (mul_sound (mul_sound c8 (mul_sound h1 h3)) r3)) (mul_sound h4 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (sub_sound (add_sound
        (mul_sound (neg_sound (mul_sound c120
          (mul_sound (mul_sound (mul_sound (mul_sound h1 h1) h1) h1) h1))) r6)
        (mul_sound (mul_sound c240 (mul_sound (mul_sound (mul_sound h1 h1) h1) h2)) r5))
        (mul_sound (mul_sound c90 (mul_sound (mul_sound h1 h2) h2)) r4))
        (mul_sound (mul_sound c60 (mul_sound (mul_sound h1 h1) h3)) r4))
      (mul_sound (mul_sound c20 (mul_sound h2 h3)) r3))
      (mul_sound (mul_sound c10 (mul_sound h1 h4)) r3)) (mul_sound h5 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring

/-- Logarithm propagation with a separately checked enclosure for the value. -/
def log {p : ℕ} (b : DyadicJet5Enclosure p) (l : DyadicInterval p) :
    DyadicJet5Enclosure p :=
  let r := b.inv
  let c2 := ofInt p 2
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c6 := ofInt p 6
  ⟨l, b.d1.mul r.d0,
   (b.d2.mul r.d0).add (b.d1.mul r.d1),
   ((b.d3.mul r.d0).add ((c2.mul b.d2).mul r.d1)).add (b.d1.mul r.d2),
   (((b.d4.mul r.d0).add ((c3.mul b.d3).mul r.d1)).add
     ((c3.mul b.d2).mul r.d2)).add (b.d1.mul r.d3),
   ((((b.d5.mul r.d0).add ((c4.mul b.d4).mul r.d1)).add
     ((c6.mul b.d3).mul r.d2)).add ((c4.mul b.d2).mul r.d3)).add
     (b.d1.mul r.d4)⟩

theorem Contains.log {p : ℕ} {b : DyadicJet5Enclosure p} {l : DyadicInterval p}
    {a : Jet5} {t : ℝ} (hb : b.Contains a t) (hp : 0 < b.d0.lo)
    (hl : l.Contains (Real.log (a.d0 t))) : (b.log l).Contains a.log t := by
  have hr := hb.inv hp
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  rcases hr with ⟨r0,r1,r2,r3,r4,r5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c6 := ofInt_sound p 6
  dsimp only [Contains, DyadicJet5Enclosure.log, Jet5.log]
  exact ⟨hl, mul_sound h1 r0,
    add_sound (mul_sound h2 r0) (mul_sound h1 r1),
    add_sound (add_sound (mul_sound h3 r0) (mul_sound (mul_sound c2 h2) r1))
      (mul_sound h1 r2),
    add_sound (add_sound (add_sound (mul_sound h4 r0) (mul_sound (mul_sound c3 h3) r1))
      (mul_sound (mul_sound c3 h2) r2)) (mul_sound h1 r3),
    add_sound (add_sound (add_sound (add_sound (mul_sound h5 r0)
      (mul_sound (mul_sound c4 h4) r1)) (mul_sound (mul_sound c6 h3) r2))
      (mul_sound (mul_sound c4 h2) r3)) (mul_sound h1 r4)⟩

end DyadicJet5Enclosure
end GeneralCK.Certificates
