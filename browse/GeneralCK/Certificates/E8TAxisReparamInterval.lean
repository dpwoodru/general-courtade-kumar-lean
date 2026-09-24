import GeneralCK.Certificates.E8TAxisDyadicJetKernel
import GeneralCK.Certificates.E8TAxisReparamJet5

/-! Outward-rounded replay of the historical `qdata5` recurrence. -/

namespace GeneralCK.Certificates.E8TAxisReparamInterval

open DyadicInterval E8TAxisReparamJet5

def powI {p : ℕ} (x : DyadicInterval p) : ℕ → DyadicInterval p
  | 0 => ofInt p 1
  | n + 1 => (powI x n).mul x

theorem powI_sound {p : ℕ} {x : DyadicInterval p} {r : ℝ}
    (hx : x.Contains r) (n : ℕ) : (powI x n).Contains (r ^ n) := by
  induction n with
  | zero => simpa [powI] using ofInt_sound p 1
  | succ n ih => simpa [powI, pow_succ] using mul_sound ih hx

def eval {p : ℕ} (x y : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨x.d0,
   (x.d1.mul y.d1.recip),
   (((y.d1.mul x.d2).sub (y.d2.mul x.d1)).mul (powI y.d1.recip 3)),
   ((((((powI y.d1 2).mul x.d3).sub ((((ofInt p 3).mul y.d1).mul y.d2).mul x.d2)).sub ((y.d1.mul y.d3).mul x.d1)).add (((ofInt p 3).mul (powI y.d2 2)).mul x.d1)).mul (powI y.d1.recip 5)),
   (((((((((powI y.d1 3).mul x.d4).sub ((((ofInt p 6).mul (powI y.d1 2)).mul y.d2).mul x.d3)).sub ((((ofInt p 4).mul (powI y.d1 2)).mul y.d3).mul x.d2)).sub (((powI y.d1 2).mul y.d4).mul x.d1)).add ((((ofInt p 15).mul y.d1).mul (powI y.d2 2)).mul x.d2)).add (((((ofInt p 10).mul y.d1).mul y.d2).mul y.d3).mul x.d1)).sub (((ofInt p 15).mul (powI y.d2 3)).mul x.d1)).mul (powI y.d1.recip 7)),
   ((((((((((((((powI y.d1 4).mul x.d5).sub ((((ofInt p 10).mul (powI y.d1 3)).mul y.d2).mul x.d4)).sub ((((ofInt p 10).mul (powI y.d1 3)).mul y.d3).mul x.d3)).sub ((((ofInt p 5).mul (powI y.d1 3)).mul y.d4).mul x.d2)).sub (((powI y.d1 3).mul y.d5).mul x.d1)).add ((((ofInt p 45).mul (powI y.d1 2)).mul (powI y.d2 2)).mul x.d3)).add (((((ofInt p 60).mul (powI y.d1 2)).mul y.d2).mul y.d3).mul x.d2)).add (((((ofInt p 15).mul (powI y.d1 2)).mul y.d2).mul y.d4).mul x.d1)).add ((((ofInt p 10).mul (powI y.d1 2)).mul (powI y.d3 2)).mul x.d1)).sub ((((ofInt p 105).mul y.d1).mul (powI y.d2 3)).mul x.d2)).sub (((((ofInt p 105).mul y.d1).mul (powI y.d2 2)).mul y.d3).mul x.d1)).add (((ofInt p 105).mul (powI y.d2 4)).mul x.d1)).mul (powI y.d1.recip 9))⟩

theorem eval_sound {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {a : ℝ}
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains (qdata5 jx jy) a := by
  rcases hx with ⟨hx0,hx1,hx2,hx3,hx4,hx5⟩
  rcases hy with ⟨hy0,hy1,hy2,hy3,hy4,hy5⟩
  have hr := recip_sound hp hy1
  dsimp only [DyadicJet5Enclosure.Contains, eval, qdata5]
  refine ⟨hx0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound hx1 hr)
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (mul_sound hy1 hx2) (mul_sound hy2 hx1)) (powI_sound hr 3))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 2) hx3) (mul_sound (mul_sound (mul_sound (ofInt_sound p 3) hy1) hy2) hx2)) (mul_sound (mul_sound hy1 hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 3) (powI_sound hy2 2)) hx1)) (powI_sound hr 5))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 3) hx4) (mul_sound (mul_sound (mul_sound (ofInt_sound p 6) (powI_sound hy1 2)) hy2) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 4) (powI_sound hy1 2)) hy3) hx2)) (mul_sound (mul_sound (powI_sound hy1 2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) hy1) (powI_sound hy2 2)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) hy1) hy2) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy2 3)) hx1)) (powI_sound hr 7))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (add_sound (add_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 4) hx5) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy2) hx4)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy3) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 5) (powI_sound hy1 3)) hy4) hx2)) (mul_sound (mul_sound (powI_sound hy1 3) hy5) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 45) (powI_sound hy1 2)) (powI_sound hy2 2)) hx3)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 60) (powI_sound hy1 2)) hy2) hy3) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy1 2)) hy2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 2)) (powI_sound hy3 2)) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 3)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 2)) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 105) (powI_sound hy2 4)) hx1)) (powI_sound hr 9))

theorem contains_of_eqAt {p : ℕ} {x : DyadicJet5Enclosure p}
    {f g : Jet5} {a : ℝ} (hx : x.Contains f a) (he : f.EqAt g a) :
    x.Contains g a := by
  rcases he with ⟨h0,h1,h2,h3,h4,h5⟩
  simpa only [DyadicJet5Enclosure.Contains, h0,h1,h2,h3,h4,h5] using hx

/-- The remaining parameter assumptions are scalar equality and soundness of
the two stable jets; the full fifth-order inverse recurrence is proved here. -/
theorem eval_contains_canonical {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {U : Set ℝ} (hU : IsOpen U)
    (hjx : jx.SoundOn U) (hjy : jy.SoundOn U)
    (hrange : ∀ a ∈ U, jy.d0 a ∈ GeneralCK.e8SlopeRange)
    (hvalue : ∀ a ∈ U, jx.d0 a = GeneralCK.e8Q (jy.d0 a))
    {a : ℝ} (ha : a ∈ U)
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (jy.d0 a) := by
  have hpReal : jy.d1 a ≠ 0 := by
    have hh := hy.2.1.1
    have hpos : (0 : ℝ) < y.d1.lo := by exact_mod_cast hp
    have hs := scale_cast_pos p
    intro he
    rw [he, mul_zero] at hh
    linarith
  have result := contains_of_eqAt (eval_sound hx hy hp)
    (qdata5_eq_canonical hU hjx hjy hrange hvalue ha hpReal)
  exact result

#print axioms eval_sound
#print axioms eval_contains_canonical

end GeneralCK.Certificates.E8TAxisReparamInterval

