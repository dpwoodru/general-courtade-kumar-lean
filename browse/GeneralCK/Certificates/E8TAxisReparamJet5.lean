import GeneralCK.Certificates.E8InverseJet5Bridge

/-! Semantic handoff for the fifth-order `qdata5` inverse recurrence.

The parameter jets use raw derivatives.  The change of parameter is checked
by the chain rule and uniqueness of derivatives on an open neighborhood.
-/

namespace GeneralCK.Certificates
namespace Jet5

def comp (f g : Jet5) : Jet5 :=
  ⟨fun a => f.d0 (g.d0 a),
   fun a => f.d1 (g.d0 a) * g.d1 a,
   fun a => f.d2 (g.d0 a) * g.d1 a ^ 2 + f.d1 (g.d0 a) * g.d2 a,
   fun a => f.d3 (g.d0 a) * g.d1 a ^ 3 +
     3 * f.d2 (g.d0 a) * g.d1 a * g.d2 a + f.d1 (g.d0 a) * g.d3 a,
   fun a => f.d4 (g.d0 a) * g.d1 a ^ 4 +
     6 * f.d3 (g.d0 a) * g.d1 a ^ 2 * g.d2 a +
     3 * f.d2 (g.d0 a) * g.d2 a ^ 2 +
     4 * f.d2 (g.d0 a) * g.d1 a * g.d3 a + f.d1 (g.d0 a) * g.d4 a,
   fun a => f.d5 (g.d0 a) * g.d1 a ^ 5 +
     10 * f.d4 (g.d0 a) * g.d1 a ^ 3 * g.d2 a +
     15 * f.d3 (g.d0 a) * g.d1 a * g.d2 a ^ 2 +
     10 * f.d3 (g.d0 a) * g.d1 a ^ 2 * g.d3 a +
     10 * f.d2 (g.d0 a) * g.d2 a * g.d3 a +
     5 * f.d2 (g.d0 a) * g.d1 a * g.d4 a + f.d1 (g.d0 a) * g.d5 a⟩

theorem SoundAt.comp {f g : Jet5} {a : ℝ}
    (hf : f.SoundAt (g.d0 a)) (hg : g.SoundAt a) :
    (f.comp g).SoundAt a := by
  have f0 := hf.1.comp a hg.1
  have f1 := hf.2.1.comp a hg.1
  have f2 := hf.2.2.1.comp a hg.1
  have f3 := hf.2.2.2.1.comp a hg.1
  have f4 := hf.2.2.2.2.comp a hg.1
  refine ⟨f0, ?_, ?_, ?_, ?_⟩
  · convert! f1.mul hg.2.1 using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := (f2.mul (hg.2.1.pow 2)).add (f1.mul hg.2.2.1)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := ((f3.mul (hg.2.1.pow 3)).add
      (((f2.mul hg.2.1).mul hg.2.2.1).const_mul 3)).add (f1.mul hg.2.2.2.1)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring
  · have h := ((((f4.mul (hg.2.1.pow 4)).add
      (((f3.mul (hg.2.1.pow 2)).mul hg.2.2.1).const_mul 6)).add
      ((f2.mul (hg.2.2.1.pow 2)).const_mul 3)).add
      (((f2.mul hg.2.1).mul hg.2.2.2.1).const_mul 4)).add (f1.mul hg.2.2.2.2)
    convert! h using 1 <;>
      simp only [Jet5.comp, Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
      first | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]; ring) | ring

def EqAt (f g : Jet5) (a : ℝ) : Prop :=
  f.d0 a = g.d0 a ∧ f.d1 a = g.d1 a ∧ f.d2 a = g.d2 a ∧
    f.d3 a = g.d3 a ∧ f.d4 a = g.d4 a ∧ f.d5 a = g.d5 a

theorem eqAt_of_soundOn {f g : Jet5} {U : Set ℝ} (hU : IsOpen U)
    (hf : f.SoundOn U) (hg : g.SoundOn U)
    (h0 : Set.EqOn f.d0 g.d0 U) {a : ℝ} (ha : a ∈ U) : f.EqAt g a := by
  have step {u v du dv : ℝ → ℝ}
      (hu : ∀ x ∈ U, HasDerivAt u (du x) x)
      (hv : ∀ x ∈ U, HasDerivAt v (dv x) x)
      (he : Set.EqOn u v U) : Set.EqOn du dv U := by
    intro x hx
    have hevent : u =ᶠ[nhds x] v := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) he
    exact (hu x hx).unique ((hv x hx).congr_of_eventuallyEq hevent)
  have h1 := step (fun x hx => (hf x hx).1) (fun x hx => (hg x hx).1) h0
  have h2 := step (fun x hx => (hf x hx).2.1) (fun x hx => (hg x hx).2.1) h1
  have h3 := step (fun x hx => (hf x hx).2.2.1) (fun x hx => (hg x hx).2.2.1) h2
  have h4 := step (fun x hx => (hf x hx).2.2.2.1) (fun x hx => (hg x hx).2.2.2.1) h3
  have h5 := step (fun x hx => (hf x hx).2.2.2.2) (fun x hx => (hg x hx).2.2.2.2) h4
  exact ⟨h0 ha, h1 ha, h2 ha, h3 ha, h4 ha, h5 ha⟩

end Jet5

namespace E8TAxisReparamJet5

open E8InverseJet5Bridge

/-- Exactly the raw derivative formulas in the retained C++ `qdata5`. -/
noncomputable def qdata5 (x y : Jet5) : Jet5 :=
  let p := y.d1
  let p2 := y.d2
  let p3 := y.d3
  let p4 := y.d4
  let p5 := y.d5
  ⟨x.d0,
   fun a => x.d1 a / p a,
   fun a => (p a * x.d2 a - p2 a * x.d1 a) / p a ^ 3,
   fun a => (p a ^ 2 * x.d3 a - 3 * p a * p2 a * x.d2 a -
     p a * p3 a * x.d1 a + 3 * p2 a ^ 2 * x.d1 a) / p a ^ 5,
   fun a => (p a ^ 3 * x.d4 a - 6 * p a ^ 2 * p2 a * x.d3 a -
     4 * p a ^ 2 * p3 a * x.d2 a - p a ^ 2 * p4 a * x.d1 a +
     15 * p a * p2 a ^ 2 * x.d2 a + 10 * p a * p2 a * p3 a * x.d1 a -
     15 * p2 a ^ 3 * x.d1 a) / p a ^ 7,
   fun a => (p a ^ 4 * x.d5 a - 10 * p a ^ 3 * p2 a * x.d4 a -
     10 * p a ^ 3 * p3 a * x.d3 a - 5 * p a ^ 3 * p4 a * x.d2 a -
     p a ^ 3 * p5 a * x.d1 a + 45 * p a ^ 2 * p2 a ^ 2 * x.d3 a +
     60 * p a ^ 2 * p2 a * p3 a * x.d2 a +
     15 * p a ^ 2 * p2 a * p4 a * x.d1 a +
     10 * p a ^ 2 * p3 a ^ 2 * x.d1 a -
     105 * p a * p2 a ^ 3 * x.d2 a -
     105 * p a * p2 a ^ 2 * p3 a * x.d1 a +
     105 * p2 a ^ 4 * x.d1 a) / p a ^ 9⟩

/-- Component evaluation at the parameter value; this is not jet composition. -/
def atParam (f y : Jet5) : Jet5 :=
  ⟨f.d0 ∘ y.d0, f.d1 ∘ y.d0, f.d2 ∘ y.d0,
    f.d3 ∘ y.d0, f.d4 ∘ y.d0, f.d5 ∘ y.d0⟩

theorem qdata5_eq_of_comp {x y f : Jet5} {a : ℝ}
    (heq : x.EqAt (f.comp y) a) (hp : y.d1 a ≠ 0) :
    (qdata5 x y).EqAt (atParam f y) a := by
  rcases heq with ⟨h0, h1, h2, h3, h4, h5⟩
  dsimp only [Jet5.comp] at h0 h1 h2 h3 h4 h5
  dsimp only [Jet5.EqAt, qdata5, atParam, Function.comp_def]
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    field_simp [hp]
  · rw [h1, h2]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3, h4]
    field_simp [hp]
    <;> ring
  · rw [h1, h2, h3, h4, h5]
    field_simp [hp]
    <;> ring

/-- Sound parameter jets and the scalar parameter identity determine every
entry of the canonical inverse jet.  No higher derivative identity is a premise. -/
theorem qdata5_eq_canonical {x y : Jet5} {U : Set ℝ}
    (hU : IsOpen U) (hx : x.SoundOn U) (hy : y.SoundOn U)
    (hrange : ∀ a ∈ U, y.d0 a ∈ GeneralCK.e8SlopeRange)
    (hvalue : ∀ a ∈ U, x.d0 a = GeneralCK.e8Q (y.d0 a))
    {a : ℝ} (ha : a ∈ U) (hp : y.d1 a ≠ 0) :
    (qdata5 x y).EqAt (atParam (e8QJet5 e8ThetaCanonicalJet5) y) a := by
  apply qdata5_eq_of_comp (hp := hp)
  apply Jet5.eqAt_of_soundOn hU hx
  · intro b hb
    exact (e8QCanonicalJet5_soundAt_unconditional (hrange b hb)).comp (hy b hb)
  · exact hvalue
  · exact ha

#print axioms qdata5_eq_of_comp
#print axioms qdata5_eq_canonical

end E8TAxisReparamJet5
end GeneralCK.Certificates
