import GeneralCK.Certificates.Jet2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Order-five univariate jets with raw derivative components. -/

namespace GeneralCK.Certificates

structure Jet5 where
  d0 : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  d3 : ℝ → ℝ
  d4 : ℝ → ℝ
  d5 : ℝ → ℝ

namespace Jet5

def SoundAt (j : Jet5) (t : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 t) t ∧ HasDerivAt j.d1 (j.d2 t) t ∧
  HasDerivAt j.d2 (j.d3 t) t ∧ HasDerivAt j.d3 (j.d4 t) t ∧
  HasDerivAt j.d4 (j.d5 t) t

def SoundOn (j : Jet5) (s : Set ℝ) : Prop := ∀ t ∈ s, j.SoundAt t

def const (c : ℝ) : Jet5 :=
  ⟨fun _ => c, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def variableJet : Jet5 :=
  ⟨id, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def add (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t + b.d0 t, fun t => a.d1 t + b.d1 t,
   fun t => a.d2 t + b.d2 t, fun t => a.d3 t + b.d3 t,
   fun t => a.d4 t + b.d4 t, fun t => a.d5 t + b.d5 t⟩

def neg (a : Jet5) : Jet5 :=
  ⟨fun t => -a.d0 t, fun t => -a.d1 t, fun t => -a.d2 t,
   fun t => -a.d3 t, fun t => -a.d4 t, fun t => -a.d5 t⟩

/-- Raw-derivative Leibniz propagation through order five. -/
def mul (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t * b.d0 t,
   fun t => a.d1 t * b.d0 t + a.d0 t * b.d1 t,
   fun t => a.d2 t * b.d0 t + 2*a.d1 t*b.d1 t + a.d0 t*b.d2 t,
   fun t => a.d3 t*b.d0 t + 3*a.d2 t*b.d1 t + 3*a.d1 t*b.d2 t + a.d0 t*b.d3 t,
   fun t => a.d4 t*b.d0 t + 4*a.d3 t*b.d1 t + 6*a.d2 t*b.d2 t +
     4*a.d1 t*b.d3 t + a.d0 t*b.d4 t,
   fun t => a.d5 t*b.d0 t + 5*a.d4 t*b.d1 t + 10*a.d3 t*b.d2 t +
     10*a.d2 t*b.d3 t + 5*a.d1 t*b.d4 t + a.d0 t*b.d5 t⟩

/-- Raw Faà di Bruno propagation for the exponential through order five. -/
noncomputable def exp (a : Jet5) : Jet5 :=
  ⟨fun t => Real.exp (a.d0 t),
   fun t => Real.exp (a.d0 t)*a.d1 t,
   fun t => Real.exp (a.d0 t)*(a.d1 t^2+a.d2 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^3+3*a.d1 t*a.d2 t+a.d3 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^4+6*a.d1 t^2*a.d2 t+3*a.d2 t^2+
     4*a.d1 t*a.d3 t+a.d4 t),
   fun t => Real.exp (a.d0 t)*(a.d1 t^5+10*a.d1 t^3*a.d2 t+
     15*a.d1 t*a.d2 t^2+10*a.d1 t^2*a.d3 t+10*a.d2 t*a.d3 t+
     5*a.d1 t*a.d4 t+a.d5 t)⟩

theorem soundAt_const (c t : ℝ) : (const c).SoundAt t := by
  exact ⟨hasDerivAt_const t c, hasDerivAt_const t 0, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t := by
  exact ⟨hasDerivAt_id t, hasDerivAt_const t 1, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem SoundAt.add {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.add b).SoundAt t := by
  exact ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.1.add hb.2.2.2.1, ha.2.2.2.2.add hb.2.2.2.2⟩

theorem SoundAt.neg {a : Jet5} {t : ℝ} (ha : a.SoundAt t) : a.neg.SoundAt t := by
  exact ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.1.neg, ha.2.2.2.2.neg⟩

theorem SoundAt.mul {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.mul b).SoundAt t := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;> first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.1.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((((ha.2.2.2.2.mul hb.1).add
      ((ha.2.2.2.1.mul hb.2.1).const_mul 4)).add
      ((ha.2.2.1.mul hb.2.2.1).const_mul 6)).add
      ((ha.2.1.mul hb.2.2.2.1).const_mul 4)).add (ha.1.mul hb.2.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring

/-- The order-five jet of `exp (c+m*t)`.  This is the first transcendental
shape needed by the E8 parameterization (`c=0`, `m=-2`). -/
noncomputable def expAffine (c m : ℝ) : Jet5 :=
  ⟨fun t => Real.exp (c+m*t), fun t => Real.exp (c+m*t)*m,
   fun t => Real.exp (c+m*t)*m^2, fun t => Real.exp (c+m*t)*m^3,
   fun t => Real.exp (c+m*t)*m^4, fun t => Real.exp (c+m*t)*m^5⟩

theorem soundAt_expAffine (c m t : ℝ) : (expAffine c m).SoundAt t := by
  have hi : HasDerivAt (fun u : ℝ => c+m*u) m t := by
    convert! (hasDerivAt_const t c).add ((hasDerivAt_id t).mul_const m) using 1
    · funext u
      simp [id_eq, mul_comm]
    · ring
  have he := (Real.hasDerivAt_exp (c+m*t)).comp t hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! he using 1 <;> simp [expAffine]
  · convert! he.mul_const m using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^2) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^3) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^4) using 1 <;> simp [expAffine] <;> ring

theorem soundOn_const (c : ℝ) (s : Set ℝ) : (const c).SoundOn s := fun t _ => soundAt_const c t
theorem soundOn_variable (s : Set ℝ) : variableJet.SoundOn s := fun t _ => soundAt_variable t

end Jet5
end GeneralCK.Certificates
