import GeneralCK.Certificates.E8InverseJet5Bridge
import GeneralCK.PureGapE8AxisConsumers

/-!
# Fourth-order directional jets of the regular E8 t derivative

The first four links of a raw `Jet5` suffice for an order-four Taylor
remainder.  Shifting the canonical order-five inverse jet gives exactly
these links for `Q'`, without requiring a sixth derivative of `Q`.
-/

namespace GeneralCK.Certificates.E8TAxisDeltaDirectionalJet

open GeneralCK Set
open E8InverseJet5Bridge

/-- Four derivative links; no derivative of the fourth component is asserted. -/
def Sound4At (j : Jet5) (u : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 u) u ∧ HasDerivAt j.d1 (j.d2 u) u ∧
    HasDerivAt j.d2 (j.d3 u) u ∧ HasDerivAt j.d3 (j.d4 u) u

def Sound4On (j : Jet5) (S : Set ℝ) : Prop := ∀ u ∈ S, Sound4At j u

theorem sound4At_of_soundAt {j : Jet5} {u : ℝ} (h : j.SoundAt u) :
    Sound4At j u :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem sound4At_const (c u : ℝ) : Sound4At (Jet5.const c) u :=
  sound4At_of_soundAt (Jet5.soundAt_const c u)

theorem Sound4At.add {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (a.add b) u :=
  ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.add hb.2.2.2⟩

theorem Sound4At.neg {a : Jet5} {u : ℝ} (ha : Sound4At a u) :
    Sound4At a.neg u :=
  ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.neg⟩

def sub (a b : Jet5) : Jet5 := a.add b.neg

theorem Sound4At.sub {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (sub a b) u :=
  ha.add hb.neg

theorem Sound4At.mul {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (a.mul b) u := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring
  · have h := (((ha.2.2.2.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring

/-- Raw derivatives under the affine change of variable `c + m*u`. -/
def affine (j : Jet5) (c m : ℝ) : Jet5 :=
  ⟨fun u => j.d0 (c + m * u),
   fun u => j.d1 (c + m * u) * m,
   fun u => j.d2 (c + m * u) * m ^ 2,
   fun u => j.d3 (c + m * u) * m ^ 3,
   fun u => j.d4 (c + m * u) * m ^ 4,
   fun u => j.d5 (c + m * u) * m ^ 5⟩

theorem Sound4At.affine {j : Jet5} {c m u : ℝ}
    (h : Sound4At j (c + m * u)) : Sound4At (affine j c m) u := by
  have hi : HasDerivAt (fun v : ℝ => c + m * v) m u := by
    convert! (hasDerivAt_const u c).add ((hasDerivAt_id u).const_mul m) using 1 <;>
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! h.1.comp u hi using 1 <;> simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]
  · convert! (h.2.1.comp u hi).mul_const m using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring
  · convert! (h.2.2.1.comp u hi).mul_const (m ^ 2) using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring
  · convert! (h.2.2.2.comp u hi).mul_const (m ^ 3) using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring

/-- The first derivative of an order-five jet, truncated after order four. -/
def shift (j : Jet5) : Jet5 :=
  ⟨j.d1, j.d2, j.d3, j.d4, j.d5, fun _ => 0⟩

theorem sound4At_shift {j : Jet5} {u : ℝ} (h : j.SoundAt u) :
    Sound4At (shift j) u :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

noncomputable def qJet : Jet5 := e8QJet5 e8ThetaCanonicalJet5

noncomputable def qPrimeJet : Jet5 := shift qJet

theorem qJet_soundAt {y : ℝ} (hy : y ∈ e8SlopeRange) : qJet.SoundAt y :=
  e8QCanonicalJet5_soundAt_unconditional hy

theorem qJet_sound4At {y : ℝ} (hy : y ∈ e8SlopeRange) : Sound4At qJet y :=
  sound4At_of_soundAt (qJet_soundAt hy)

theorem qPrimeJet_sound4At {y : ℝ} (hy : y ∈ e8SlopeRange) :
    Sound4At qPrimeJet y :=
  sound4At_shift (qJet_soundAt hy)

@[simp] theorem qJet_d0 (y : ℝ) : qJet.d0 y = e8Q y := rfl

theorem qJet_d0_eq_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qJet.d0 y = e8RegularQ y :=
  (e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le).symm

theorem qPrimeJet_d0_eq_deriv_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qPrimeJet.d0 y = deriv e8RegularQ y := by
  have hq : HasDerivAt e8Q (qPrimeJet.d0 y) y := (qJet_soundAt hy).1
  have he : e8RegularQ =ᶠ[nhds y] e8Q := by
    filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
    exact e8RegularQ_eq_e8Q hz.le
  exact (hq.congr_of_eventuallyEq he).deriv.symm

/-- Product-rule graph for the first t derivative of the E8 determinant.
The inputs are `Q(A),Q(B),Q(C),Q(D),Q'(A),Q'(B),Q'(C)`. -/
def deltaTGraph (a b c d ap bp cp : Jet5) : Jet5 :=
  (((bp.mul (sub c a)).add ((sub b d).mul (sub cp ap))).add
    (((sub bp cp).mul (d.add a)).neg)).add (((sub b c).mul ap).neg)

theorem sound4At_deltaTGraph {a b c d ap bp cp : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) (hc : Sound4At c u)
    (hd : Sound4At d u) (hap : Sound4At ap u) (hbp : Sound4At bp u)
    (hcp : Sound4At cp u) : Sound4At (deltaTGraph a b c d ap bp cp) u :=
  ((hbp.mul (hc.sub ha)).add ((hb.sub hd).mul (hcp.sub hap))).add
    (((hbp.sub hcp).mul (hd.add ha)).neg) |>.add (((hb.sub hc).mul hap).neg)

/-- All four inverse arguments belong to the positive slope range. -/
def InputsInRange (s t : ℝ) : Prop :=
  t ∈ e8SlopeRange ∧ 2 * s + t ∈ e8SlopeRange ∧
    s + t ∈ e8SlopeRange ∧ s ∈ e8SlopeRange

/-- The order-four jet along `(s,t)=(s0+ds*u,t0+dt*u)`. -/
noncomputable def deltaTJet (s0 t0 ds dt : ℝ) : Jet5 :=
  deltaTGraph
    (affine qJet t0 dt)
    (affine qJet (2 * s0 + t0) (2 * ds + dt))
    (affine qJet (s0 + t0) (ds + dt))
    (affine qJet s0 ds)
    (affine qPrimeJet t0 dt)
    (affine qPrimeJet (2 * s0 + t0) (2 * ds + dt))
    (affine qPrimeJet (s0 + t0) (ds + dt))

theorem deltaTJet_sound4At {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4At (deltaTJet s0 t0 ds dt) u := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u ∈ e8SlopeRange := by
    rw [show (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.1
  have hC : (s0 + t0) + (ds + dt) * u ∈ e8SlopeRange := by
    rw [show (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.2.1
  exact sound4At_deltaTGraph
    (qJet_sound4At h.1).affine (qJet_sound4At hB).affine
    (qJet_sound4At hC).affine (qJet_sound4At h.2.2.2).affine
    (qPrimeJet_sound4At h.1).affine (qPrimeJet_sound4At hB).affine
    (qPrimeJet_sound4At hC).affine

theorem deltaTJet_sound4On {s0 t0 ds dt : ℝ} {S : Set ℝ}
    (h : ∀ u ∈ S, InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4On (deltaTJet s0 t0 ds dt) S :=
  fun u hu => deltaTJet_sound4At (h u hu)

theorem deltaTJet_d0_eq_regular {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    (deltaTJet s0 t0 ds dt).d0 u =
      e8RegularDeltaT (s0 + ds * u) (t0 + dt * u) := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) := by ring
  have hC : (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) := by ring
  have hregB : DifferentiableAt ℝ e8RegularQ
      (2 * (s0 + ds * u) + (t0 + dt * u)) :=
    (e8RegularQ_contDiffAt_of_mem h.2.1).differentiableAt (by norm_num)
  have hregC : DifferentiableAt ℝ e8RegularQ
      ((s0 + ds * u) + (t0 + dt * u)) :=
    (e8RegularQ_contDiffAt_of_mem h.2.2.1).differentiableAt (by norm_num)
  have hregA : DifferentiableAt ℝ e8RegularQ (t0 + dt * u) :=
    (e8RegularQ_contDiffAt_of_mem h.1).differentiableAt (by norm_num)
  rw [e8RegularDeltaT, deriv_e8Delta_right e8RegularQ _ _ hregB hregC hregA]
  dsimp only [deltaTJet, deltaTGraph, sub, Jet5.add, Jet5.neg, Jet5.mul, affine]
  rw [hB, hC, qJet_d0_eq_regular h.1, qJet_d0_eq_regular h.2.1,
    qJet_d0_eq_regular h.2.2.1, qJet_d0_eq_regular h.2.2.2,
    qPrimeJet_d0_eq_deriv_regular h.1,
    qPrimeJet_d0_eq_deriv_regular h.2.1,
    qPrimeJet_d0_eq_deriv_regular h.2.2.1]
  simp only [e8DeltaDerivT]
  ring

#print axioms deltaTJet_sound4On
#print axioms deltaTJet_d0_eq_regular

end GeneralCK.Certificates.E8TAxisDeltaDirectionalJet
