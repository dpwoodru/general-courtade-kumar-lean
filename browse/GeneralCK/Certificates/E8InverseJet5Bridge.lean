import GeneralCK.Certificates.Jet5ReciprocalLog
import GeneralCK.Certificates.E8ThetaFourthDerivative

/-! A fifth-order inverse recurrence for the concrete `e8Q`.

`ThetaJetReplay` records actual derivatives of `e8Theta` through order five
on the positive axis.  The concrete canonical replay is proved below without
an additional smoothness premise. -/

namespace GeneralCK.Certificates.E8InverseJet5Bridge

open GeneralCK Set

def ThetaJetReplay (θ : Jet5) : Prop :=
  θ.SoundOn (Ioi 0) ∧
    ∀ x, 0 < x → θ.d0 x = e8Theta x ∧ θ.d1 x = deriv e8Theta x

/-- The canonical raw-derivative jet of `e8Theta`. -/
noncomputable def e8ThetaCanonicalJet5 : Jet5 :=
  ⟨e8Theta,
   deriv e8Theta,
   deriv (deriv e8Theta),
   deriv (deriv (deriv e8Theta)),
   deriv (deriv (deriv (deriv e8Theta))),
   deriv (deriv (deriv (deriv (deriv e8Theta))))⟩

/-- A compatibility interface retained for callers that supply smoothness
directly.  The concrete instance is discharged unconditionally below. -/
def E8ThetaSmooth345 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv e8Theta)) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

/-- Compatibility interface for the last two soundness links. -/
def E8ThetaSmooth45 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

/-- Compatibility interface for the final soundness link. -/
def E8ThetaSmooth5 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

theorem e8ThetaSmooth45_of_smooth5 (h : E8ThetaSmooth5) :
    E8ThetaSmooth45 := by
  intro x hx
  exact ⟨GeneralCK.differentiableAt_deriv3_e8Theta hx, h x hx⟩

/-- The final smoothness premise follows from the `C³` regularity of the
explicit second-derivative formula. -/
theorem e8Theta_smooth5 : E8ThetaSmooth5 := by
  intro x hx
  exact GeneralCK.differentiableAt_deriv4_e8Theta hx

theorem e8ThetaSmooth345_of_smooth45 (h : E8ThetaSmooth45) :
    E8ThetaSmooth345 := by
  intro x hx
  exact ⟨GeneralCK.differentiableAt_deriv2_e8Theta hx, (h x hx).1, (h x hx).2⟩

/-- Construction of the full replay from explicit smoothness links. -/
theorem e8ThetaCanonicalJet5_replay (h : E8ThetaSmooth345) :
    ThetaJetReplay e8ThetaCanonicalJet5 := by
  constructor
  · intro x hx
    have hh := h x hx
    simp only [e8ThetaCanonicalJet5]
    exact ⟨(hasDerivAt_e8Theta hx).differentiableAt.hasDerivAt,
      (GeneralCK.hasDerivAt_deriv_e8Theta hx).differentiableAt.hasDerivAt,
      hh.1.hasDerivAt, hh.2.1.hasDerivAt, hh.2.2.hasDerivAt⟩
  · intro x _
    simp [e8ThetaCanonicalJet5]

/-- Full canonical replay from the two residual higher-smoothness links. -/
theorem e8ThetaCanonicalJet5_replay_of_smooth45 (h : E8ThetaSmooth45) :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay (e8ThetaSmooth345_of_smooth45 h)

/-- Full canonical replay from the sole residual d4→d5 link. -/
theorem e8ThetaCanonicalJet5_replay_of_smooth5 (h : E8ThetaSmooth5) :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay_of_smooth45 (e8ThetaSmooth45_of_smooth5 h)

/-- Unconditional order-five replay for the concrete E8 theta function. -/
theorem e8ThetaCanonicalJet5_replay_unconditional :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay_of_smooth5 e8Theta_smooth5

noncomputable def e8QJet5 (θ : Jet5) : Jet5 :=
  let A := fun y => θ.d1 (e8Q y)
  let B := fun y => θ.d2 (e8Q y)
  let C := fun y => θ.d3 (e8Q y)
  let D := fun y => θ.d4 (e8Q y)
  let E := fun y => θ.d5 (e8Q y)
  let r := fun y => (A y)⁻¹
  ⟨e8Q, r,
   fun y => -B y*r y^3,
   fun y => 3*B y^2*r y^5-C y*r y^4,
   fun y => -15*B y^3*r y^7+10*B y*C y*r y^6-D y*r y^5,
   fun y => 105*B y^4*r y^9-105*B y^2*C y*r y^8+
     (10*C y^2+15*B y*D y)*r y^7-E y*r y^6⟩

theorem e8QJet5_soundAt {θ : Jet5} (hθ : ThetaJetReplay θ)
    {y : ℝ} (hy : y ∈ e8SlopeRange) : (e8QJet5 θ).SoundAt y := by
  let A := fun z => θ.d1 (e8Q z)
  let B := fun z => θ.d2 (e8Q z)
  let C := fun z => θ.d3 (e8Q z)
  let D := fun z => θ.d4 (e8Q z)
  let E := fun z => θ.d5 (e8Q z)
  let r := fun z => (A z)⁻¹
  have hqpos : 0 < e8Q y := e8Q_pos hy
  have hs := hθ.1 (e8Q y) hqpos
  have hAeq : A y = deriv e8Theta (e8Q y) := hθ.2 _ hqpos |>.2
  have hAne : A y ≠ 0 := by
    rw [hAeq]
    exact (deriv_e8Theta_pos hqpos).ne'
  have hq1 : HasDerivAt e8Q (r y) y := by
    simpa [r, A, hAeq] using hasDerivAt_e8Q hy
  have hA : HasDerivAt A (B y*r y) y := by
    convert! hs.2.1.comp y hq1 using 1 <;> simp [A, B, r, Function.comp_def]
  have hB : HasDerivAt B (C y*r y) y := by
    convert! hs.2.2.1.comp y hq1 using 1 <;> simp [B, C, r, Function.comp_def]
  have hC : HasDerivAt C (D y*r y) y := by
    convert! hs.2.2.2.1.comp y hq1 using 1 <;> simp [C, D, r, Function.comp_def]
  have hD : HasDerivAt D (E y*r y) y := by
    convert! hs.2.2.2.2.comp y hq1 using 1 <;> simp [D, E, r, Function.comp_def]
  have hr0 := hA.inv hAne
  have hr : HasDerivAt r (-B y*r y^3) y := by
    convert! hr0 using 1 <;> simp only [r] <;> field_simp [hAne] <;> ring
  refine ⟨hq1, hr, ?_, ?_, ?_⟩
  · have h := (hB.mul (hr.pow 3)).neg
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((hB.pow 2).mul (hr.pow 5)).const_mul 3 |>.sub
      (hC.mul (hr.pow 4))
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((hB.pow 3).mul (hr.pow 7)).const_mul (-15)).add
      ((((hB.mul hC).mul (hr.pow 6)).const_mul 10).sub
        (hD.mul (hr.pow 5)))
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring

/-- The fifth-order concrete inverse jet now depends only on the three
explicit residual smoothness links of `e8Theta`. -/
theorem e8QCanonicalJet5_soundAt (h : E8ThetaSmooth345)
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y :=
  e8QJet5_soundAt (e8ThetaCanonicalJet5_replay h) hy

/-- Concrete order-five inverse soundness from the two remaining links. -/
theorem e8QCanonicalJet5_soundAt_of_smooth45 (h : E8ThetaSmooth45)
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y :=
  e8QJet5_soundAt (e8ThetaCanonicalJet5_replay_of_smooth45 h) hy

/-- Concrete order-five inverse soundness from the sole residual link. -/
theorem e8QCanonicalJet5_soundAt_of_smooth5 (h : E8ThetaSmooth5)
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y :=
  e8QJet5_soundAt (e8ThetaCanonicalJet5_replay_of_smooth5 h) hy

/-- Unconditional fifth-order inverse jet for the concrete `e8Q`. -/
theorem e8QCanonicalJet5_soundAt_unconditional
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y :=
  e8QJet5_soundAt e8ThetaCanonicalJet5_replay_unconditional hy

end GeneralCK.Certificates.E8InverseJet5Bridge
