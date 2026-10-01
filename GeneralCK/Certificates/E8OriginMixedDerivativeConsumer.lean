import GeneralCK.Certificates.E8TauDiscRealAgreement

/-! Repeated one-variable integration for the E8 origin checker. -/

namespace GeneralCK.Certificates.E8OriginMixedDerivativeConsumer

open Set

/-- Positivity of the `∂s²∂t` derivative, together with the three exact axis
zeros, implies positivity of the original bivariate function. -/
theorem positive_of_mixed_derivative
    {D Ds Dss K : ℝ → ℝ → ℝ}
    {R : ℝ}
    (hD0 : ∀ t, 0 ≤ t → t ≤ R → D 0 t = 0)
    (hDs0 : ∀ t, 0 ≤ t → t ≤ R → Ds 0 t = 0)
    (hDss0 : ∀ s, 0 ≤ s → s ≤ R → Dss s 0 = 0)
    (hD : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
      HasDerivAt (fun u => D u t) (Ds s t) s)
    (hDs : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
      HasDerivAt (fun u => Ds u t) (Dss s t) s)
    (hDss : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
      HasDerivAt (fun v => Dss s v) (K s t) t)
    (hK : ∀ s t, 0 ≤ s → 0 < t → s + t ≤ R → 0 < K s t)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t ≤ R) :
    0 < D s t := by
  have hDssPos (u : ℝ) (hu : 0 ≤ u) (huUpper : u ≤ s) : 0 < Dss u t := by
    have hmono : StrictMonoOn (fun v => Dss u v) (Icc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      · intro v hv
        exact (hDss u v hu hv.1
          ((add_le_add huUpper hv.2).trans hst)).continuousAt.continuousWithinAt
      · intro v hv
        have hv' : 0 < v ∧ v < t := by simpa [mem_Ioo] using hv
        rw [(hDss u v hu hv'.1.le
          ((add_le_add huUpper hv'.2.le).trans hst)).deriv]
        exact hK u v hu hv'.1 (by linarith)
    have hlt := hmono (show 0 ∈ Icc (0 : ℝ) t by constructor <;> linarith)
      (show t ∈ Icc (0 : ℝ) t by constructor <;> linarith) ht
    simpa [hDss0 u hu (huUpper.trans (by linarith [hst]))] using hlt
  have hDsPos (u : ℝ) (hu : 0 < u) (huUpper : u ≤ s) : 0 < Ds u t := by
    have hmono : StrictMonoOn (fun v => Ds v t) (Icc 0 u) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 u)
      · intro v hv
        exact (hDs v t hv.1 ht.le
          ((add_le_add (hv.2.trans huUpper) (le_refl t)).trans hst)).continuousAt.continuousWithinAt
      · intro v hv
        have hv' : 0 < v ∧ v < u := by simpa [mem_Ioo] using hv
        rw [(hDs v t hv'.1.le ht.le
          ((add_le_add (hv'.2.le.trans huUpper) (le_refl t)).trans hst)).deriv]
        exact hDssPos v hv'.1.le (hv'.2.le.trans huUpper)
    have hlt := hmono (show 0 ∈ Icc (0 : ℝ) u by constructor <;> linarith)
      (show u ∈ Icc (0 : ℝ) u by constructor <;> linarith) hu
    simpa [hDs0 t ht.le (by linarith [hst])] using hlt
  have hmono : StrictMonoOn (fun u => D u t) (Icc 0 s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s)
    · intro u hu
      exact (hD u t hu.1 ht.le
        ((add_le_add hu.2 (le_refl t)).trans hst)).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : 0 < u ∧ u < s := by simpa [mem_Ioo] using hu
      rw [(hD u t hu'.1.le ht.le
        ((add_le_add hu'.2.le (le_refl t)).trans hst)).deriv]
      exact hDsPos u hu'.1 hu'.2.le
  have hlt := hmono (show 0 ∈ Icc (0 : ℝ) s by constructor <;> linarith)
    (show s ∈ Icc (0 : ℝ) s by constructor <;> linarith) hs
  simpa [hD0 t ht.le (by linarith [hst])] using hlt

noncomputable def deltaS (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  deriv (fun u => e8Delta Q u t) s

noncomputable def deltaSS (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  deriv (fun u => deltaS Q u t) s

noncomputable def deltaSST (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  deriv (fun v => deltaSS Q s v) t

theorem delta_zero_left_of_zero {Q : ℝ → ℝ} (hQ0 : Q 0 = 0) (t : ℝ) :
    e8Delta Q 0 t = 0 := by
  unfold e8Delta
  rw [hQ0]
  ring

theorem delta_zero_right_of_zero {Q : ℝ → ℝ} (hQ0 : Q 0 = 0) (s : ℝ) :
    e8Delta Q s 0 = 0 := by
  unfold e8Delta
  rw [hQ0]
  ring

theorem deltaS_zero_left_of_zero {Q : ℝ → ℝ} (hQ0 : Q 0 = 0)
    (t : ℝ) (hQt : DifferentiableAt ℝ Q t)
    (hQdiff0 : DifferentiableAt ℝ Q 0) :
    deltaS Q 0 t = 0 := by
  unfold deltaS
  rw [deriv_e8Delta_left Q 0 t (by simpa using hQt) (by simpa using hQt) hQdiff0]
  unfold e8DeltaDerivS
  rw [hQ0]
  ring

theorem deltaSS_zero_right_of_zero {Q : ℝ → ℝ} (hQ0 : Q 0 = 0) (s : ℝ) :
    deltaSS Q s 0 = 0 := by
  have hzero : (fun u => deltaS Q u 0) = fun _ => 0 := by
    funext u
    unfold deltaS
    have heq : (fun v => e8Delta Q v 0) = fun _ => 0 := by
      funext v
      exact delta_zero_right_of_zero hQ0 v
    rw [heq, deriv_const]
  unfold deltaSS
  rw [hzero, deriv_const]

theorem qReal_zero (cert : E8OriginAnalyticCertificate.QuantitativeCertificate) :
    E8OriginPositiveConsumer.qReal cert 0 = 0 := by
  have heq := (E8QuantitativeBranchBridge.qDisc_eventuallyEq_qGerm
    cert.inverse).self_of_nhds
  unfold E8OriginPositiveConsumer.qReal
  change (E8QuantitativeBranchBridge.qDisc cert.inverse (0 : ℂ)).re = 0
  rw [heq, E8AnalyticGerm.qGerm_zero]
  rfl

/-- Exact analytic statement produced by the origin Taylor replay.  It uses
the same `∂s²∂t` derivative as `cert_local_K.cpp`; all integration and axis
bookkeeping are separated from its numerical proof. -/
structure MixedDerivativeCertificate (Q : ℝ → ℝ) (R : ℝ) : Prop where
  delta_zero_left : ∀ t, 0 ≤ t → t ≤ R → e8Delta Q 0 t = 0
  deltaS_zero_left : ∀ t, 0 ≤ t → t ≤ R → deltaS Q 0 t = 0
  deltaSS_zero_right : ∀ s, 0 ≤ s → s ≤ R → deltaSS Q s 0 = 0
  hasDeriv_delta : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
    HasDerivAt (fun u => e8Delta Q u t) (deltaS Q s t) s
  hasDeriv_deltaS : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
    HasDerivAt (fun u => deltaS Q u t) (deltaSS Q s t) s
  hasDeriv_deltaSS : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ R →
    HasDerivAt (fun v => deltaSS Q s v) (deltaSST Q s t) t
  mixed_pos : ∀ s t, 0 ≤ s → 0 < t → s + t ≤ R →
    0 < deltaSST Q s t

theorem discOriginPositive_of_mixedDerivativeCertificate
    (cert : E8OriginAnalyticCertificate.QuantitativeCertificate)
    (h : MixedDerivativeCertificate (E8OriginPositiveConsumer.qReal cert)
      (2 / 25 : ℝ)) :
    E8OriginPositiveConsumer.DiscOriginPositive cert := by
  intro s t hadm hst
  exact positive_of_mixed_derivative h.delta_zero_left h.deltaS_zero_left
    h.deltaSS_zero_right h.hasDeriv_delta h.hasDeriv_deltaS h.hasDeriv_deltaSS
    h.mixed_pos hadm.1 hadm.2.1 hst

/-- Aggregate-facing origin owner: real-axis identification and all three
integrations are discharged here.  The sole remaining origin-checker input
is the mixed-derivative certificate for the quantitative branch. -/
theorem e8PositiveOn_of_globalDerivativeBound_and_mixedCertificate
    (hAggregate : E8OriginPositiveConsumer.GlobalDerivativeBound)
    (hmixed : MixedDerivativeCertificate
      (E8OriginPositiveConsumer.qReal
        (E8OriginPositiveConsumer.certificateOfGlobalDerivativeBound hAggregate))
      (2 / 25 : ℝ)) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) := by
  let cert := E8OriginPositiveConsumer.certificateOfGlobalDerivativeBound hAggregate
  apply E8OriginPositiveConsumer.e8PositiveOn_of_quantitativeCertificate cert
  · exact E8TauDiscRealAgreement.realAgreementOnOrigin_of_globalDerivativeBound hAggregate
  · exact discOriginPositive_of_mixedDerivativeCertificate cert hmixed

end GeneralCK.Certificates.E8OriginMixedDerivativeConsumer
