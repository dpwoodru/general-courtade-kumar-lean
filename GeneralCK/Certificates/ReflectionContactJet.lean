import GeneralCK.ReflectionContactInverse
import GeneralCK.Certificates.Jet2Composition

namespace GeneralCK.Certificates
open Set Filter
open scoped Topology

/-- The inverse of the decreasing natural-entropy bias ratio, with explicit
first and second inverse-function derivatives. -/
noncomputable def reflectionContactJet : Jet2 where
  value := Reflection.biasContact
  first := fun y => (Reflection.biasRprime (Reflection.biasContact y))⁻¹
  second := fun y => -Reflection.biasRsecond (Reflection.biasContact y) /
    (Reflection.biasRprime (Reflection.biasContact y))^3

theorem reflectionContactJet_soundAt {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.SoundAt y := by
  refine ⟨Reflection.hasDerivAt_biasContact_inv hy, ?_⟩
  have heq : reflectionContactJet.first =ᶠ[𝓝 y] deriv Reflection.biasContact := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (Reflection.hasDerivAt_biasContact_inv ht).deriv.symm
  exact (Reflection.hasDerivAt_deriv_biasContact hy).congr_of_eventuallyEq heq

theorem reflectionContactJet_soundOn : reflectionContactJet.SoundOn (Ioi 0) :=
  fun _ hy => reflectionContactJet_soundAt hy

/-- A positive sound input jet can be passed through the implicit contact map. -/
theorem reflectionContactJet_comp_soundOn {j : Jet2} {s : Set ℝ}
    (hj : j.SoundOn s) (hpos : ∀ t ∈ s, 0 < j.value t) :
    (reflectionContactJet.comp j).SoundOn s :=
  reflectionContactJet_soundOn.comp hj hpos

theorem reflectionContactJet_comp_soundAt {j : Jet2} {t : ℝ}
    (hj : j.SoundAt t) (hpos : 0 < j.value t) :
    (reflectionContactJet.comp j).SoundAt t :=
  (reflectionContactJet_soundAt hpos).comp hj

end GeneralCK.Certificates
