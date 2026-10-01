import GeneralCK.ReflectionRegularContact
import GeneralCK.Certificates.Jet2Composition

namespace GeneralCK.Certificates
open GeneralCK.Reflection

noncomputable def regularContactJet : Jet2 :=
  ⟨regularContact,regularContactFirst,regularContactSecond⟩

theorem regularContactJet_soundOn (s : Set ℝ) : regularContactJet.SoundOn s :=
  fun t _ => ⟨hasDerivAt_regularContact t,hasDerivAt_regularContactFirst t⟩

theorem regularContactJet_comp_soundOn {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s) :
    (regularContactJet.comp j).SoundOn s :=
  (regularContactJet_soundOn Set.univ).comp hj (fun _ _ => Set.mem_univ _)

end GeneralCK.Certificates
