import GeneralCK.Certificates.Jet2

namespace GeneralCK.Certificates.Jet2

/-- Composition, including the second-order chain rule. -/
def comp (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value (k.value t),
    fun t => j.first (k.value t)*k.first t,
    fun t => j.second (k.value t)*(k.first t)^2+j.first (k.value t)*k.second t⟩

theorem SoundAt.comp {j k : Jet2} {t : ℝ} (hj : j.SoundAt (k.value t))
    (hk : k.SoundAt t) : (j.comp k).SoundAt t := by
  refine ⟨hj.1.comp t hk.1, ?_⟩
  have hh := (hj.2.comp t hk.1).mul hk.2
  convert! hh using 1
  simp only [Jet2.comp, Function.comp_apply]
  ring

theorem SoundOn.comp {j k : Jet2} {s u : Set ℝ} (hj : j.SoundOn u)
    (hk : k.SoundOn s) (hmap : Set.MapsTo k.value s u) : (j.comp k).SoundOn s :=
  fun t ht => (hj (k.value t) (hmap ht)).comp (hk t ht)

end GeneralCK.Certificates.Jet2
