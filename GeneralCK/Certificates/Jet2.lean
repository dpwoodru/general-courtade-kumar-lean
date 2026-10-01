import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GeneralCK.Certificates

/-- A scalar or directional second-order jet with explicit derivative functions. -/
structure Jet2 where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ

namespace Jet2
open scoped Topology

/-- Both derivative assertions are required; no totalized derivative is used.
Use `SoundOn` on a neighborhood to identify the actual second derivative. -/
def SoundAt (j : Jet2) (t : ℝ) : Prop :=
  HasDerivAt j.value (j.first t) t ∧ HasDerivAt j.first (j.second t) t

/-- Soundness throughout a domain, with unrestricted local derivatives at its points. -/
def SoundOn (j : Jet2) (s : Set ℝ) : Prop := ∀ t ∈ s, j.SoundAt t

def const (c : ℝ) : Jet2 := ⟨fun _ => c, fun _ => 0, fun _ => 0⟩
def variableJet : Jet2 := ⟨id, fun _ => 1, fun _ => 0⟩

def add (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value t+k.value t, fun t => j.first t+k.first t,
    fun t => j.second t+k.second t⟩

def neg (j : Jet2) : Jet2 :=
  ⟨fun t => -j.value t, fun t => -j.first t, fun t => -j.second t⟩

def mul (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value t*k.value t,
    fun t => j.first t*k.value t+j.value t*k.first t,
    fun t => j.second t*k.value t+2*j.first t*k.first t+j.value t*k.second t⟩

noncomputable def inv (j : Jet2) : Jet2 :=
  ⟨fun t => (j.value t)⁻¹,
    fun t => -j.first t/(j.value t)^2,
    fun t => 2*(j.first t)^2/(j.value t)^3-j.second t/(j.value t)^2⟩

noncomputable def log (j : Jet2) : Jet2 :=
  ⟨fun t => Real.log (j.value t),
    fun t => j.first t/j.value t,
    fun t => j.second t/j.value t-(j.first t)^2/(j.value t)^2⟩

theorem soundAt_const (c t : ℝ) : (const c).SoundAt t :=
  ⟨hasDerivAt_const t c, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t :=
  ⟨hasDerivAt_id t, hasDerivAt_const t 1⟩

theorem SoundAt.add {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.add k).SoundAt t := ⟨hj.1.add hk.1, hj.2.add hk.2⟩

theorem SoundAt.neg {j : Jet2} {t : ℝ} (hj : j.SoundAt t) :
    j.neg.SoundAt t := ⟨hj.1.neg, hj.2.neg⟩

theorem SoundAt.mul {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.mul k).SoundAt t := by
  refine ⟨hj.1.mul hk.1, ?_⟩
  have hh := (hj.2.mul hk.1).add (hj.1.mul hk.2)
  convert! hh using 1
  simp only [Jet2.mul]
  ring

theorem SoundAt.inv {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.inv.SoundAt t := by
  constructor
  · convert! hj.1.inv hn using 1
  · have hh := hj.2.neg.div (hj.1.pow 2) (pow_ne_zero 2 hn)
    convert! hh using 1
    simp only [Jet2.inv, Pi.pow_apply, Pi.neg_apply]
    field_simp [hn]
    ring

theorem SoundAt.log {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.log.SoundAt t := by
  refine ⟨hj.1.log hn, ?_⟩
  have hh := hj.2.div hj.1 hn
  convert! hh using 1
  simp only [Jet2.log]
  field_simp [hn]

theorem soundOn_const (c : ℝ) (s : Set ℝ) : (const c).SoundOn s :=
  fun t _ => soundAt_const c t

theorem soundOn_variable (s : Set ℝ) : variableJet.SoundOn s :=
  fun t _ => soundAt_variable t

theorem SoundOn.add {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s) :
    (j.add k).SoundOn s := fun t ht => (hj t ht).add (hk t ht)

theorem SoundOn.neg {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s) :
    j.neg.SoundOn s := fun t ht => (hj t ht).neg

theorem SoundOn.mul {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s) :
    (j.mul k).SoundOn s := fun t ht => (hj t ht).mul (hk t ht)

theorem SoundOn.inv {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hn : ∀ t ∈ s, j.value t ≠ 0) : j.inv.SoundOn s :=
  fun t ht => (hj t ht).inv (hn t ht)

theorem SoundOn.log {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hn : ∀ t ∈ s, j.value t ≠ 0) : j.log.SoundOn s :=
  fun t ht => (hj t ht).log (hn t ht)

theorem SoundOn.mono {j : Jet2} {s u : Set ℝ} (hj : j.SoundOn s) (hu : u ⊆ s) :
    j.SoundOn u := fun t ht => hj t (hu ht)

/-- A locally sound jet supplies a derivative of the actual first derivative.
The neighborhood assumption prevents identifying a second derivative from
an isolated pointwise assertion about an arbitrarily chosen first function. -/
theorem SoundOn.hasDerivAt_deriv {j : Jet2} {s : Set ℝ} {t : ℝ}
    (hj : j.SoundOn s) (hs : s ∈ 𝓝 t) :
    HasDerivAt (deriv j.value) (j.second t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  apply (hj t ht).2.congr_of_eventuallyEq
  filter_upwards [hs] with u hu
  exact (hj u hu).1.deriv

theorem SoundOn.deriv_deriv {j : Jet2} {s : Set ℝ} {t : ℝ}
    (hj : j.SoundOn s) (hs : s ∈ 𝓝 t) :
    deriv (deriv j.value) t = j.second t := (hj.hasDerivAt_deriv hs).deriv

end Jet2
end GeneralCK.Certificates
