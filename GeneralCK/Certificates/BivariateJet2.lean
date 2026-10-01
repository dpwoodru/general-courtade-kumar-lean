import GeneralCK.Certificates.Jet2Composition
import GeneralCK.Certificates.ReflectionTaylor

namespace GeneralCK.Certificates

/-- A symmetric coordinate Hessian, evaluated along a parameterized path.
The component functions alone assert no differentiability; soundness is supplied
by projection to the existing explicit two-derivative `Jet2` contract. -/
structure BivariateJet2 where
  value : ℝ → ℝ
  firstA : ℝ → ℝ
  firstZ : ℝ → ℝ
  secondAA : ℝ → ℝ
  secondAZ : ℝ → ℝ
  secondZZ : ℝ → ℝ

namespace BivariateJet2

def projection (j : BivariateJet2) (da dz : ℝ) : Jet2 :=
  ⟨j.value, fun t => j.firstA t*da+j.firstZ t*dz,
    fun t => j.secondAA t*da^2+2*j.secondAZ t*da*dz+j.secondZZ t*dz^2⟩

def const (c : ℝ) : BivariateJet2 :=
  ⟨fun _ => c,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def coordinateA (a : ℝ → ℝ) : BivariateJet2 :=
  ⟨a,fun _ => 1,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def coordinateZ (z : ℝ → ℝ) : BivariateJet2 :=
  ⟨z,fun _ => 0,fun _ => 1,fun _ => 0,fun _ => 0,fun _ => 0⟩

def affineA (c x : ℝ) : BivariateJet2 := coordinateA (fun t => c+t*(x-c))
def affineZ (c x : ℝ) : BivariateJet2 := coordinateZ (fun t => c+t*(x-c))

def add (j k : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => j.value t+k.value t,
    fun t => j.firstA t+k.firstA t,fun t => j.firstZ t+k.firstZ t,
    fun t => j.secondAA t+k.secondAA t,fun t => j.secondAZ t+k.secondAZ t,
    fun t => j.secondZZ t+k.secondZZ t⟩

def neg (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => -j.value t,fun t => -j.firstA t,fun t => -j.firstZ t,
    fun t => -j.secondAA t,fun t => -j.secondAZ t,fun t => -j.secondZZ t⟩

def mul (j k : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => j.value t*k.value t,
    fun t => j.firstA t*k.value t+j.value t*k.firstA t,
    fun t => j.firstZ t*k.value t+j.value t*k.firstZ t,
    fun t => j.secondAA t*k.value t+2*j.firstA t*k.firstA t+j.value t*k.secondAA t,
    fun t => j.secondAZ t*k.value t+j.firstA t*k.firstZ t+j.firstZ t*k.firstA t+
      j.value t*k.secondAZ t,
    fun t => j.secondZZ t*k.value t+2*j.firstZ t*k.firstZ t+j.value t*k.secondZZ t⟩

noncomputable def inv (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => (j.value t)⁻¹,
    fun t => -j.firstA t/(j.value t)^2,fun t => -j.firstZ t/(j.value t)^2,
    fun t => 2*(j.firstA t)^2/(j.value t)^3-j.secondAA t/(j.value t)^2,
    fun t => 2*j.firstA t*j.firstZ t/(j.value t)^3-j.secondAZ t/(j.value t)^2,
    fun t => 2*(j.firstZ t)^2/(j.value t)^3-j.secondZZ t/(j.value t)^2⟩

noncomputable def log (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => Real.log (j.value t),
    fun t => j.firstA t/j.value t,fun t => j.firstZ t/j.value t,
    fun t => j.secondAA t/j.value t-(j.firstA t)^2/(j.value t)^2,
    fun t => j.secondAZ t/j.value t-j.firstA t*j.firstZ t/(j.value t)^2,
    fun t => j.secondZZ t/j.value t-(j.firstZ t)^2/(j.value t)^2⟩

/-- The ordinary scalar outer chain rule, retaining both coordinates. -/
def outerCompose (outer : Jet2) (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => outer.value (j.value t),
    fun t => outer.first (j.value t)*j.firstA t,
    fun t => outer.first (j.value t)*j.firstZ t,
    fun t => outer.second (j.value t)*(j.firstA t)^2+outer.first (j.value t)*j.secondAA t,
    fun t => outer.second (j.value t)*j.firstA t*j.firstZ t+outer.first (j.value t)*j.secondAZ t,
    fun t => outer.second (j.value t)*(j.firstZ t)^2+outer.first (j.value t)*j.secondZZ t⟩

private theorem jet_ext {j k : Jet2} (hv : j.value=k.value)
    (hf : j.first=k.first) (hs : j.second=k.second) : j=k := by
  cases j; cases k; simp_all

private theorem biv_ext {j k : BivariateJet2} (hv : j.value=k.value)
    (ha : j.firstA=k.firstA) (hz : j.firstZ=k.firstZ)
    (haa : j.secondAA=k.secondAA) (haz : j.secondAZ=k.secondAZ)
    (hzz : j.secondZZ=k.secondZZ) : j=k := by
  cases j; cases k; simp_all

theorem inv_eq_outerCompose (j : BivariateJet2) :
    j.inv=outerCompose Jet2.variableJet.inv j := by
  apply biv_ext <;> funext t <;>
    simp only [inv,outerCompose,Jet2.inv,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

theorem log_eq_outerCompose (j : BivariateJet2) :
    j.log=outerCompose Jet2.variableJet.log j := by
  apply biv_ext <;> funext t <;>
    simp only [log,outerCompose,Jet2.log,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

@[simp] theorem projection_const (c da dz : ℝ) :
    (const c).projection da dz=Jet2.const c := by
  apply jet_ext <;> funext t <;> simp [projection,const,Jet2.const]

@[simp] theorem projection_affineA (c x dz : ℝ) :
    (affineA c x).projection (x-c) dz=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineA,coordinateA,Jet2.segment]

@[simp] theorem projection_affineZ (c x da : ℝ) :
    (affineZ c x).projection da (x-c)=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineZ,coordinateZ,Jet2.segment]

@[simp] theorem projection_add (j k : BivariateJet2) (da dz : ℝ) :
    (j.add k).projection da dz=(j.projection da dz).add (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,add,Jet2.add] <;> ring

@[simp] theorem projection_neg (j : BivariateJet2) (da dz : ℝ) :
    j.neg.projection da dz=(j.projection da dz).neg := by
  apply jet_ext <;> funext t <;> simp only [projection,neg,Jet2.neg] <;> ring

@[simp] theorem projection_mul (j k : BivariateJet2) (da dz : ℝ) :
    (j.mul k).projection da dz=(j.projection da dz).mul (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,mul,Jet2.mul] <;> ring

/-- Algebraic commutation is unconditional, including the totalized zero inverse.
Actual derivative soundness still requires the usual nonzero hypothesis. -/
@[simp] theorem projection_inv (j : BivariateJet2) (da dz : ℝ) :
    j.inv.projection da dz=(j.projection da dz).inv := by
  apply jet_ext <;> funext t <;> simp only [projection,inv,Jet2.inv,div_eq_mul_inv] <;> ring

@[simp] theorem projection_log (j : BivariateJet2) (da dz : ℝ) :
    j.log.projection da dz=(j.projection da dz).log := by
  apply jet_ext <;> funext t <;> simp only [projection,log,Jet2.log,div_eq_mul_inv] <;> ring

@[simp] theorem projection_outerCompose (outer : Jet2) (j : BivariateJet2) (da dz : ℝ) :
    (outerCompose outer j).projection da dz=outer.comp (j.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,outerCompose,Jet2.comp] <;> ring

abbrev DirectionalSoundAt (j : BivariateJet2) (da dz t : ℝ) : Prop :=
  (j.projection da dz).SoundAt t

abbrev DirectionalSoundOn (j : BivariateJet2) (da dz : ℝ) (s : Set ℝ) : Prop :=
  (j.projection da dz).SoundOn s

theorem DirectionalSoundAt.add {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.add k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_add] using Jet2.SoundAt.add hj hk

theorem DirectionalSoundAt.neg {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) : j.neg.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_neg] using Jet2.SoundAt.neg hj

theorem DirectionalSoundAt.mul {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.mul k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_mul] using Jet2.SoundAt.mul hj hk

theorem DirectionalSoundAt.inv {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.inv.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_inv] using Jet2.SoundAt.inv hj hn

theorem DirectionalSoundAt.log {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.log.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_log] using Jet2.SoundAt.log hj hn

theorem DirectionalSoundAt.outerCompose {outer : Jet2} {j : BivariateJet2} {da dz t : ℝ}
    (ho : outer.SoundAt (j.value t)) (hj : j.DirectionalSoundAt da dz t) :
    (outerCompose outer j).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_outerCompose] using ho.comp hj

theorem DirectionalSoundOn.outerCompose {outer : Jet2} {j : BivariateJet2}
    {da dz : ℝ} {s u : Set ℝ} (ho : outer.SoundOn u)
    (hj : j.DirectionalSoundOn da dz s) (hm : Set.MapsTo j.value s u) :
    (outerCompose outer j).DirectionalSoundOn da dz s := by
  simpa only [DirectionalSoundOn,projection_outerCompose] using ho.comp hj hm

theorem soundOn_affineA (c x dz : ℝ) (s : Set ℝ) :
    (affineA c x).DirectionalSoundOn (x-c) dz s := by
  simpa only [DirectionalSoundOn,projection_affineA] using Jet2.soundOn_segment c x s

theorem soundOn_affineZ (c x da : ℝ) (s : Set ℝ) :
    (affineZ c x).DirectionalSoundOn da (x-c) s := by
  simpa only [DirectionalSoundOn,projection_affineZ] using Jet2.soundOn_segment c x s

end BivariateJet2
end GeneralCK.Certificates
