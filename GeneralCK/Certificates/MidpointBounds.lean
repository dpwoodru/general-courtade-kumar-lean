import GeneralCK.Certificates.TaylorBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace GeneralCK.Certificates
open Set

/-- An upper second derivative bound gives an upper Taylor polynomial on
either side of the center. No nonnegativity hypothesis on M is needed. -/
theorem taylor_upper_on_interval {f df ddf : ℝ → ℝ} {l u m s M : ℝ}
    (hm : m ∈ Icc l u) (hs : s ∈ Icc l u)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (df x) x)
    (hdd : ∀ x ∈ Icc l u, HasDerivAt df (ddf x) x)
    (hM : ∀ x ∈ Icc l u, ddf x ≤ M) :
    f s ≤ f m+df m*(s-m)+M*(s-m)^2/2 := by
  let x : ℝ → ℝ := fun t => m+t*(s-m)
  have hx : ∀ t ∈ Icc (0:ℝ) 1, x t ∈ Icc l u := by
    intro t ht
    dsimp [x]
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hs.1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hm.1),
      mul_nonneg ht.1 (sub_nonneg.mpr hs.2),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hm.2)]
  have hxd (t : ℝ) : HasDerivAt x (s-m) t := by
    convert! ((hasDerivAt_id t).mul_const (s-m)).const_add m using 1 <;> ring
  have h := taylor_lower_of_second_bound
    (f := fun t => -f (x t)) (df := fun t => -(df (x t)*(s-m)))
    (ddf := fun t => -(ddf (x t)*(s-m)^2)) (M := M*(s-m)^2)
    (fun t ht => ((hd (x t) (hx t ht)).comp t (hxd t)).neg)
    (fun t ht => by
      convert! (((hdd (x t) (hx t ⟨ht.1.le,ht.2.le⟩)).comp t (hxd t)).mul_const (s-m)).neg using 1
      ring)
    (fun t ht => by
      have hh := mul_le_mul_of_nonneg_right (hM (x t) (hx t ⟨ht.1.le,ht.2.le⟩)) (sq_nonneg (s-m))
      linarith)
  dsimp [x] at h
  simp only [zero_mul,add_zero,one_mul,add_sub_cancel] at h
  linarith

/-- Integrating a quadratic majorant by the mean value theorem cancels its
linear term exactly at the midpoint. This theorem does not use numerical integration. -/
theorem difference_le_midpoint_quadratic {V P : ℝ → ℝ} {l u p0 p1 M : ℝ}
    (hlu : l<u) (hd : ∀ s ∈ Icc l u, HasDerivAt V (P s) s)
    (hP : ∀ s ∈ Ioo l u, P s ≤ p0+p1*(s-(l+u)/2)+M*(s-(l+u)/2)^2/2) :
    V u-V l ≤ p0*(u-l)+M*(u-l)^3/24 := by
  let Q : ℝ → ℝ := fun s => p0*s+p1*(s-(l+u)/2)^2/2+M*(s-(l+u)/2)^3/6
  let dQ : ℝ → ℝ := fun s => p0+p1*(s-(l+u)/2)+M*(s-(l+u)/2)^2/2
  have hQ (s : ℝ) : HasDerivAt Q (dQ s) s := by
    have hshift := (hasDerivAt_id s).sub_const ((l+u)/2)
    convert! (((hasDerivAt_id s).const_mul p0).add
      ((hshift.pow 2).const_mul p1 |>.div_const 2)).add
      ((hshift.pow 3).const_mul M |>.div_const 6) using 1 <;> dsimp [Q,dQ] <;> ring
  have hD : ∀ s ∈ Icc l u, HasDerivAt (fun s => V s-Q s) (P s-dQ s) s :=
    fun s hs => (hd s hs).sub (hQ s)
  obtain ⟨s,hs,heq⟩ := exists_hasDerivAt_eq_slope (fun s => V s-Q s)
    (fun s => P s-dQ s) hlu
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => hD s ⟨hs.1.le,hs.2.le⟩)
  have hle : P s-dQ s ≤ 0 := sub_nonpos.mpr (hP s hs)
  rw [heq] at hle
  have hdelta := (div_le_iff₀ (sub_pos.mpr hlu)).mp hle
  have hpoly : Q u-Q l=p0*(u-l)+M*(u-l)^3/24 := by dsimp [Q]; ring
  linarith

/-- A midpoint value and uniform second derivative bound control an
antiderivative difference; the midpoint slope needs no interval enclosure. -/
theorem difference_le_midpoint_second_bound {V P dP ddP : ℝ → ℝ} {l u p0 M : ℝ}
    (hlu : l<u) (hd : ∀ s ∈ Icc l u, HasDerivAt V (P s) s)
    (hP : ∀ s ∈ Icc l u, HasDerivAt P (dP s) s)
    (hPP : ∀ s ∈ Icc l u, HasDerivAt dP (ddP s) s)
    (hvalue : P ((l+u)/2) ≤ p0) (hM : ∀ s ∈ Icc l u, ddP s ≤ M) :
    V u-V l ≤ p0*(u-l)+M*(u-l)^3/24 := by
  apply difference_le_midpoint_quadratic hlu hd (p1 := dP ((l+u)/2))
  intro s hs
  have ht := taylor_upper_on_interval (by constructor <;> linarith : (l+u)/2 ∈ Icc l u)
    ⟨hs.1.le,hs.2.le⟩ hP hPP hM
  linarith

end GeneralCK.Certificates
