import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GeneralCK.Certificates.Jet2

namespace GeneralCK.Certificates
open Set

/-- A second-derivative enclosure gives a lower Taylor bound along a segment. -/
theorem taylor_lower_of_second_bound {f df ddf : ℝ → ℝ} {M : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ ddf t) :
    f 0+df 0-M/2 ≤ f 1 := by
  let g : ℝ → ℝ := fun t => f t+(M/2)*t^2
  let dg : ℝ → ℝ := fun t => df t+M*t
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (dg t) t := by
    intro t ht
    convert! (hd t ht).add (((hasDerivAt_id t).pow 2).const_mul (M/2)) using 1
    dsimp [dg]
    ring
  have hgg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt dg (ddf t+M) t := by
    intro t ht
    convert! (hdd t ht).add ((hasDerivAt_id t).const_mul M) using 1
    ring
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (f' := dg) (f'' := fun t => ddf t+M)
    · intro t ht
      exact (hg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hgg t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      linarith [hbound t ht]
  have hb := hc.le_slope_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1)
    (hg 0 (by norm_num))
  dsimp [g,dg] at hb
  simp only [slope_def_field,zero_pow (by norm_num : 2 ≠ 0),one_pow,mul_zero,
    add_zero,sub_zero,div_one,mul_one] at hb
  linarith

/-- Certificate form of the one-variable Taylor estimate. -/
theorem taylor_lower_from_enclosures {f df ddf : ℝ → ℝ} {L A M : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hvalue : L ≤ f 0) (hslope : -A ≤ df 0)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ ddf t) :
    L-A-M/2 ≤ f 1 := by
  linarith [taylor_lower_of_second_bound hd hdd hbound]

/-- The bivariate Taylor remainder from componentwise second derivative bounds.
All second derivative bounds must hold throughout the segment. -/
theorem taylor_rectangle_lower {f df ddf haa haz hzz : ℝ → ℝ}
    {L pa pz Maa Maz Mzz ra rz da dz : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hvalue : L ≤ f 0) (hslope : -(pa*ra+pz*rz) ≤ df 0)
    (hra : 0 ≤ ra) (_hrz : 0 ≤ rz) (hda : |da| ≤ ra) (hdz : |dz| ≤ rz)
    (hMaa : 0 ≤ Maa) (hMaz : 0 ≤ Maz) (hMzz : 0 ≤ Mzz)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, ddf t=haa t*da^2+2*haz t*da*dz+hzz t*dz^2)
    (haa_bound : ∀ t ∈ Ioo (0:ℝ) 1, |haa t| ≤ Maa)
    (haz_bound : ∀ t ∈ Ioo (0:ℝ) 1, |haz t| ≤ Maz)
    (hzz_bound : ∀ t ∈ Ioo (0:ℝ) 1, |hzz t| ≤ Mzz) :
    L-pa*ra-pz*rz-(Maa*ra^2+2*Maz*ra*rz+Mzz*rz^2)/2 ≤ f 1 := by
  have hda2 : da^2 ≤ ra^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg da) hda
  have hdz2 : dz^2 ≤ rz^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg dz) hdz
  have hcross : |da*dz| ≤ ra*rz := by
    rw [abs_mul]
    exact mul_le_mul hda hdz (abs_nonneg _) hra
  have hbound : ∀ t ∈ Ioo (0:ℝ) 1,
      -(Maa*ra^2+2*Maz*ra*rz+Mzz*rz^2) ≤ ddf t := by
    intro t ht
    have ha := (abs_le.mp (haa_bound t ht)).1
    have hz := (abs_le.mp (hzz_bound t ht)).1
    have hac := mul_le_mul_of_nonneg_right ha (sq_nonneg da)
    have hzc := mul_le_mul_of_nonneg_right hz (sq_nonneg dz)
    have har := mul_le_mul_of_nonneg_left hda2 hMaa
    have hzr := mul_le_mul_of_nonneg_left hdz2 hMzz
    have hcz : |haz t*(da*dz)| ≤ Maz*(ra*rz) := by
      rw [abs_mul]
      exact mul_le_mul (haz_bound t ht) hcross (abs_nonneg _) hMaz
    have hcl := (abs_le.mp hcz).1
    rw [hsecond t ht]
    nlinarith
  have hh := taylor_lower_from_enclosures hd hdd hvalue hslope hbound
  linarith

/-- An accepted lower Taylor enclosure certifies positivity of a sound jet's value. -/
theorem Jet2.value_pos_of_taylor {j : Jet2} {L A M : ℝ}
    (hj : j.SoundOn (Icc (0:ℝ) 1))
    (hvalue : L ≤ j.value 0) (hslope : -A ≤ j.first 0)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ j.second t)
    (haccept : 0 < L-A-M/2) : 0 < j.value 1 := by
  exact haccept.trans_le (taylor_lower_from_enclosures (fun t ht => (hj t ht).1)
    (fun t ht => (hj t ⟨ht.1.le,ht.2.le⟩).2) hvalue hslope hsecond)

end GeneralCK.Certificates
