import GeneralCK.Certificates.BivariateJetBounds

namespace GeneralCK.Certificates
open Set JetBounds

namespace JetBounds.Interval

noncomputable def magnitude (i : Interval) : ℝ := max |i.lo| |i.hi|

theorem magnitude_nonneg (i : Interval) : 0 ≤ i.magnitude :=
  (abs_nonneg i.lo).trans (le_max_left _ _)

theorem Contains.abs_le_magnitude {i : Interval} {x : ℝ} (hx : i.Contains x) :
    |x| ≤ i.magnitude := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le i.lo).trans hx.1)
  · exact hx.2.trans ((le_abs_self i.hi).trans (le_max_right _ _))

end JetBounds.Interval

namespace BivariateJetEnclosure

/-- Contract coordinate gradient and Hessian bounds only at the final step. -/
noncomputable def taylorLower (center whole : BivariateJetEnclosure) (ra rz : ℝ) : ℝ :=
  center.value.lo-center.firstA.magnitude*ra-center.firstZ.magnitude*rz-
    (whole.secondAA.magnitude*ra^2+2*whole.secondAZ.magnitude*ra*rz+
      whole.secondZZ.magnitude*rz^2)/2

theorem taylor_lower {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz) :
    taylorLower center whole ra rz≤j.value 1 := by
  have hA := hc.2.1.abs_le_magnitude
  have hZ := hc.2.2.1.abs_le_magnitude
  have hAterm : |j.firstA 0*da|≤center.firstA.magnitude*ra := by
    rw [abs_mul]
    exact mul_le_mul hA hda (abs_nonneg _) center.firstA.magnitude_nonneg
  have hZterm : |j.firstZ 0*dz|≤center.firstZ.magnitude*rz := by
    rw [abs_mul]
    exact mul_le_mul hZ hdz (abs_nonneg _) center.firstZ.magnitude_nonneg
  have hslope : -(center.firstA.magnitude*ra+center.firstZ.magnitude*rz)≤
      (j.projection da dz).first 0 := by
    have h := (abs_add_le (j.firstA 0*da) (j.firstZ 0*dz)).trans (add_le_add hAterm hZterm)
    exact (abs_le.mp h).1
  exact taylor_rectangle_lower
    (fun t ht => (hs t ht).1)
    (fun t ht => (hs t ⟨ht.1.le,ht.2.le⟩).2)
    hc.1.1 hslope hra hrz hda hdz
    whole.secondAA.magnitude_nonneg whole.secondAZ.magnitude_nonneg whole.secondZZ.magnitude_nonneg
    (fun _ _ => rfl)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.2.abs_le_magnitude)

theorem value_pos_of_taylor {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (hcheck : 0<taylorLower center whole ra rz) : 0<j.value 1 :=
  hcheck.trans_le (taylor_lower hs hc hw hra hrz hda hdz)

end BivariateJetEnclosure
end GeneralCK.Certificates
