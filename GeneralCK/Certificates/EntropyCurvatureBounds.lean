import GeneralCK.EntropyCurvatureDefs
import GeneralCK.Certificates.MixedBounds
import GeneralCK.EtaMonotone

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem xi_log_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    xi v = ((-Real.log v)-(-Real.log (1-v)))/2 := by
  unfold xi J
  rw [Real.log_div (by linarith) hv.ne']
  field_simp [log_two_pos.ne']
  ring

theorem kap_log_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    Mixed.kap v = ((-Real.log v)+(-Real.log (1-v)))/2 := by
  unfold Mixed.kap
  rw [Real.log_mul hv.ne' (by linarith)]
  ring

theorem endpoint_bounds {v a b c d : ℝ} (hv : 0 < v) (hv' : v < 1)
    (ha : a ≤ -Real.log v) (hb : b ≤ -Real.log (1-v))
    (hc : -Real.log v ≤ c) (hd : -Real.log (1-v) ≤ d) :
    (a-d)/2 ≤ xi v ∧ xi v ≤ (c-b)/2 ∧
    (a+b)/2 ≤ Mixed.kap v ∧ Mixed.kap v ≤ (c+d)/2 := by
  rw [xi_log_identity hv hv',kap_log_identity hv hv']
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem xi_antitone {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1/2) (huv : u ≤ v) :
    xi v ≤ xi u := by
  unfold xi
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (J_antitone hu hv huv) log_two_pos.le) (by norm_num)

theorem kap_antitone {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1/2) (huv : u ≤ v) :
    Mixed.kap v ≤ Mixed.kap u := by
  have hp : 0 < u*(1-u) := by
    have hu' : 0 < 1-u := by linarith
    positivity
  have hq : u*(1-u) ≤ v*(1-v) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr huv) (show 0 ≤ 1-u-v by linarith)]
  have hlog := Real.log_le_log hp hq
  unfold Mixed.kap
  linarith

theorem polynomial_bounds {x t B xl xu tl tu Bl Bu : ℝ}
    (hxl : 0 ≤ xl) (htl : 0 ≤ tl) (hBl : 0 ≤ Bl)
    (hx : xl ≤ x) (hx' : x ≤ xu) (ht : tl ≤ t) (ht' : t ≤ tu)
    (hB : Bl ≤ B) (hB' : B ≤ Bu) :
    Bl^3*xl*(1+tl^2)+xl^3*tl^4-Bu^3*tu-2*xu^3*tu^2*Bu ≤ polyP x t B ∧
    4*Bl^3*(1+tl^2)-2*Bu^2*tu^3*xu-8*Bu^2*tu^2-6*Bu^2*tu*xu
      -Bu*tu^5*xu+3*Bl*tl^4+9*Bl*tl^3*xl-3*tu^5*xu ≤ polyR x t B := by
  have hx0 := hxl.trans hx
  have ht0 := htl.trans ht
  have hB0 := hBl.trans hB
  have hxu0 := hx0.trans hx'
  have htu0 := ht0.trans ht'
  have hBu0 := hB0.trans hB'
  constructor
  · calc
      _ ≤ B^3*x*(1+t^2)+x^3*t^4-B^3*t-2*x^3*t^2*B := by gcongr
      _ = _ := by unfold polyP; ring
  · unfold polyR
    gcongr

theorem leaf_sound {l u xl xu Bl Bu v : ℝ}
    (hl : 0 < l) (hu : u ≤ 1/2) (hv : l ≤ v) (hv' : v ≤ u)
    (hxl : 0 ≤ xl) (hBl : 0 ≤ Bl)
    (hxu : xi l ≤ xu) (hxl' : xl ≤ xi u)
    (hBu : Mixed.kap l ≤ Bu) (hBl' : Bl ≤ Mixed.kap u)
    (hP : 0 < Bl^3*xl*(1+(1-2*u)^2)+xl^3*(1-2*u)^4-Bu^3*(1-2*l)-2*xu^3*(1-2*l)^2*Bu)
    (hR : 0 < 4*Bl^3*(1+(1-2*u)^2)-2*Bu^2*(1-2*l)^3*xu-8*Bu^2*(1-2*l)^2
      -6*Bu^2*(1-2*l)*xu-Bu*(1-2*l)^5*xu+3*Bl*(1-2*u)^4+9*Bl*(1-2*u)^3*xl-3*(1-2*l)^5*xu) :
    0 < P v ∧ 0 < R v := by
  have ht := polynomial_bounds hxl (by linarith : 0 ≤ 1-2*u) hBl
    (hxl'.trans (xi_antitone (hl.trans_le hv) hu hv'))
    ((xi_antitone hl (hv'.trans hu) hv).trans hxu)
    (by linarith : 1-2*u ≤ 1-2*v) (by linarith : 1-2*v ≤ 1-2*l)
    (hBl'.trans (kap_antitone (hl.trans_le hv) hu hv'))
    ((kap_antitone hl (hv'.trans hu) hv).trans hBu)
  exact ⟨hP.trans_le ht.1,hR.trans_le ht.2⟩

end GeneralCK.Certificates.EntropyCurvature
