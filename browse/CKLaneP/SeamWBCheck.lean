/-
Lane P — the value-form seam cell checker for case B (WB): `1 ≤ t0 < t1 ≤ 2` (`q ≥ S/2`).

Base point `y_lo = 2q − S`: `s(y_lo) = cPG(S − q, q)` (`seamCurve_ylo`), right fiber from `p` to `S − q`
(`rightFiber_affine`, derivative bound `c1v − (12/E)(q − x)` as in `wcheckA`), `DC ≥ DCb`, no bulk;
dip `M (y* − y_lo)²/(2E) ≤ M·Yv²/(2E_lo)` (`seam_dip_M`, `Yv` the stationary-point bound).
Needed near `t = 1⁺` for `p ≳ 3.4e-5`, where the stationary point sits just below the top of the
domain (vacuity fails) and the normalized N-B form is too lossy.
-/
import CKLaneP.SeamWCheck

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

namespace WCell

def LBlo (c : WCell) : ℚ := (2 - c.t1) * (Sq / 2 - c.p1)
def RB (c : WCell) : ℚ := max 0 (c.c1v * c.LBlo - 6 / c.EL * c.bhi ^ 2)

end WCell

/-- The Boolean check of a WB-cell (case B, value form). -/
def wcheckB (c : WCell) : Bool := decide (
  VD.okDy 60 c.np0 = true ∧ VD.okDy 60 c.np1 = true ∧ VD.okDy 60 c.nql = true ∧
  VD.okDy 60 c.nq = true ∧ VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nva = true ∧
  VD.okDy 60 c.nxb = true ∧ VD.okDy 60 c.nx2 = true ∧
  dyq c.np0 ≤ c.p0 ∧ c.p1 ≤ dyq c.np1 ∧ 0 < c.p0 ∧ c.p0 < c.p1 ∧ c.p1 ≤ Sq / 2 ∧
  1 ≤ c.t0 ∧ c.t0 < c.t1 ∧ c.t1 ≤ 2 ∧
  dyq c.nql ≤ c.p0 + c.blo ∧ c.p1 + c.bhi ≤ c.qd ∧ c.qd ≤ 1 / 10000 ∧
  0 < (dy c.np0).a1 + (dy c.np0).a2 ∧ 0 < c.eL ∧ 0 < c.fL ∧ 0 < c.Jq ∧ c.eH ≤ c.fL ∧
  dyq c.nvb ≤ 1 / 10000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Xmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Xmin * (dy c.nvb).Hlo ∧
  0 < c.Vmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Vmin * (dy c.nvb).Hlo ∧
  2 * c.Wmax * (dy c.nva).Hhi ≤ 1 - 2 * (dy c.nva).v ∧ 1 < (dy c.nva).b1 ∧
  0 < c.xb ∧ (dy c.nxb).v < 1 / 2 ∧ 1 - 2 * (dy c.nxb).v ≤ 2 * c.xb * (dy c.nxb).Hlo ∧
  2 * c.xb * (dy c.nx2).Hhi ≤ 1 - 2 * (dy c.nx2).v ∧ 0 < (dy dhN).kapLo ∧ 0 ≤ c.M ∧
  0 ≤ c.Pmin ∧ c.Pmin ≤ c.Pmax ∧
  1 ≤ ⌊(1 + c.fL / c.eH) / 2 * 2 ^ 60⌋₊ ∧ 1 ≤ ⌊(1 + c.kh) ^ 2 / (4 * c.kh) * 2 ^ 60⌋₊ ∧
  1 ≤ ⌊(c.p0 + c.blo) / c.p1 * 2 ^ 60⌋₊ ∧ 1 ≤ ⌊(c.p1 + c.p0 + c.blo) / (2 * c.p1) * 2 ^ 60⌋₊ ∧
  c.A0v + c.lam * (Sq - 2 * c.p0) < c.thb ∧ c.lam * c.EH < c.thb / c.xb ∧
  0 ≤ c.DCb + c.RB - c.M * c.Yv ^ 2 / (2 * c.EL))

set_option maxHeartbeats 4000000 in
theorem wcheckB_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : WCell)
    (hc : wcheckB c = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hys0B : 2 * q - 1 / 10000 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    0 ≤ seamCurve (1 / 10000) (H p) (H q) ys := by
  unfold wcheckB at hc
  obtain ⟨ok0, ok1, okql, okq, okvb, okva, okxb, okx2, hnp0, hnp1, hp0pos, hp01, hp1S,
    ht0pos, ht01, ht1le, hql, hqhi, hqd, ha12, heL, hfL, hJq, hkh1, hvb, hvba1, hXmin, hbrX,
    hVmin, hbrV, hbrW, hvab1, hxb, hxbv, hbrxb, hbrx2, hdhk, hM0, hPmin0, hPminmax, hfl1, hfl2,
    hflA, hflC, hneed, hden, hfinal⟩ := of_decide_eq_true hc
  have d0 := dy_sound ok0
  have d1 := dy_sound ok1
  have dql := dy_sound okql
  have dq := dy_sound okq
  have dvb := dy_sound okvb
  have dva := dy_sound okva
  have dxb := dy_sound okxb
  have dx2 := dy_sound okx2
  have dh := dy_sound dh_ok
  -- domain
  have hp0R : (0 : ℝ) < ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp0pos
  have hp : 0 < p := lt_of_lt_of_le hp0R hp0
  have hp1SR : ((c.p1 : ℚ) : ℝ) ≤ 1 / 10000 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1S
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have ht0one : (1 : ℝ) ≤ ((c.t0 : ℚ) : ℝ) := by exact_mod_cast ht0pos
  have ht0R : (0 : ℝ) < ((c.t0 : ℚ) : ℝ) := by linarith
  have ht1R : ((c.t1 : ℚ) : ℝ) ≤ 2 := by exact_mod_cast ht1le
  have ht1nn : (0 : ℝ) ≤ ((c.t1 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ c.t1 := le_trans (le_trans zero_le_one ht0pos) ht01.le
    exact_mod_cast this
  have hpqS : p + q < 1 / 10000 := by linarith
  have hε : 0 < 1 / 10000 / 2 - p := by
    by_contra hcon
    push Not at hcon
    have hpe : p = 1 / 10000 / 2 := le_antisymm (le_trans hp1 hp1SR) (by linarith)
    have h0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) = 0 := by rw [hpe, sub_self, mul_zero]
    linarith
  have hβlo : ((c.blo : ℚ) : ℝ) ≤ q - p := by
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_left (by linarith) ht0R.le) ht0
  have hblo0 : (0 : ℝ) ≤ ((c.blo : ℚ) : ℝ) := by
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    rw [e]; exact mul_nonneg ht0R.le (by linarith)
  have hβ0 : 0 < q - p := by
    have := mul_pos ht0R hε
    linarith
  have hbhi : q - p ≤ ((c.bhi : ℚ) : ℝ) := by
    have e : ((c.bhi : ℚ) : ℝ) = ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) := by
      unfold WCell.bhi; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans ht1 (mul_le_mul_of_nonneg_left (by linarith) ht1nn)
  have hpq : p < q := by linarith
  have hqSB : 1 / 10000 / 2 ≤ q := by
    have h1 := mul_le_mul_of_nonneg_right ht0one hε.le
    rw [one_mul] at h1
    linarith
  have hys0 : 0 < ys := by linarith
  have hqhiR : ((c.p1 : ℚ) : ℝ) + ((c.bhi : ℚ) : ℝ) ≤ ((c.qd : ℚ) : ℝ) := by exact_mod_cast hqhi
  have hqqd : q ≤ ((c.qd : ℚ) : ℝ) := by linarith
  have hqdR : ((c.qd : ℚ) : ℝ) ≤ 1 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hqd
    rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at this
    exact this
  have hqlR : ((dy c.nql).v : ℝ) ≤ q := by
    rw [dy_v]
    have h := (Rat.cast_le (K := ℝ)).mpr hql
    push_cast at h
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    have h2 : ((dyq c.nql : ℚ) : ℝ) ≤ ((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hql
      exact_mod_cast this
    linarith
  have hq0 : 0 < q := by linarith
  -- entropy data
  have hv0 : ((dy c.np0).v : ℝ) ≤ (c.p0 : ℝ) := by rw [dy_v]; exact_mod_cast hnp0
  have hv1 : (c.p1 : ℝ) ≤ ((dy c.np1).v : ℝ) := by rw [dy_v]; exact_mod_cast hnp1
  have hvq : ((dy c.nq).v : ℝ) = (c.qd : ℝ) := by rw [dy_v]; rfl
  have hv00 : (0 : ℝ) < ((dy c.np0).v : ℝ) := by exact_mod_cast d0.1
  have hvl0 : (0 : ℝ) < ((dy c.nql).v : ℝ) := by exact_mod_cast dql.1
  have hv1h : ((dy c.np1).v : ℝ) ≤ 1 / 2 := VD.cast_le_half d1.2.1
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  have heLR : ((c.eL : ℚ) : ℝ) ≤ H p :=
    le_trans (VD.Hlo_le d0) (hHmono hv00.le (hv0.trans hp0) (by linarith))
  have heHR : H p ≤ ((c.eH : ℚ) : ℝ) :=
    le_trans (hHmono hp.le (hp1.trans hv1) hv1h) (VD.le_Hhi d1)
  have hfLR : ((c.fL : ℚ) : ℝ) ≤ H q :=
    le_trans (VD.Hlo_le dql) (hHmono hvl0.le hqlR (by linarith))
  have hfHR : H q ≤ ((c.fH : ℚ) : ℝ) := by
    have h := VD.le_Hhi dq
    rw [hvq] at h
    exact le_trans (hHmono hq0.le hqqd (by linarith)) h
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le (by linarith)
  have hJqR : ((c.Jq : ℚ) : ℝ) ≤ J q := by
    have h := VD.Jlo_le dq
    rw [hvq] at h
    exact le_trans h (J_antitone hq0 (by linarith) hqqd)
  have hrsR : radialSlope p ≤ ((c.rs0 : ℚ) : ℝ) :=
    le_trans (ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hv00, by linarith⟩
      ⟨hp, by linarith⟩ (hv0.trans hp0)) (VD.le_Shi d0 ha12)
  have heL0 : (0 : ℝ) < ((c.eL : ℚ) : ℝ) := by exact_mod_cast heL
  have hfL0 : (0 : ℝ) < ((c.fL : ℚ) : ℝ) := by exact_mod_cast hfL
  have hJq0 : (0 : ℝ) < ((c.Jq : ℚ) : ℝ) := by exact_mod_cast hJq
  have hHp : 0 < H p := lt_of_lt_of_le heL0 heLR
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have eEL : ((c.EL : ℚ) : ℝ) = ((c.eL : ℚ) : ℝ) + ((c.fL : ℚ) : ℝ) := by
    unfold WCell.EL; push_cast; ring
  have eEH : ((c.EH : ℚ) : ℝ) = ((c.eH : ℚ) : ℝ) + ((c.fH : ℚ) : ℝ) := by
    unfold WCell.EH; push_cast; ring
  have hELR : ((c.EL : ℚ) : ℝ) ≤ H p + H q := by rw [eEL]; linarith
  have hEHR : H p + H q ≤ ((c.EH : ℚ) : ℝ) := by rw [eEH]; linarith
  have hEL0 : (0 : ℝ) < ((c.EL : ℚ) : ℝ) := by rw [eEL]; linarith
  have hEH0 : (0 : ℝ) < ((c.EH : ℚ) : ℝ) := lt_of_lt_of_le hE hEHR
  -- profile brackets
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact le_trans hvb (by norm_num)
  have hPmaxAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    exact PmaxQ_sound dvb hvbv hvba1 (radialContact_pos (by linarith) one_pos)
      (contact_le_of_bracket dvb hXmin hbrX hx)
  have hPminAll : ∀ x : ℝ, ((c.Vmin : ℚ) : ℝ) ≤ x → x ≤ ((c.Wmax : ℚ) : ℝ) →
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx1 hx2
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hVmin) hx1
    exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hx2)
      (contact_le_of_bracket dvb hVmin hbrV hx1)
  have hPminAllX : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → x ≤ ((c.Wmax : ℚ) : ℝ) →
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx1 hx2
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx1
    exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hx2)
      (contact_le_of_bracket dvb hXmin hbrX hx1)
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) := by exact_mod_cast hPmin0
  have hPminmaxR : ((c.Pmin : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by exact_mod_cast hPminmax
  have hPmax0R : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := le_trans hPmin0R hPminmaxR
  have eXmin : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) /
      (2 * ((c.fH : ℚ) : ℝ)) := by
    unfold WCell.Xmin; push_cast; rw [Sq_cast]
  have eVmin : ((c.Vmin : ℚ) : ℝ) = (1 - 2 * ((c.qd : ℚ) : ℝ)) / ((c.EH : ℚ) : ℝ) := by
    unfold WCell.Vmin; push_cast; ring
  have eWmax : ((c.Wmax : ℚ) : ℝ) = 1 / (2 * ((c.eL : ℚ) : ℝ)) := by
    unfold WCell.Wmax; push_cast; ring
  have hA0 : (0 : ℝ) ≤ 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  -- (DC)
  have hDC : ((c.DC0 : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    unfold WCell.DC0
    rcases le_total c.DCraw 0 with hneg | hpos
    · rw [max_eq_left hneg, mul_zero]
      have h := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints hdouble hp hpq.le
        (by linarith : q ≤ 1 / 2)
      push_cast
      linarith
    · rw [max_eq_right hpos]
      have h := dc_cell_lower (p0 := ((c.p0 : ℚ) : ℝ)) (p1 := ((c.p1 : ℚ) : ℝ))
        (βhi := ((c.bhi : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (rs0 := ((c.rs0 : ℚ) : ℝ))
        (l2hi := ((L2hiD : ℚ) : ℝ)) (l2lo := ((L2loD : ℚ) : ℝ)) hp0R hp0 hp1 hpq
        (by linarith) hbhi hJqR hJq0 hrsR log2D_bounds.2 log2D_bounds.1 VD.L2lo_pos
      have hraw : (0 : ℝ) ≤ ((c.DCraw : ℚ) : ℝ) := by exact_mod_cast hpos
      have eraw : ((c.DCraw : ℚ) : ℝ) = 1 / (((c.p1 : ℚ) : ℝ) * (2 + ((c.bhi : ℚ) : ℝ) /
          ((c.p0 : ℚ) : ℝ)) * ((L2hiD : ℚ) : ℝ)) - ((c.rs0 : ℚ) : ℝ) / (4 * ((L2loD : ℚ) : ℝ) *
          (((c.p0 : ℚ) : ℝ) * (1 - ((c.p0 : ℚ) : ℝ))) * ((c.Jq : ℚ) : ℝ)) := by
        unfold WCell.DCraw; push_cast; ring
      rw [← eraw] at h
      have hb2 : ((c.blo : ℚ) : ℝ) ^ 2 ≤ (q - p) ^ 2 := pow_le_pow_left₀ hblo0 hβlo 2
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hb2 hraw]
  -- (DC, sharp defect form)
  have hDC2 : ((c.DC2 : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    have hqd12 : ((c.qd : ℚ) : ℝ) < 1 / 2 := by linarith
    have hLA : ((logDnQ ((c.p0 + c.blo) / c.p1) : ℚ) : ℝ) ≤
        Real.log ((((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ)) / ((c.p1 : ℚ) : ℝ)) := by
      have h := logDnQ_sound hflA
      push_cast at h
      exact h
    have hLB : Real.log (2 * ((c.qd : ℚ) : ℝ) / (((c.qd : ℚ) : ℝ) + ((c.p0 : ℚ) : ℝ))) ≤
        ((logUpQ (2 * c.qd / (c.qd + c.p0)) : ℚ) : ℝ) := by
      have hpos : (0 : ℚ) < 2 * c.qd / (c.qd + c.p0) := by
        have : (0 : ℚ) < c.qd := by
          have : (0 : ℝ) < ((c.qd : ℚ) : ℝ) := by linarith
          exact_mod_cast this
        positivity
      have h := logUpQ_sound hpos
      push_cast at h
      exact h
    have hLC : ((logDnQ ((c.p1 + c.p0 + c.blo) / (2 * c.p1)) : ℚ) : ℝ) ≤
        Real.log ((((c.p1 : ℚ) : ℝ) + ((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ)) / (2 * ((c.p1 : ℚ) : ℝ))) := by
      have h := logDnQ_sound hflC
      push_cast at h
      exact h
    have h := dc_cell_lower2 (p0 := ((c.p0 : ℚ) : ℝ)) (p1 := ((c.p1 : ℚ) : ℝ))
      (blo := ((c.blo : ℚ) : ℝ)) (bhi := ((c.bhi : ℚ) : ℝ)) (qd := ((c.qd : ℚ) : ℝ))
      (rs0 := ((c.rs0 : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (l2hi := ((L2hiD : ℚ) : ℝ))
      (l2lo := ((L2loD : ℚ) : ℝ)) hp0R hp0 hp1 hpq hqqd hqd12 hblo0 hβlo hbhi hJqR hJq0 hrsR
      log2D_bounds.2 log2D_bounds.1 VD.L2lo_pos hLA hLB hLC
    have e : ((c.DC2 : ℚ) : ℝ) = ((c.blo : ℚ) : ℝ) * max 0 ((logDnQ ((c.p0 + c.blo) / c.p1) : ℚ) : ℝ) /
        (2 * ((L2hiD : ℚ) : ℝ)) - 2 * ((c.rs0 : ℚ) : ℝ) * (((((c.qd : ℚ) : ℝ) *
        ((logUpQ (2 * c.qd / (c.qd + c.p0)) : ℚ) : ℝ) / 2 - ((c.p0 : ℚ) : ℝ) *
        max 0 ((logDnQ ((c.p1 + c.p0 + c.blo) / (2 * c.p1)) : ℚ) : ℝ) / 2) +
        ((c.bhi : ℚ) : ℝ) ^ 2 / (4 * (1 - ((c.qd : ℚ) : ℝ)))) / ((L2loD : ℚ) : ℝ)) / ((c.Jq : ℚ) : ℝ) := by
      unfold WCell.DC2; push_cast; ring
    rw [e]; exact h
  have hDCb : ((c.DCb : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    unfold WCell.DCb; push_cast; exact max_le hDC hDC2
  -- (R)
  have hc1v : ∀ t ∈ Ioo p q, ((c.c1v : ℚ) : ℝ) - 12 / ((c.EL : ℚ) : ℝ) * (q - t) ≤
      rightD q (H p) (H q) t := by
    intro t ht
    have h := rightD_ge hp ht.1.le ht.2 (by linarith) hPmin0R
      (fun x hx => hPminAll x
        (by rw [eVmin]; exact le_trans (vmin_le_of (by linarith) hE hEHR (by linarith [ht.2])) hx.1)
        (by rw [eWmax]; exact le_trans hx.2 (w_le_wmax_of (by linarith [ht.1]) heL0 heLR)))
    have hlogv : ((logDnQ ((1 + c.fL / c.eH) / 2) : ℚ) : ℝ) ≤ Real.log ((H p + H q) / (2 * H p)) := by
      have h1 := logDnQ_sound hfl1
      refine le_trans h1 (Real.log_le_log ?_ ?_)
      · have : (0 : ℚ) < (1 + c.fL / c.eH) / 2 := by
          have : (0 : ℚ) < c.eH := lt_of_lt_of_le heL (by
            have := (Rat.cast_le (K := ℝ)).mp (le_trans heLR heHR); exact this)
          positivity
        exact_mod_cast this
      · push_cast
        have heH0 : (0 : ℝ) < ((c.eH : ℚ) : ℝ) := lt_of_lt_of_le hHp heHR
        have h2 : ((c.fL : ℚ) : ℝ) / ((c.eH : ℚ) : ℝ) ≤ H q / H p := by
          rw [div_le_div_iff₀ heH0 hHp]
          exact mul_le_mul hfLR heHR hHp.le (by linarith)
        have e3 : (H p + H q) / (2 * H p) = (1 + H q / H p) / 2 := by field_simp
        rw [e3]
        linarith
    have ec : ((c.c1v : ℚ) : ℝ) = ((c.Pmin : ℚ) : ℝ) * ((logDnQ ((1 + c.fL / c.eH) / 2) : ℚ) : ℝ) := by
      unfold WCell.c1v; push_cast; ring
    rw [ec]
    have h3 : 12 * ((q - t) / (H p + H q)) ≤ 12 / ((c.EL : ℚ) : ℝ) * (q - t) := by
      rw [mul_div_assoc', div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by nlinarith [ht.2]) hEL0 hELR
    have h4 := mul_le_mul_of_nonneg_left hlogv hPmin0R
    linarith
  -- (R, case B): right fiber from p to S − q
  have hSq_le : 1 / 10000 - q ≤ q := by linarith
  have hp_le : p ≤ 1 / 10000 - q := by linarith
  have hRB : ((c.RB : ℚ) : ℝ) ≤ canonicalPureGap (1 / 10000 - q) q (H p) (H q) -
      canonicalPureGap p q (H p) (H q) := by
    have hmono := rightFiber_mono (a := p) (x0 := 1 / 10000 - q) (b := q) hp hp_le hSq_le
      (le_trans hqqd hqdR)
    unfold WCell.RB
    rcases le_total (c.c1v * c.LBlo - 6 / c.EL * c.bhi ^ 2) 0 with hneg | hpos
    · rw [max_eq_left hneg]
      push_cast
      linarith
    · rw [max_eq_right hpos]
      have hLB0 : (0 : ℚ) ≤ c.LBlo := by
        unfold WCell.LBlo
        exact mul_nonneg (by linarith) (by linarith)
      have hbhiQ : (0 : ℚ) < c.bhi := by
        have : (0 : ℝ) < ((c.bhi : ℚ) : ℝ) := by linarith
        exact_mod_cast this
      have hELQ : (0 : ℚ) < c.EL := by exact_mod_cast hEL0
      have hc1vQ : (0 : ℚ) ≤ c.c1v := by
        by_contra h
        push Not at h
        have h1 : c.c1v * c.LBlo ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hLB0
        have h2 : (0 : ℚ) < 6 / c.EL * c.bhi ^ 2 := by positivity
        linarith
      have hc1v0 : (0 : ℝ) ≤ ((c.c1v : ℚ) : ℝ) := by exact_mod_cast hc1vQ
      have eLB : ((c.LBlo : ℚ) : ℝ) = (2 - ((c.t1 : ℚ) : ℝ)) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
        unfold WCell.LBlo; push_cast; rw [Sq_cast]
      have hLBle : ((c.LBlo : ℚ) : ℝ) ≤ 1 / 10000 - q - p := by
        rw [eLB]
        have h2 : (2 - ((c.t1 : ℚ) : ℝ)) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) ≤
            (2 - ((c.t1 : ℚ) : ℝ)) * (1 / 10000 / 2 - p) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith [ht1, h2]
      have hsq : (q - p) ^ 2 - (q - (1 / 10000 - q)) ^ 2 ≤ ((c.bhi : ℚ) : ℝ) ^ 2 := by
        have h1 : (q - p) ^ 2 ≤ ((c.bhi : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hbhi 2
        nlinarith [sq_nonneg (q - (1 / 10000 - q))]
      have hcomb : ((c.c1v : ℚ) : ℝ) * ((c.LBlo : ℚ) : ℝ) - 6 / ((c.EL : ℚ) : ℝ) * ((c.bhi : ℚ) : ℝ) ^ 2 ≤
          ((c.c1v : ℚ) : ℝ) * (1 / 10000 - q - p) -
            12 / ((c.EL : ℚ) : ℝ) * ((q - p) ^ 2 - (q - (1 / 10000 - q)) ^ 2) / 2 := by
        have h1 := mul_le_mul_of_nonneg_left hLBle hc1v0
        have h6 : (0 : ℝ) ≤ 6 / ((c.EL : ℚ) : ℝ) := by positivity
        have h2 := mul_le_mul_of_nonneg_left hsq h6
        have e : 12 / ((c.EL : ℚ) : ℝ) * ((q - p) ^ 2 - (q - (1 / 10000 - q)) ^ 2) / 2 =
            6 / ((c.EL : ℚ) : ℝ) * ((q - p) ^ 2 - (q - (1 / 10000 - q)) ^ 2) := by ring
        rw [e]
        linarith
      have haff := rightFiber_affine (a := p) (b := q) (t1 := p) (t2 := 1 / 10000 - q)
        (c1 := ((c.c1v : ℚ) : ℝ)) (c2 := 12 / ((c.EL : ℚ) : ℝ)) hp le_rfl hp_le hSq_le (by linarith)
        (fun t ht => hc1v t ⟨ht.1, by linarith [ht.2]⟩)
      push_cast
      linarith
  -- (dip)
  have hden0 : (0 : ℝ) < 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  have hlamR : ((c.lam : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) := by
    unfold WCell.lam; push_cast; rw [Sq_cast]
  have hlam0 : (0 : ℝ) ≤ ((c.lam : ℚ) : ℝ) := by rw [hlamR]; positivity
  have hfeH : (0 : ℚ) < c.fH / c.eL := by
    have hfH0 : (0 : ℝ) < ((c.fH : ℚ) : ℝ) := lt_of_lt_of_le hHq hfHR
    have : (0 : ℚ) < c.fH := by exact_mod_cast hfH0
    positivity
  have eA : ((c.A0v : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / 2 * ((logUpQ (c.fH / c.eL) : ℚ) : ℝ) := by
    unfold WCell.A0v; push_cast; ring
  have hlogfe : Real.log (H q / H p) ≤ ((logUpQ (c.fH / c.eL) : ℚ) : ℝ) := by
    refine le_trans (Real.log_le_log (div_pos hHq hHp) ?_) (by
      have := logUpQ_sound hfeH
      push_cast at this
      exact this)
    push_cast
    rw [div_le_div_iff₀ hHp heL0]
    exact mul_le_mul hfHR heLR heL0.le (le_trans hHq.le hfHR)
  have hA0v0 : (0 : ℝ) ≤ ((c.A0v : ℚ) : ℝ) := by
    rw [eA]
    have : 0 ≤ Real.log (H q / H p) := Real.log_nonneg (by rw [le_div_iff₀ hHp]; linarith)
    have := le_trans this hlogfe
    positivity
  have hΔ : seamDelta (1 / 10000) (H p) (H q) ys ≤ ((c.A0v : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * ys := by
    have h := seamDelta_le_log (S := 1 / 10000) (y := ys) (P := ((c.Pmax : ℚ) : ℝ)) hHp hHpq
      hys0.le (by linarith) hPmax0R
      (fun t ht => hPmaxAll t (le_trans (by rw [eXmin]; exact xmin_le_of hHq hfHR hA0 (by linarith)) ht.1))
    have hA : ((c.Pmax : ℚ) : ℝ) / 2 * Real.log (H q / H p) ≤ ((c.A0v : ℚ) : ℝ) := by
      rw [eA]; exact mul_le_mul_of_nonneg_left hlogfe (by positivity)
    have hL : ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys)) ≤ ((c.lam : ℚ) : ℝ) * ys := by
      rw [hlamR]
      have h1 : 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) ≤ 1 - 1 / 10000 - ys := by linarith
      have h2 : ys / (1 - 1 / 10000 - ys) ≤ ys / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) :=
        div_le_div_of_nonneg_left hys0.le hden0 h1
      calc ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys))
          ≤ ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 hPmax0R
        _ = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) * ys := by ring
    linarith
  have hxbR : (0 : ℝ) < ((c.xb : ℚ) : ℝ) := by exact_mod_cast hxb
  have hθb : ((c.thb : ℚ) : ℝ) ≤ e8Theta ((c.xb : ℚ) : ℝ) := theta_ge_Slo dxb hxbv hxb le_rfl hbrxb
  have hneedR : ((c.A0v : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) <
      ((c.thb : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hneed
    push_cast at h
    rw [Sq_cast] at h
    exact h
  have hdenR' : ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hden
    push_cast at h
    exact h
  have hdenR : ((c.lam : ℚ) : ℝ) * (H p + H q) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hEHR hlam0
    linarith
  have hyhi : ys ≤ 1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  have hTD : e8Theta (ys / (H p + H q)) = seamDelta (1 / 10000) (H p) (H q) ys := by
    have h := seamD_eq_sub (1 / 10000) (H p) (H q) ys
    rw [hstat] at h
    linarith
  have hyslt : ys / (H p + H q) < ((c.xb : ℚ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 := e8Theta_mono hxbR hcon
    have h2 : ((c.lam : ℚ) : ℝ) * ys ≤ ((c.lam : ℚ) : ℝ) * (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hyhi hlam0
    linarith
  have hxst := xstar_le (S := 1 / 10000) hHp hHq hstat hΔ hys0 hyhi hlam0 hxbR hθb hneedR hdenR
  have hdpos : 0 < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) := by
    linarith
  have hYv : ys ≤ ((c.Yv : ℚ) : ℝ) := by
    have eY : ((c.Yv : ℚ) : ℝ) = ((c.A0v : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) /
        (((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ)) := by
      unfold WCell.Yv; push_cast; ring
    rw [eY]
    exact le_trans hxst (ystar_mono_of (th := ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ))
      (lam := ((c.lam : ℚ) : ℝ)) hA0v0 hE hEHR hlam0 hdpos)
  have hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q)) := by
    intro t ht
    have h := slope_Mof okx2 hdhk hbrx2 (div_pos ht.1 hE)
      (div_le_div_of_nonneg_right ht.2.le hE.le) hyslt.le
    have e : ys / (H p + H q) - t / (H p + H q) = (ys - t) / (H p + H q) := by ring
    rw [e] at h
    exact h
  have hM0R : (0 : ℝ) ≤ ((c.M : ℚ) : ℝ) := by exact_mod_cast hM0
  -- (master, case B)
  have hylo0 : 0 ≤ 2 * q - 1 / 10000 := by linarith
  have hMB : ∀ t ∈ Ioo (2 * q - 1 / 10000) ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q)) := fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩
  have hdip := seam_dip_M (S := 1 / 10000) (by norm_num) hHp hHq hylo0 hys0B (by linarith) hstat hMB
  rw [seamCurve_ylo] at hdip
  have hY2 : (ys - (2 * q - 1 / 10000)) ^ 2 ≤ ((c.Yv : ℚ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hd1 : ((c.M : ℚ) : ℝ) * (ys - (2 * q - 1 / 10000)) ^ 2 / (2 * (H p + H q)) ≤
      ((c.M : ℚ) : ℝ) * ((c.Yv : ℚ) : ℝ) ^ 2 / (2 * (H p + H q)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hY2 hM0R
  have hd2 := dip_mono_of (Y := ((c.Yv : ℚ) : ℝ)) hM0R hEL0 hELR
  have hfinR := (Rat.cast_le (K := ℝ)).mpr hfinal
  push_cast at hfinR
  linarith

end CKLaneP
