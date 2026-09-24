/-
Lane P — the small-scale (T) seam lemma: all `(p, q)` with `q ≤ qT`, in κ-cells `κ = H p/H q`.

Uniform in the scale: `f = H q ≤ fT := Hhi(nqT)`, `E = f(1+κ) ≤ fT(1+κ1)`, contacts of all large
arguments `≤ vb` (`X ≥ (1−2S)/(2fT)`), `Pmin0 = (1−2vb)/((1+vb/2)³ log2⁺)` (no lower bracket).
Base = bulk only (DC ≥ 0 by the owner, right fiber ≥ 0 by `rightFiber_mono`):
    bulk ≥ (S/2 − qT)·max(0, Jv),  Jv = max(9/40 (1−κ1)², Pmin0·log((1+κ1)²/(4κ1)) − (Pmax−Pmin0)·log(2/(1+κ0))).
Kinds: 0 = middle cell (dip ≤ M A0² E_T/(2 D_T²), A0 = (Pmax/2) log(1/κ0));
       1 = last cell `[κ0, 1]` normalized by `(1−κ)²`;
       2 = first cell `(0, κ1]` with the slope-gap dip bound `dip ≤ S·(1 + 1/L_K)/log2⁻`.
-/
import CKLaneP.SeamWBase
import CKLaneP.ThetaLip

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

structure TCell where
  qT : ℚ
  nqT : ℕ
  k0 : ℚ
  k1 : ℚ
  nvb : ℕ
  xb : ℚ
  nxb : ℕ
  nx2 : ℕ
  xK : ℚ
  nxK : ℕ
  nvK : ℕ
deriving Repr

namespace TCell

def fT (c : TCell) : ℚ := (dy c.nqT).Hhi
def ET (c : TCell) : ℚ := c.fT * (1 + c.k1)
def vb (c : TCell) : ℚ := (dy c.nvb).v
def Xmin (c : TCell) : ℚ := (1 - 2 * Sq) / (2 * c.fT)
def Pmax (c : TCell) : ℚ := PmaxQ (dy c.nvb)
def Pmin0 (c : TCell) : ℚ := (1 - 2 * c.vb) / ((1 + c.vb / 2) ^ 3 * L2hiD)
def lam (c : TCell) : ℚ := c.Pmax / (1 - 2 * Sq)
def thb (c : TCell) : ℚ := (dy c.nxb).Slo
def M (c : TCell) : ℚ := Mof c.xb c.nx2
def Jv (c : TCell) : ℚ :=
  max (9 / 40 * (1 - c.k1) ^ 2)
    (c.Pmin0 * logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) - (c.Pmax - c.Pmin0) * logUpQ (2 / (1 + c.k0)))
def B0 (c : TCell) : ℚ := (Sq / 2 - c.qT) * max 0 c.Jv
def A0 (c : TCell) : ℚ := c.Pmax / 2 * logUpQ (1 / c.k0)
def DT (c : TCell) : ℚ := c.thb / c.xb - c.lam * c.ET

end TCell

/-- Conditions shared by all T-cells. -/
def tcommon (c : TCell) : Bool := decide (
  VD.okDy 60 c.nqT = true ∧ VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nxb = true ∧
  VD.okDy 60 c.nx2 = true ∧
  0 < c.qT ∧ c.qT ≤ dyq c.nqT ∧ c.qT < Sq / 2 ∧ 0 < c.fT ∧
  0 ≤ c.k0 ∧ c.k0 < c.k1 ∧ c.k1 ≤ 1 ∧
  dyq c.nvb ≤ 1 / 10000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Xmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Xmin * (dy c.nvb).Hlo ∧
  0 < c.xb ∧ (dy c.nxb).v < 1 / 2 ∧ 1 - 2 * (dy c.nxb).v ≤ 2 * c.xb * (dy c.nxb).Hlo ∧
  2 * c.xb * (dy c.nx2).Hhi ≤ 1 - 2 * (dy c.nx2).v ∧ 0 < (dy dhN).kapLo ∧ 0 ≤ c.M ∧
  0 ≤ c.Pmin0 ∧ c.Pmin0 ≤ c.Pmax ∧ 0 < c.k1 ∧
  1 ≤ ⌊(1 + c.k1) ^ 2 / (4 * c.k1) * 2 ^ 60⌋₊)

/-- T-cell check by kind. -/
def tcheck (kind : ℕ) (c : TCell) : Bool :=
  tcommon c && (match kind with
  | 0 => decide (0 < c.k0 ∧ c.A0 + c.lam * Sq < c.thb ∧ 0 < c.DT ∧
      0 ≤ c.B0 - c.M * c.A0 ^ 2 * c.ET / (2 * c.DT ^ 2))
  | 1 => decide (0 < c.k0 ∧ c.k1 = 1 ∧
      c.Pmax / 2 * ((1 - c.k0) / c.k0) + c.lam * Sq < c.thb ∧ 0 < c.DT ∧
      0 ≤ (Sq / 2 - c.qT) * (9 / 40) - c.M * (c.Pmax / 2 / c.k0) ^ 2 * c.ET / (2 * c.DT ^ 2))
  | _ => decide (VD.okDy 60 c.nxK = true ∧ VD.okDy 60 c.nvK = true ∧ 0 < c.xK ∧
      2 * c.xK * (dy c.nxK).Hhi ≤ 1 - 2 * (dy c.nxK).v ∧ 0 < (dy c.nxK).a1 + (dy c.nxK).a2 ∧
      (dy c.nxK).v < 1 / 2 ∧
      1 ≤ ⌊1 / c.k1 * 2 ^ 60⌋₊ ∧ (dy c.nxK).Shi < c.Pmin0 / 2 * logDnQ (1 / c.k1) ∧
      1 - 2 * (dy c.nvK).v ≤ 2 * c.xK * (dy c.nvK).Hlo ∧ 0 < (dy c.nvK).a1 ∧
      0 ≤ c.B0 - Sq * (1 + 1 / (dy c.nvK).a1) / L2loD))

set_option maxHeartbeats 2000000 in
/-- Real consequences shared by the T-cells. -/
theorem tcell_facts (c : TCell) (hc : tcommon c = true) {p q ys : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p) :
    0 < H p ∧ H p ≤ H q ∧ H p + H q ≤ ((c.ET : ℚ) : ℝ) ∧ q ≤ 1 / 10000 / 2 ∧
    (∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ)) ∧
    (∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → ((c.Pmin0 : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1)) ∧
    ((c.Xmin : ℚ) : ℝ) ≤ (1 - 1 / 10000 - ys) / (2 * H q) ∧
    (∀ m ∈ Icc q (1 / 10000 / 2), ((c.Xmin : ℚ) : ℝ) ≤ (1 - 2 * m) / (2 * H q)) ∧
    radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 ≤ 1 / 10000 ∧
    0 ≤ ((c.Pmin0 : ℚ) : ℝ) ∧ ((c.Pmin0 : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by
  unfold tcommon at hc
  obtain ⟨okT, okvb, okxb, okx2, hqT0, hqTd, hqTS, hfT, hk00, hk01, hk11, hvb, hvba1, hXmin, hbrX,
    -, -, -, -, -, -, hPmin00, hPmm, -, -⟩ := of_decide_eq_true hc
  have dT := dy_sound okT
  have dvb := dy_sound okvb
  have hq0 : 0 < q := hp.trans hpq
  have hqTSR : ((c.qT : ℚ) : ℝ) < 1 / 10000 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have hqS : q ≤ 1 / 10000 / 2 := by linarith
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le (by linarith)
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hqTdR : ((c.qT : ℚ) : ℝ) ≤ ((dy c.nqT).v : ℝ) := by rw [dy_v]; exact_mod_cast hqTd
  have hvTh : ((dy c.nqT).v : ℝ) ≤ 1 / 2 := VD.cast_le_half dT.2.1
  have hfTR : H q ≤ ((c.fT : ℚ) : ℝ) :=
    le_trans (hHmono hq0.le (hqT.trans hqTdR) hvTh) (VD.le_Hhi dT)
  have hk1R : ((c.k1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hk11
  have hET : H p + H q ≤ ((c.ET : ℚ) : ℝ) := by
    have e : ((c.ET : ℚ) : ℝ) = ((c.fT : ℚ) : ℝ) * (1 + ((c.k1 : ℚ) : ℝ)) := by
      unfold TCell.ET; push_cast; ring
    rw [e]
    have h1 : H p ≤ ((c.k1 : ℚ) : ℝ) * H q := by
      rw [div_le_iff₀ hHq] at hk1; linarith
    have h2 : ((c.k1 : ℚ) : ℝ) * H q ≤ ((c.k1 : ℚ) : ℝ) * ((c.fT : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hfTR (by linarith [div_pos hHp hHq])
    nlinarith
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact le_trans hvb (by norm_num)
  have hvbR : ((dy c.nvb).v : ℝ) ≤ 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hvbv
    rw [show ((1 / 1000 : ℚ) : ℝ) = 1 / 1000 by norm_num] at this
    exact this
  have hL4 : (4 : ℝ) ≤ -Real.log ((dy c.nvb).v : ℝ) :=
    le_trans (by exact_mod_cast hvba1) dvb.2.2.1
  have hPmaxAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    exact PmaxQ_sound dvb hvbv hvba1 (radialContact_pos (by linarith) one_pos)
      (contact_le_of_bracket dvb hXmin hbrX hx)
  have hPminAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      ((c.Pmin0 : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    have hcb := contact_le_of_bracket dvb hXmin hbrX hx
    have h := profile_ge_bracket0 (radialContact_pos (by linarith) one_pos) hcb hvbR hL4
    have hl2 := log2D_bounds
    have e : ((c.Pmin0 : ℚ) : ℝ) = (1 - 2 * ((dy c.nvb).v : ℝ)) /
        ((1 + ((dy c.nvb).v : ℝ) / 2) ^ 3 * ((L2hiD : ℚ) : ℝ)) := by
      unfold TCell.Pmin0 TCell.vb; push_cast; ring
    rw [e]
    have hvb0 : (0 : ℝ) < ((dy c.nvb).v : ℝ) := by exact_mod_cast dvb.1
    refine le_trans ?_ h
    apply div_le_div_of_nonneg_left (by linarith) (by have := log_two_pos; positivity)
    exact mul_le_mul_of_nonneg_left hl2.2 (by positivity)
  have eX : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000)) / (2 * ((c.fT : ℚ) : ℝ)) := by
    unfold TCell.Xmin; push_cast; rw [Sq_cast]
  have hXf : ((c.Xmin : ℚ) : ℝ) ≤ (1 - 1 / 10000 - ys) / (2 * H q) := by
    rw [eX]; exact xmin_le_of hHq hfTR (by norm_num) (by linarith)
  have hXm : ∀ m ∈ Icc q (1 / 10000 / 2), ((c.Xmin : ℚ) : ℝ) ≤ (1 - 2 * m) / (2 * H q) := by
    intro m hm
    rw [eX]; exact xmin_le_of hHq hfTR (by norm_num) (by linarith [hm.2])
  have hcX : radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 ≤ 1 / 10000 := by
    have hcb := contact_le_of_bracket dvb hXmin hbrX (le_refl ((c.Xmin : ℚ) : ℝ))
    have : ((dy c.nvb).v : ℝ) ≤ 1 / 10000 := by
      have h' : ((dy c.nvb).v : ℚ) ≤ 1 / 10000 := by rw [dy_v]; exact hvb
      have h2 := (Rat.cast_le (K := ℝ)).mpr h'
      rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at h2
      exact h2
    linarith
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin0 : ℚ) : ℝ) := by exact_mod_cast hPmin00
  have hPmmR : ((c.Pmin0 : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by exact_mod_cast hPmm
  exact ⟨hHp, hHpq, hET, hqS, hPmaxAll, hPminAll, hXf, hXm, hcX, hPmin0R, hPmmR⟩

/-- Bulk lower bound for T-cells: `jdef ≥ max(0, Jv)` on `[q, S/2]`. -/
theorem tcell_bulk (c : TCell) (hc : tcommon c = true) {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ)) :
    ∀ m ∈ Icc q (1 / 10000 / 2), max 0 ((c.Jv : ℚ) : ℝ) ≤ jdef (H p) (H q) m := by
  have hpS : p < 1 / 10000 / 2 := by
    have hc' := hc
    unfold tcommon at hc'
    obtain ⟨-, -, -, -, -, -, hqTS, -⟩ := of_decide_eq_true hc'
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    linarith
  obtain ⟨hHp, hHpq, -, hqS, hPmaxAll, hPminAll, -, hXm, hcX, hPmin0R, hPmmR⟩ :=
    tcell_facts c hc hp hpq hqT hk0 hk1 (ys := (1 / 10000 - 2 * p) / 2) (by linarith) (by linarith)
  have hc' := hc
  unfold tcommon at hc'
  obtain ⟨-, -, -, -, -, -, -, -, hk00, hk01, hk11, -, -, -, -, -, -, -, -, -, -, -, -, hk1pos,
    hfl⟩ := of_decide_eq_true hc'
  intro m hm
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hm12 : m < 1 / 2 := by linarith [hm.2]
  have hZ : 0 < 1 - 2 * m := by linarith
  have hXZ : ∀ x : ℝ, (1 - 2 * m) / (2 * H q) ≤ x → ((c.Xmin : ℚ) : ℝ) ≤ x :=
    fun x hx => le_trans (hXm m hm) hx
  have hcap : radialContact ((1 - 2 * m) / H q) 1 ≤ 1 / 10000 := by
    have e : (1 - 2 * m) / H q = 2 * ((1 - 2 * m) / (2 * H q)) := by field_simp
    rw [e]
    have hmono : radialContact (2 * ((1 - 2 * m) / (2 * H q))) 1 ≤
        radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 := by
      have hX0 : (0 : ℝ) < ((c.Xmin : ℚ) : ℝ) := by
        have hc2 := hc
        unfold tcommon at hc2
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hX, -⟩ := of_decide_eq_true hc2
        exact_mod_cast hX
      apply (radialContact_le_iff_ratio (by positivity) (by positivity) one_pos one_pos).2
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [hXm m hm]
    linarith
  have hjl := jdef_lower hHp hHpq hm12 hcap
  have hj0 : 0 ≤ jdef (H p) (H q) m := le_trans (by positivity) hjl
  set κ := H p / H q with hκd
  have hkpos : 0 < κ := div_pos hHp hHq
  have hk1R : ((c.k1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hk11
  have hj1 : 9 / 40 * (1 - ((c.k1 : ℚ) : ℝ)) ^ 2 ≤ jdef (H p) (H q) m := by
    refine le_trans ?_ hjl
    have e : 9 / 10 * (H q - H p) ^ 2 / (4 * H q ^ 2) = 9 / 40 * (1 - κ) ^ 2 := by
      rw [hκd]; field_simp; ring
    rw [e]
    have h1 : 0 ≤ 1 - ((c.k1 : ℚ) : ℝ) := by linarith
    have h3 := pow_le_pow_left₀ h1 (show 1 - ((c.k1 : ℚ) : ℝ) ≤ 1 - κ by linarith) 2
    linarith
  have hj2 : ((c.Pmin0 : ℚ) : ℝ) * ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) -
      (((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ) ≤
      jdef (H p) (H q) m := by
    have hjg := jdef_ge_log (Pm := ((c.Pmin0 : ℚ) : ℝ)) (PM := ((c.Pmax : ℚ) : ℝ)) hHp hHpq hm12
      (fun x hx => hPminAll x (hXZ x (le_trans (div_le_div_of_nonneg_left hZ.le hE
        (by linarith)) hx.1)))
      (fun x hx => hPmaxAll x (hXZ x hx.1))
    have hE2e : (H p + H q) / (2 * H p) = (1 + κ) / (2 * κ) := by
      rw [hκd]; field_simp; ring
    have h2fE : 2 * H q / (H p + H q) = 2 / (1 + κ) := by
      rw [hκd]; field_simp; ring
    rw [hE2e, h2fE] at hjg
    have hsplit : Real.log ((1 + κ) / (2 * κ)) = Real.log ((1 + κ) ^ 2 / (4 * κ)) +
        Real.log (2 / (1 + κ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    rw [hsplit] at hjg
    have hlog1 : ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) ≤
        Real.log ((1 + κ) ^ 2 / (4 * κ)) := by
      refine le_trans (logDnQ_sound hfl) ?_
      have hk1p : (0 : ℝ) < ((c.k1 : ℚ) : ℝ) := by exact_mod_cast hk1pos
      apply Real.log_le_log (by push_cast; positivity)
      push_cast
      exact kappa_ratio_mono hkpos hk1 hk1R
    have hk0R : (0 : ℝ) ≤ ((c.k0 : ℚ) : ℝ) := by exact_mod_cast hk00
    have hlog2 : Real.log (2 / (1 + κ)) ≤ ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ) := by
      have hpos : (0 : ℚ) < 2 / (1 + c.k0) := by
        have : (0 : ℚ) ≤ c.k0 := hk00
        positivity
      refine le_trans (Real.log_le_log (by positivity) ?_) (by
        have := logUpQ_sound hpos
        push_cast at this
        exact this)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hPd : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog1 hPmin0R, mul_le_mul_of_nonneg_left hlog2 hPd]
  have eJv : ((c.Jv : ℚ) : ℝ) = max (9 / 40 * (1 - ((c.k1 : ℚ) : ℝ)) ^ 2)
      (((c.Pmin0 : ℚ) : ℝ) * ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) -
        (((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ)) := by
    unfold TCell.Jv; push_cast; ring_nf
  rw [eJv]
  exact max_le hj0 (max_le hj1 hj2)

/-- Quadratic bulk bound for T-cells: `9/40 (1 − κ)² ≤ jdef` on `[q, S/2]`. -/
theorem tcell_jdef (c : TCell) (hc : tcommon c = true) {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ)) :
    ∀ m ∈ Icc q (1 / 10000 / 2), 9 / 40 * (1 - H p / H q) ^ 2 ≤ jdef (H p) (H q) m := by
  have hc' := hc
  unfold tcommon at hc'
  obtain ⟨-, -, -, -, -, -, hqTS, -, -, -, -, -, -, hX, -⟩ := of_decide_eq_true hc'
  have hpS : p < 1 / 10000 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    linarith
  obtain ⟨hHp, hHpq, -, hqS, -, -, -, hXm, hcX, -, -⟩ :=
    tcell_facts c hc hp hpq hqT hk0 hk1 (ys := (1 / 10000 - 2 * p) / 2) (by linarith) (by linarith)
  intro m hm
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hm12 : m < 1 / 2 := by linarith [hm.2]
  have hcap : radialContact ((1 - 2 * m) / H q) 1 ≤ 1 / 10000 := by
    have e : (1 - 2 * m) / H q = 2 * ((1 - 2 * m) / (2 * H q)) := by field_simp
    rw [e]
    have hX0 : (0 : ℝ) < ((c.Xmin : ℚ) : ℝ) := by exact_mod_cast hX
    have hmono : radialContact (2 * ((1 - 2 * m) / (2 * H q))) 1 ≤
        radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 := by
      have hZ : 0 < 1 - 2 * m := by linarith
      apply (radialContact_le_iff_ratio (by positivity) (by positivity) one_pos one_pos).2
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [hXm m hm]
    linarith
  have hjl := jdef_lower hHp hHpq hm12 hcap
  have e : 9 / 10 * (H q - H p) ^ 2 / (4 * H q ^ 2) = 9 / 40 * (1 - H p / H q) ^ 2 := by
    field_simp; ring
  linarith

set_option maxHeartbeats 4000000 in
/-- Soundness of the T-cell checks. -/
theorem tcheck_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (kind : ℕ) (c : TCell)
    (hc : tcheck kind c = true) {p q ys : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    0 ≤ seamCurve (1 / 10000) (H p) (H q) ys := by
  unfold tcheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hcom, hkind⟩ := hc
  obtain ⟨hHp, hHpq, hET, hqS, hPmaxAll, hPminAll, hXf, hXm, hcX, hPmin0R, hPmmR⟩ :=
    tcell_facts c hcom hp hpq hqT hk0 hk1 hys0 hysS
  have hbulk := tcell_bulk c hcom hp hpq hqT hk0 hk1
  have hcom' := hcom
  unfold tcommon at hcom'
  obtain ⟨okT, okvb, okxb, okx2, hqT0, hqTd, hqTS, hfT, hk00, hk01, hk11, hvb, hvba1, hXmin, hbrX,
    hxb, hxbv, hbrxb, hbrx2, hdhk, hM0, hPmin00, hPmm, hk1pos, hfl⟩ := of_decide_eq_true hcom'
  have dxb := dy_sound okxb
  have dx2 := dy_sound okx2
  have dh := dy_sound dh_ok
  have dvb := dy_sound okvb
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hq0 : 0 < q := hp.trans hpq
  have hqTSR : ((c.qT : ℚ) : ℝ) < 1 / 10000 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have hPmax0R : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := le_trans hPmin0R hPmmR
  -- base: DC ≥ 0, right fiber ≥ 0, bulk ≥ (S/2 − qT)·max 0 Jv
  have hDC := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints hdouble hp hpq.le
    (by linarith : q ≤ 1 / 2)
  have hRf := rightFiber_mono hp hpq.le le_rfl (by linarith)
  have hB0 : ((c.B0 : ℚ) : ℝ) ≤ emLine (H p) (H q) (1 / 10000 / 2) - emLine (H p) (H q) q := by
    have hmvt := emLine_mvt (ℓ := max 0 ((c.Jv : ℚ) : ℝ)) hHp hHq hqS (by linarith) hbulk
    have eB : ((c.B0 : ℚ) : ℝ) = (1 / 10000 / 2 - ((c.qT : ℚ) : ℝ)) * max 0 ((c.Jv : ℚ) : ℝ) := by
      unfold TCell.B0; push_cast; rw [Sq_cast]
    rw [eB]
    have hℓ0 : (0 : ℝ) ≤ max 0 ((c.Jv : ℚ) : ℝ) := le_max_left _ _
    have := mul_le_mul_of_nonneg_right (show 1 / 10000 / 2 - ((c.qT : ℚ) : ℝ) ≤ 1 / 10000 / 2 - q by
      linarith) hℓ0
    linarith
  have hem : emLine (H p) (H q) q = canonicalPureGap q q (H p) (H q) := rfl
  -- common dip machinery
  have hlamR : ((c.lam : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000)) := by
    unfold TCell.lam; push_cast; rw [Sq_cast]
  have hlam0 : (0 : ℝ) ≤ ((c.lam : ℚ) : ℝ) := by rw [hlamR]; positivity
  have hTD : e8Theta (ys / (H p + H q)) = seamDelta (1 / 10000) (H p) (H q) ys := by
    have h := seamD_eq_sub (1 / 10000) (H p) (H q) ys
    rw [hstat] at h
    linarith
  have hΔup : seamDelta (1 / 10000) (H p) (H q) ys ≤
      ((c.Pmax : ℚ) : ℝ) / 2 * Real.log (H q / H p) + ((c.lam : ℚ) : ℝ) * ys := by
    have h := seamDelta_le_log (S := 1 / 10000) (y := ys) (P := ((c.Pmax : ℚ) : ℝ)) hHp hHpq
      hys0.le (by linarith) hPmax0R (fun t ht => hPmaxAll t (le_trans hXf ht.1))
    have hL : ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys)) ≤ ((c.lam : ℚ) : ℝ) * ys := by
      rw [hlamR]
      have h1 : (1 - 2 * (1 / 10000) : ℝ) ≤ 1 - 1 / 10000 - ys := by linarith
      have h2 : ys / (1 - 1 / 10000 - ys) ≤ ys / (1 - 2 * (1 / 10000)) :=
        div_le_div_of_nonneg_left hys0.le (by norm_num) h1
      calc ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys))
          ≤ ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 2 * (1 / 10000))) := mul_le_mul_of_nonneg_left h2 hPmax0R
        _ = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000)) * ys := by ring
    linarith
  have hlogκ : Real.log (H q / H p) = Real.log (1 / (H p / H q)) := by
    congr 1; field_simp
  have hk1R : ((c.k1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hk11
  have hkpos : 0 < H p / H q := div_pos hHp hHq
  match kind, hkind with
  | 0, hkind =>
    obtain ⟨hk0pos, hneed, hDT, hfin⟩ := of_decide_eq_true hkind
    have hk0R : (0 : ℝ) < ((c.k0 : ℚ) : ℝ) := by exact_mod_cast hk0pos
    have hA0 : ((c.Pmax : ℚ) : ℝ) / 2 * Real.log (H q / H p) ≤ ((c.A0 : ℚ) : ℝ) := by
      have eA : ((c.A0 : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / 2 * ((logUpQ (1 / c.k0) : ℚ) : ℝ) := by
        unfold TCell.A0; push_cast; ring
      rw [eA]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hpos : (0 : ℚ) < 1 / c.k0 := by positivity
      refine le_trans ?_ (by have := logUpQ_sound hpos; push_cast at this; exact this)
      rw [hlogκ]
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le hk0R hk0
    have hΔ : seamDelta (1 / 10000) (H p) (H q) ys ≤ ((c.A0 : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * ys := by
      linarith
    have hxbR : (0 : ℝ) < ((c.xb : ℚ) : ℝ) := by exact_mod_cast hxb
    have hθb : ((c.thb : ℚ) : ℝ) ≤ e8Theta ((c.xb : ℚ) : ℝ) := theta_ge_Slo dxb hxbv hxb le_rfl hbrxb
    have hneedR : ((c.A0 : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * (1 / 10000) < ((c.thb : ℚ) : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hneed
      push_cast at h; rw [Sq_cast] at h; exact h
    have eDT : ((c.DT : ℚ) : ℝ) = ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) -
        ((c.lam : ℚ) : ℝ) * ((c.ET : ℚ) : ℝ) := by unfold TCell.DT; push_cast; ring
    have hDTR : (0 : ℝ) < ((c.DT : ℚ) : ℝ) := by exact_mod_cast hDT
    have hdenR : ((c.lam : ℚ) : ℝ) * (H p + H q) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hET hlam0
      linarith
    have hyhi : ys ≤ 1 / 10000 := by linarith
    have hxst := xstar_le (S := 1 / 10000) hHp hHq hstat hΔ hys0 hyhi hlam0 hxbR hθb hneedR hdenR
    have hyslt : ys / (H p + H q) < ((c.xb : ℚ) : ℝ) := by
      by_contra hcon
      push Not at hcon
      have h1 := e8Theta_mono hxbR hcon
      have h2 : ((c.lam : ℚ) : ℝ) * ys ≤ ((c.lam : ℚ) : ℝ) * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hyhi hlam0
      linarith
    have hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
        ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q)) := by
      intro t ht
      have h := slope_Mof okx2 hdhk hbrx2 (div_pos ht.1 hE)
        (div_le_div_of_nonneg_right ht.2.le hE.le) hyslt.le
      have e : ys / (H p + H q) - t / (H p + H q) = (ys - t) / (H p + H q) := by ring
      rw [e] at h; exact h
    have hM0R : (0 : ℝ) ≤ ((c.M : ℚ) : ℝ) := by exact_mod_cast hM0
    set D := ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * (H p + H q) with hD
    have hDge : ((c.DT : ℚ) : ℝ) ≤ D := by
      rw [eDT, hD]; have := mul_le_mul_of_nonneg_left hET hlam0; linarith
    have hD0 : 0 < D := lt_of_lt_of_le hDTR hDge
    have hA0nn : (0 : ℝ) ≤ ((c.A0 : ℚ) : ℝ) := by
      have : 0 ≤ Real.log (H q / H p) := Real.log_nonneg (by rw [le_div_iff₀ hHp]; linarith)
      nlinarith
    have hcheck : 0 ≤ 0 + 0 + ((c.B0 : ℚ) : ℝ) - ((c.M : ℚ) : ℝ) *
        (((c.A0 : ℚ) : ℝ) * (H p + H q) / D) ^ 2 / (2 * (H p + H q)) := by
      have hfinR := (Rat.cast_le (K := ℝ)).mpr hfin
      push_cast at hfinR
      have e1 : ((c.M : ℚ) : ℝ) * (((c.A0 : ℚ) : ℝ) * (H p + H q) / D) ^ 2 / (2 * (H p + H q)) =
          ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * (H p + H q) / (2 * D ^ 2) := by
        field_simp
      have h2 : ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * (H p + H q) / (2 * D ^ 2) ≤
          ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * ((c.ET : ℚ) : ℝ) / (2 * ((c.DT : ℚ) : ℝ) ^ 2) := by
        have hnum : ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * (H p + H q) ≤
            ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * ((c.ET : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hET (by positivity)
        have hden : 2 * ((c.DT : ℚ) : ℝ) ^ 2 ≤ 2 * D ^ 2 := by
          have := pow_le_pow_left₀ hDTR.le hDge 2; linarith
        calc ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * (H p + H q) / (2 * D ^ 2)
            ≤ ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * ((c.ET : ℚ) : ℝ) / (2 * D ^ 2) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ ((c.M : ℚ) : ℝ) * ((c.A0 : ℚ) : ℝ) ^ 2 * ((c.ET : ℚ) : ℝ) / (2 * ((c.DT : ℚ) : ℝ) ^ 2) :=
              div_le_div_of_nonneg_left (by have := le_trans hE.le hET; positivity)
                (by positivity) hden
      rw [e1]
      linarith
    exact seam_master_Aval (by norm_num) le_rfl hp hpq hqS hys0 hysS hstat hDC (by linarith)
      (by linarith) hM hM0R (by rw [mul_div_assoc] at hxst ⊢; exact hxst) hcheck
  | 1, hkind =>
    obtain ⟨hk0pos, hk1eq, hneed, hDT, hfin⟩ := of_decide_eq_true hkind
    have hk0R : (0 : ℝ) < ((c.k0 : ℚ) : ℝ) := by exact_mod_cast hk0pos
    set κ := H p / H q with hκd
    have hκ1 : κ ≤ 1 := by rw [hκd, div_le_one hHq]; exact hHpq
    -- A0 := Pmax/2 · log(1/κ) ≤ (1 − κ)·Pmax/(2 k0)
    have hlog : Real.log (H q / H p) ≤ (1 - κ) / κ := by
      rw [hlogκ]
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 / κ by positivity)
      have e : 1 / κ - 1 = (1 - κ) / κ := by field_simp
      linarith
    set A0 := ((c.Pmax : ℚ) : ℝ) / 2 * ((1 - κ) / κ) with hA0d
    have hΔ : seamDelta (1 / 10000) (H p) (H q) ys ≤ A0 + ((c.lam : ℚ) : ℝ) * ys := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) / 2)
      linarith
    have hA0le : A0 ≤ (1 - κ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) := by
      rw [hA0d]
      have h1 : (1 - κ) / κ ≤ (1 - κ) / ((c.k0 : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left (by linarith) hk0R hk0
      have e : (1 - κ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) =
          ((c.Pmax : ℚ) : ℝ) / 2 * ((1 - κ) / ((c.k0 : ℚ) : ℝ)) := by ring
      rw [e]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hA0max : A0 ≤ ((c.Pmax : ℚ) : ℝ) / 2 * ((1 - ((c.k0 : ℚ) : ℝ)) / ((c.k0 : ℚ) : ℝ)) := by
      rw [hA0d]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have e1 : (1 - κ) / κ = 1 / κ - 1 := by field_simp
      have e2 : (1 - ((c.k0 : ℚ) : ℝ)) / ((c.k0 : ℚ) : ℝ) = 1 / ((c.k0 : ℚ) : ℝ) - 1 := by field_simp
      rw [e1, e2]
      have := one_div_le_one_div_of_le hk0R hk0
      linarith
    have hA0nn : 0 ≤ A0 := by rw [hA0d]; apply mul_nonneg (by positivity); apply div_nonneg (by linarith) hkpos.le
    have hxbR : (0 : ℝ) < ((c.xb : ℚ) : ℝ) := by exact_mod_cast hxb
    have hθb : ((c.thb : ℚ) : ℝ) ≤ e8Theta ((c.xb : ℚ) : ℝ) := theta_ge_Slo dxb hxbv hxb le_rfl hbrxb
    have hneedR : A0 + ((c.lam : ℚ) : ℝ) * (1 / 10000) < ((c.thb : ℚ) : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hneed
      push_cast at h; rw [Sq_cast] at h
      linarith
    have eDT : ((c.DT : ℚ) : ℝ) = ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) -
        ((c.lam : ℚ) : ℝ) * ((c.ET : ℚ) : ℝ) := by unfold TCell.DT; push_cast; ring
    have hDTR : (0 : ℝ) < ((c.DT : ℚ) : ℝ) := by exact_mod_cast hDT
    have hdenR : ((c.lam : ℚ) : ℝ) * (H p + H q) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hET hlam0
      linarith
    have hyhi : ys ≤ 1 / 10000 := by linarith
    have hxst := xstar_le (S := 1 / 10000) hHp hHq hstat hΔ hys0 hyhi hlam0 hxbR hθb hneedR hdenR
    have hyslt : ys / (H p + H q) < ((c.xb : ℚ) : ℝ) := by
      by_contra hcon
      push Not at hcon
      have h1 := e8Theta_mono hxbR hcon
      have h2 : ((c.lam : ℚ) : ℝ) * ys ≤ ((c.lam : ℚ) : ℝ) * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hyhi hlam0
      linarith
    have hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
        ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q)) := by
      intro t ht
      have h := slope_Mof okx2 hdhk hbrx2 (div_pos ht.1 hE)
        (div_le_div_of_nonneg_right ht.2.le hE.le) hyslt.le
      have e : ys / (H p + H q) - t / (H p + H q) = (ys - t) / (H p + H q) := by ring
      rw [e] at h; exact h
    have hM0R : (0 : ℝ) ≤ ((c.M : ℚ) : ℝ) := by exact_mod_cast hM0
    set D := ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * (H p + H q) with hD
    have hDge : ((c.DT : ℚ) : ℝ) ≤ D := by
      rw [eDT, hD]; have := mul_le_mul_of_nonneg_left hET hlam0; linarith
    have hD0 : 0 < D := lt_of_lt_of_le hDTR hDge
    -- bulk with (1 − κ)²
    have hjq := tcell_jdef c hcom hp hpq hqT hk0 hk1
    have hBq : (1 / 10000 / 2 - ((c.qT : ℚ) : ℝ)) * (9 / 40 * (1 - κ) ^ 2) ≤
        emLine (H p) (H q) (1 / 10000 / 2) - emLine (H p) (H q) q := by
      have hmvt := emLine_mvt (ℓ := 9 / 40 * (1 - κ) ^ 2) hHp hHq hqS (by linarith) hjq
      have := mul_le_mul_of_nonneg_right (show 1 / 10000 / 2 - ((c.qT : ℚ) : ℝ) ≤ 1 / 10000 / 2 - q by
        linarith) (by positivity : (0 : ℝ) ≤ 9 / 40 * (1 - κ) ^ 2)
      linarith
    have hcheck : 0 ≤ 0 + 0 + (1 / 10000 / 2 - ((c.qT : ℚ) : ℝ)) * (9 / 40 * (1 - κ) ^ 2) -
        ((c.M : ℚ) : ℝ) * (A0 * (H p + H q) / D) ^ 2 / (2 * (H p + H q)) := by
      have hfinR := (Rat.cast_le (K := ℝ)).mpr hfin
      push_cast at hfinR
      rw [Sq_cast] at hfinR
      have e1 : ((c.M : ℚ) : ℝ) * (A0 * (H p + H q) / D) ^ 2 / (2 * (H p + H q)) =
          ((c.M : ℚ) : ℝ) * A0 ^ 2 * (H p + H q) / (2 * D ^ 2) := by field_simp
      have hA2 : A0 ^ 2 ≤ (1 - κ) ^ 2 * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 := by
        have := pow_le_pow_left₀ hA0nn hA0le 2
        nlinarith
      have h2 : ((c.M : ℚ) : ℝ) * A0 ^ 2 * (H p + H q) / (2 * D ^ 2) ≤
          (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
            ((c.ET : ℚ) : ℝ) / (2 * ((c.DT : ℚ) : ℝ) ^ 2)) := by
        have hnum : ((c.M : ℚ) : ℝ) * A0 ^ 2 * (H p + H q) ≤
            (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
              ((c.ET : ℚ) : ℝ)) := by
          have h3 := mul_le_mul hA2 hET hE.le (by positivity)
          have h4 := mul_le_mul_of_nonneg_left h3 hM0R
          nlinarith
        have hden : 2 * ((c.DT : ℚ) : ℝ) ^ 2 ≤ 2 * D ^ 2 := by
          have := pow_le_pow_left₀ hDTR.le hDge 2; linarith
        calc ((c.M : ℚ) : ℝ) * A0 ^ 2 * (H p + H q) / (2 * D ^ 2)
            ≤ (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
              ((c.ET : ℚ) : ℝ)) / (2 * D ^ 2) := div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
              ((c.ET : ℚ) : ℝ)) / (2 * ((c.DT : ℚ) : ℝ) ^ 2) :=
              div_le_div_of_nonneg_left (by have := le_trans hE.le hET; positivity) (by positivity) hden
          _ = (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
              ((c.ET : ℚ) : ℝ) / (2 * ((c.DT : ℚ) : ℝ) ^ 2)) := by ring
      have h5 : (1 - κ) ^ 2 * (((c.M : ℚ) : ℝ) * (((c.Pmax : ℚ) : ℝ) / 2 / ((c.k0 : ℚ) : ℝ)) ^ 2 *
            ((c.ET : ℚ) : ℝ) / (2 * ((c.DT : ℚ) : ℝ) ^ 2)) ≤
          (1 - κ) ^ 2 * ((1 / 10000 / 2 - ((c.qT : ℚ) : ℝ)) * (9 / 40)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      rw [e1]
      nlinarith
    exact seam_master_Aval (by norm_num) le_rfl hp hpq hqS hys0 hysS hstat hDC (by linarith)
      hBq hM hM0R (by rw [mul_div_assoc] at hxst ⊢; exact hxst) hcheck
  | (n + 2), hkind =>
    obtain ⟨okxK, okvK, hxK, hbrxK, haxK, hvxK, hfl1, hshi, hbrvK, hvKa1, hfin⟩ :=
      of_decide_eq_true hkind
    have dxK := dy_sound okxK
    have dvK := dy_sound okvK
    have hxKR : (0 : ℝ) < ((c.xK : ℚ) : ℝ) := by exact_mod_cast hxK
    -- Θ(y*/E) = Δ(y*) ≥ Pmin0/2 · log(f/e) ≥ Pmin0/2 · logDn(1/k1) > Shi(xK) ≥ Θ(xK)
    have hΔlo := seamDelta_ge (S := 1 / 10000) (y := ys) (P := ((c.Pmin0 : ℚ) : ℝ)) hHp hHpq hys0.le
      (by linarith) hPmin0R (fun t ht => hPminAll t (le_trans hXf ht.1))
    have hk1p : (0 : ℝ) < ((c.k1 : ℚ) : ℝ) := by exact_mod_cast hk1pos
    have hlog1 : ((logDnQ (1 / c.k1) : ℚ) : ℝ) ≤ Real.log (H q / H p) := by
      refine le_trans (logDnQ_sound hfl1) ?_
      push_cast
      rw [hlogκ]
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le hkpos hk1
    have hThK : e8Theta ((c.xK : ℚ) : ℝ) ≤ (((dy c.nxK).Shi : ℚ) : ℝ) :=
      theta_le_Shi dxK hvxK haxK hxKR le_rfl hbrxK
    have hshiR : (((dy c.nxK).Shi : ℚ) : ℝ) < ((c.Pmin0 : ℚ) : ℝ) / 2 *
        ((logDnQ (1 / c.k1) : ℚ) : ℝ) := by
      have := (Rat.cast_lt (K := ℝ)).mpr hshi
      push_cast at this; exact this
    have hxge : ((c.xK : ℚ) : ℝ) ≤ ys / (H p + H q) := by
      by_contra hcon
      push Not at hcon
      have h1 := e8Theta_mono (div_pos hys0 hE) hcon.le
      have h2 := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ ((c.Pmin0 : ℚ) : ℝ) / 2)
      linarith
    -- v* ≤ vK and the slope-gap bound
    have hvstar : radialContact ys ((H p + H q) / 2) = radialContact (2 * (ys / (H p + H q))) 1 := by
      rw [radialContact_normalize_entropy ys (show (H p + H q) / 2 ≠ 0 by positivity)]
      congr 1; field_simp
    have hvK := contact_le_of_bracket dvK hxK hbrvK hxge
    rw [← hvstar] at hvK
    set v := radialContact ys ((H p + H q) / 2) with hvd
    have hv0 : 0 < v := radialContact_pos hys0 (by positivity)
    have hvh : v < 1 / 2 := radialContact_lt_half hys0 (by positivity)
    have hLv : ((dy c.nvK).a1 : ℝ) ≤ -Real.log v := by
      have h1 := dvK.2.2.1
      have h2 : Real.log v ≤ Real.log ((dy c.nvK).v : ℝ) := Real.log_le_log hv0 hvK
      linarith
    have ha1R : (0 : ℝ) < ((dy c.nvK).a1 : ℝ) := by exact_mod_cast hvKa1
    have hgap := slopeGap_le hv0 hvh.le (lt_of_lt_of_le ha1R hLv)
    have hgap2 : radialSlope v - J v ≤ (1 + 1 / ((dy c.nvK).a1 : ℝ)) / ((L2loD : ℚ) : ℝ) := by
      refine le_trans hgap ?_
      have h1 : 1 / (-Real.log v) ≤ 1 / ((dy c.nvK).a1 : ℝ) := one_div_le_one_div_of_le ha1R hLv
      have hl2 := log2D_bounds
      have hL0 := VD.L2lo_pos
      calc (1 + 1 / (-Real.log v)) / Real.log 2 ≤ (1 + 1 / ((dy c.nvK).a1 : ℝ)) / Real.log 2 :=
            div_le_div_of_nonneg_right (by linarith) (by have := log_two_pos; linarith)
        _ ≤ (1 + 1 / ((dy c.nvK).a1 : ℝ)) / ((L2loD : ℚ) : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hL0 hl2.1
    have hdipK : dipK (H p + H q) ys ≤ 1 / 10000 * ((1 + 1 / ((dy c.nvK).a1 : ℝ)) / ((L2loD : ℚ) : ℝ)) := by
      rw [dipK_eq hE hys0]
      have hK0 : 0 ≤ radialSlope v - J v := by
        unfold radialSlope
        rw [add_sub_cancel_left]
        have : 0 < kap v := kap_pos hv0 hvh
        have : 0 ≤ hn v := by
          rw [hn_eq_H_mul_log]; exact mul_nonneg (H_nonneg hv0.le (by linarith)) log_two_pos.le
        apply div_nonneg (mul_nonneg (by linarith) this)
        have := log_two_pos
        have h1v : 0 < 1 - v := by linarith
        positivity
      have h1 := mul_le_mul_of_nonneg_left hgap2 hys0.le
      have h2 : ys * ((1 + 1 / ((dy c.nvK).a1 : ℝ)) / ((L2loD : ℚ) : ℝ)) ≤
          1 / 10000 * ((1 + 1 / ((dy c.nvK).a1 : ℝ)) / ((L2loD : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by have := VD.L2lo_pos; positivity)
      linarith
    have hkb := seam_kbound' (S := 1 / 10000) (by norm_num) hHp hHq le_rfl hys0 (by linarith) hstat
    rw [seamCurve_zero] at hkb
    have hfinR := (Rat.cast_le (K := ℝ)).mpr hfin
    push_cast at hfinR
    rw [Sq_cast] at hfinR
    have e : (1 / 10000 : ℝ) * (1 + 1 / (((dy c.nvK).a1 : ℚ) : ℝ)) / ((L2loD : ℚ) : ℝ) =
        1 / 10000 * ((1 + 1 / (((dy c.nvK).a1 : ℚ) : ℝ)) / ((L2loD : ℚ) : ℝ)) := by ring
    rw [e] at hfinR
    linarith

end CKLaneP
