import CKLaneN23.CUni

/-!
# CKLaneN23.CStep2 — Horner step, shifted candidates, and the implicit-function TMs (Lane N23b)

* `step_horner` : Boolean-checked `tmHorner` step.
* `monoT k c`   : the TPoly `c x^k`; candidates `G ± cb x^NU` are `TPoly.add G (monoT NU (±cb))`.
* `gC_TM`       : residual signs (checked TMs) ⇒ `Good (x ↦ gC (cw x)) ⟨G, cb, NU⟩`.
* `Rst_TM`      : residual signs (checked TMs) ⇒ `Good (x ↦ Rst (ce x)) ⟨PR, cb, NU⟩`.
-/

namespace CKLaneN23.CT

open GeneralCK

noncomputable def hornerChk (X : TMd) (vx n : ℕ) (cs : List LPoly) (D : TMd) : Bool :=
  zeroPrefix X.P vx && decide (vx ≤ X.n) && decide (n ≤ X.n) && matchChk (tmHorner X vx n cs) D

theorem step_horner {x : ℝ → ℝ → ℝ → ℝ} {X D : TMd} (hx : Good x X) (vx n : ℕ) (cs : List LPoly)
    (hc : hornerChk X vx n cs D = true) : Good (fun a σ τ => hornerL cs (x a σ τ)) D := by
  unfold hornerChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact (tmHorner_good hx vx n h1 h2 h3 cs).1.of_chk h4

/-- `c x^k` -/
def monoT : ℕ → ℚ → TPoly
  | 0, c => [[((0, 0), [(0, c)])]]
  | k + 1, c => [] :: monoT k c

theorem eval_monoT (x σ τ : ℝ) (k : ℕ) (c : ℚ) :
    TPoly.eval x σ τ (Real.log 2) (monoT k c) = (c : ℝ) * x ^ k := by
  induction k with
  | zero =>
    simp [monoT, TPoly.eval_cons, TPoly.eval_nil, QPoly.eval_cons, QPoly.eval_nil, LPoly.eval_cons,
      LPoly.eval_nil]
  | succ k ih =>
    rw [monoT, TPoly.eval_cons, QPoly.eval_nil, ih]
    ring

theorem ev_shift (G : TPoly) (k : ℕ) (c : ℚ) (x σ τ : ℝ) :
    ev (TPoly.add G (monoT k c)) x σ τ = ev G x σ τ + (c : ℝ) * x ^ k := by
  unfold ev
  rw [TPoly.eval_add, eval_monoT]

theorem LPoly.eval_c (q : ℚ) : LPoly.eval (Real.log 2) [(0, q)] = (q : ℝ) := LPoly.eval_const q

/-! ## contact ratio TM from two residual signs -/

theorem gC_TM (cw cb : ℚ) (hcw : 0 < cw) (hcw1 : cw ≤ 5) (hcb : 0 ≤ cb) (G : TPoly) (NU : ℕ)
    (hres_p : ∀ x σ τ, Dom x σ τ →
      hent (Real.sqrt ((cw : ℝ) * x * (ev (TPoly.add G (monoT NU cb)) x σ τ *
        ev (TPoly.add G (monoT NU cb)) x σ τ))) +
        ((-1 : ℚ) : ℝ) * ev (TPoly.add G (monoT NU cb)) x σ τ ≤ 0)
    (hres_m : ∀ x σ τ, Dom x σ τ →
      0 ≤ hent (Real.sqrt ((cw : ℝ) * x * (ev (TPoly.add G (monoT NU (-cb))) x σ τ *
        ev (TPoly.add G (monoT NU (-cb))) x σ τ))) +
        ((-1 : ℚ) : ℝ) * ev (TPoly.add G (monoT NU (-cb))) x σ τ)
    (hm0 : ∀ x σ τ, Dom x σ τ → 0 ≤ ev (TPoly.add G (monoT NU (-cb))) x σ τ)
    (hp2 : ∀ x σ τ, Dom x σ τ →
      ev (TPoly.add G (monoT NU cb)) x σ τ + LPoly.eval (Real.log 2) [(0, -2)] ≤ 0) :
    Good (fun x _ _ => gC ((cw : ℝ) * x)) ⟨G, cb, NU⟩ := by
  refine ⟨?_, hcb⟩
  intro x σ τ hd
  have hx0 := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  have hcw' : (0 : ℝ) < cw := by exact_mod_cast hcw
  have hcw1' : (cw : ℝ) ≤ 5 := by exact_mod_cast hcw1
  have hw : 0 < (cw : ℝ) * x := mul_pos hcw' hx0
  have hw4 : (cw : ℝ) * x ≤ 1 / 4 := by nlinarith
  have hsw : Real.sqrt ((cw : ℝ) * x) ≤ 1 / 2 := by
    have : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact Real.sqrt_le_sqrt hw4
  have hGp := ev_shift G NU cb x σ τ
  have hGm := ev_shift G NU (-cb) x σ τ
  have hp2' := hp2 x σ τ hd
  rw [LPoly.eval_c] at hp2'
  push_cast at hp2'
  have hm0' := hm0 x σ τ hd
  have hcbx : (0 : ℝ) ≤ (cb : ℝ) * x ^ NU := mul_nonneg (by exact_mod_cast hcb) (pow_nonneg hx0.le _)
  have hmp : ev (TPoly.add G (monoT NU (-cb))) x σ τ ≤ ev (TPoly.add G (monoT NU cb)) x σ τ := by
    rw [hGp, hGm]; push_cast; linarith
  have hp1 : Real.sqrt ((cw : ℝ) * x) * ev (TPoly.add G (monoT NU cb)) x σ τ ≤ 1 := by
    have h0 : 0 ≤ ev (TPoly.add G (monoT NU cb)) x σ τ := hm0'.trans hmp
    have := mul_le_mul hsw (show ev (TPoly.add G (monoT NU cb)) x σ τ ≤ 2 by linarith) h0 (by norm_num)
    linarith
  obtain ⟨hlo, hhi⟩ := gC_bracket hw hm0' hmp hp1 (hres_m x σ τ hd) (hres_p x σ τ hd)
  rw [hGp] at hhi
  rw [hGm] at hlo
  push_cast at hlo hhi
  show |gC ((cw : ℝ) * x) - ev G x σ τ| ≤ (cb : ℝ) * x ^ NU
  rw [abs_le]
  constructor <;> nlinarith

/-! ## entropy-inverse TM from two residual signs -/

theorem Rst_TM (ce cb : ℚ) (hce : 0 < ce) (hce1 : ce ≤ 10) (hcb : 0 ≤ cb) (PR : TPoly) (NU : ℕ)
    (hres_p : ∀ x σ τ, Dom x σ τ →
      hent (Real.sqrt (ev (TPoly.add PR (monoT NU cb)) x σ τ)) +
        ((ce : ℝ) * x + LPoly.eval (Real.log 2) [(0, -1)]) ≤ 0)
    (hres_m : ∀ x σ τ, Dom x σ τ →
      0 ≤ hent (Real.sqrt (ev (TPoly.add PR (monoT NU (-cb))) x σ τ)) +
        ((ce : ℝ) * x + LPoly.eval (Real.log 2) [(0, -1)]))
    (hm0 : ∀ x σ τ, Dom x σ τ → 0 ≤ ev (TPoly.add PR (monoT NU (-cb))) x σ τ)
    (hp1 : ∀ x σ τ, Dom x σ τ →
      ev (TPoly.add PR (monoT NU cb)) x σ τ + LPoly.eval (Real.log 2) [(0, -1)] ≤ 0) :
    Good (fun x _ _ => Rst ((ce : ℝ) * x)) ⟨PR, cb, NU⟩ := by
  refine ⟨?_, hcb⟩
  intro x σ τ hd
  have hx0 := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  have hce' : (0 : ℝ) < ce := by exact_mod_cast hce
  have hce1' : (ce : ℝ) ≤ 10 := by exact_mod_cast hce1
  have hε0 : 0 < (ce : ℝ) * x := mul_pos hce' hx0
  have hε1 : (ce : ℝ) * x < 1 := by nlinarith
  have hGp := ev_shift PR NU cb x σ τ
  have hGm := ev_shift PR NU (-cb) x σ τ
  have hp1' := hp1 x σ τ hd
  rw [LPoly.eval_c] at hp1'
  push_cast at hp1'
  have hm0' := hm0 x σ τ hd
  have hcbx : (0 : ℝ) ≤ (cb : ℝ) * x ^ NU := mul_nonneg (by exact_mod_cast hcb) (pow_nonneg hx0.le _)
  have hmp : ev (TPoly.add PR (monoT NU (-cb))) x σ τ ≤ ev (TPoly.add PR (monoT NU cb)) x σ τ := by
    rw [hGp, hGm]; push_cast; linarith
  have hlo0 := hres_m x σ τ hd
  have hhi0 := hres_p x σ τ hd
  rw [LPoly.eval_c] at hlo0 hhi0
  obtain ⟨hlo, hhi⟩ := Rst_bracket hε0 hε1 hm0' hmp (by linarith) hlo0 hhi0
  rw [hGp] at hhi
  rw [hGm] at hlo
  push_cast at hlo hhi
  show |Rst ((ce : ℝ) * x) - ev PR x σ τ| ≤ (cb : ℝ) * x ^ NU
  rw [abs_le]
  constructor <;> nlinarith

end CKLaneN23.CT
