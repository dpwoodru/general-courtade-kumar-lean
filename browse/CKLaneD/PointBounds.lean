import CKLaneD.LogCert
import GeneralCK.ProfileDerivatives

/-!
# Lane D: rational enclosures of `H x` and `J x` at a rational point

From certified bounds on `log x` and `log (1 - x)` and on `log 2`.
-/

namespace CKLaneD

open GeneralCK

/-- Lower bound of `N / log 2` from a lower bound `N0` of `N`. -/
def divLo (N : ℚ) : ℚ := if 0 ≤ N then N / L1 else N / L0

/-- Upper bound of `N / log 2` from an upper bound `N1` of `N`. -/
def divHi (N : ℚ) : ℚ := if 0 ≤ N then N / L0 else N / L1

theorem divLo_le {N0 : ℚ} {N : ℝ} (h : (N0 : ℝ) ≤ N) :
    ((divLo N0 : ℚ) : ℝ) ≤ N / Real.log 2 := by
  have hL := log2_bounds
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := L0_pos_real
  have hL1 : (0 : ℝ) < (L1 : ℝ) := hL0.trans_le (hL.1.trans hL.2)
  unfold divLo
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast h0
    rw [div_le_div_iff₀ hL1 hl2]
    nlinarith
  · push_cast
    have h0' : (N0 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    rw [div_le_div_iff₀ hL0 hl2]
    nlinarith

theorem le_divHi {N1 : ℚ} {N : ℝ} (h : N ≤ (N1 : ℝ)) :
    N / Real.log 2 ≤ ((divHi N1 : ℚ) : ℝ) := by
  have hL := log2_bounds
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := L0_pos_real
  have hL1 : (0 : ℝ) < (L1 : ℝ) := hL0.trans_le (hL.1.trans hL.2)
  unfold divHi
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast h0
    rw [div_le_div_iff₀ hl2 hL0]
    nlinarith
  · push_cast
    have h0' : (N1 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    rw [div_le_div_iff₀ hl2 hL1]
    nlinarith

/-- Logarithm certificates for `x` and `1 - x`. -/
structure PtCert where
  cx : LogCert
  cy : LogCert
  deriving Repr, DecidableEq

def checkPt (x : ℚ) (p : PtCert) : Bool := checkLogCert x p.cx && checkLogCert (1 - x) p.cy

def Hlo (x : ℚ) (p : PtCert) : ℚ := divLo (x * (-p.cx.hi) + (1 - x) * (-p.cy.hi))
def Hhi (x : ℚ) (p : PtCert) : ℚ := divHi (x * (-p.cx.lo) + (1 - x) * (-p.cy.lo))
def Jlo (_x : ℚ) (p : PtCert) : ℚ := divLo (p.cy.lo - p.cx.hi)
def Jhi (_x : ℚ) (p : PtCert) : ℚ := divHi (p.cy.hi - p.cx.lo)

theorem H_eq_logs (x : ℝ) :
    H x = (x * (-Real.log x) + (1 - x) * (-Real.log (1 - x))) / Real.log 2 := by
  unfold H
  congr 1
  simp only [Real.binEntropy, Real.log_inv]
  try ring

theorem J_eq_logs {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    J x = (Real.log (1 - x) - Real.log x) / Real.log 2 := by
  unfold J
  rw [Real.log_div (by linarith) hx.ne']

theorem checkPt_bounds {x : ℚ} {p : PtCert} (h : checkPt x p = true) :
    0 < x ∧ x < 1 ∧
    (Hlo x p : ℝ) ≤ H (x : ℝ) ∧ H (x : ℝ) ≤ (Hhi x p : ℝ) ∧
    (Jlo x p : ℝ) ≤ J (x : ℝ) ∧ J (x : ℝ) ≤ (Jhi x p : ℝ) := by
  unfold checkPt at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hx0 : 0 < x := by
    unfold checkLogCert at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  have hx1 : 0 < 1 - x := by
    unfold checkLogCert at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.1.1
  have hA := checkLogCert_sound h1
  have hB := checkLogCert_sound h2
  push_cast at hB
  have hx0' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by
    have : x < 1 := by linarith
    exact_mod_cast this
  refine ⟨hx0, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [H_eq_logs]
    unfold Hlo
    apply divLo_le
    push_cast
    have h1x : (0 : ℝ) ≤ 1 - (x : ℝ) := by linarith
    nlinarith [hA.1, hA.2, hB.1, hB.2]
  · rw [H_eq_logs]
    unfold Hhi
    apply le_divHi
    push_cast
    have h1x : (0 : ℝ) ≤ 1 - (x : ℝ) := by linarith
    nlinarith [hA.1, hA.2, hB.1, hB.2]
  · rw [J_eq_logs hx0' hx1']
    unfold Jlo
    apply divLo_le
    push_cast
    linarith [hA.1, hA.2, hB.1, hB.2]
  · rw [J_eq_logs hx0' hx1']
    unfold Jhi
    apply le_divHi
    push_cast
    linarith [hA.1, hA.2, hB.1, hB.2]

end CKLaneD
