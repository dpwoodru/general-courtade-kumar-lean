import CKLaneN4.SplitKernel

/-!
# Lane N4: GLOBAL_SPLIT (archived two-leaf partition of `q ∈ [0, 11/25]`), kernel-checked

Archive `/tmp/ckgc/CK_GENERAL_COMPLETION/reduction/eight_global/GLOBAL_SPLIT_RESULT.json` (sha256 `83733dbdbbba470818c2258669ec602596d9a898822bab9d2aae6b175097b341`), claim `E·2c0(q)Cn(Cq/(2c0(q)))/q^2 < 1/5 for E≤11/200, q≤11/25`.
Leaves `0` = `[0, 11/50]` and `1` = `[11/50, 11/25]`; certified normalized values (×11/200)
0.189686 and 0.182333 (archived [0.1896861862406186306 and [0.1823331023414647731).

Consequences:
* `split_bound`: `13q/6 < 2 c0(q)` and `2 c0(q) · capacity((13q/6)/(2 c0(q))) ≤ (40/11) q^2` on `[0, 11/25]`;
* `endpointCoefficient_ge_c0`: `d ≤ 1 - q → c0(q) ≤ endpointCoefficient d`;
* `split_term_lower`: the signed split term of `retained_child_decomposition` is `≥ -(1/5) q^2/E`
  (`E ≤ 11/200`, `0 ≤ q ≤ 11/25`, `d ≤ 1 - q`, `0 ≤ A ≤ 13q/(3E)`, `|t| < 1`).
-/

namespace CKLaneN4

open GeneralCK CKLaneD PsiSignedSplit PsiChildEntropyCoupling

/-- Log certificate of `1 + z_r` for leaf `0`. -/
def splitCp0 : LogCert := ⟨0, 15, (511981548543774142767 / 1180591620717411303424 : ℚ), (1023963097087548285543 / 2361183241434822606848 : ℚ)⟩
/-- Log certificate of `1 - z_r` for leaf `0`. -/
def splitCm0 : LogCert := ⟨1, 7, (-231058922645319141745 / 295147905179352825856 : ℚ), (-3696942762325106267863 / 4722366482869645213696 : ℚ)⟩
/-- Log certificate of `1 + z_r` for leaf `1`. -/
def splitCp1 : LogCert := ⟨0, 20, (384781422068929056061 / 590295810358705651712 : ℚ), (3078251376551432448517 / 4722366482869645213696 : ℚ)⟩
/-- Log certificate of `1 - z_r` for leaf `1`. -/
def splitCm1 : LogCert := ⟨4, 11, (-5936663537392215703093 / 2361183241434822606848 : ℚ), (-11873327074784431406155 / 4722366482869645213696 : ℚ)⟩

theorem split_leaf0 : checkSplit 0 (11 / 50) splitCp0 splitCm0 = true := by decide +kernel

theorem split_leaf1 : checkSplit (11 / 50) (11 / 25) splitCp1 splitCm1 = true := by decide +kernel

theorem split_bound {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 11 / 25) :
    13 * q / 6 < 2 * c0 q ∧
      2 * c0 q * capacity ((13 * q / 6) / (2 * c0 q)) ≤ (40 / 11) * q ^ 2 := by
  by_cases h : q ≤ 11 / 50
  · exact checkSplit_sound split_leaf0 (by push_cast; linarith) (by push_cast; linarith)
  · exact checkSplit_sound split_leaf1 (by push_cast; linarith) (by push_cast; linarith)

theorem endpointCoefficient_ge_c0 {d q : ℝ} (hdq : d ≤ 1 - q) :
    c0 q ≤ endpointCoefficient d := by
  have hβ := c0_beta_pos
  have e : endpointCoefficient d - c0 q = (13 / 12 - 1 / (2 * Real.log 2)) * (1 - d - q) := by
    unfold endpointCoefficient c0
    field_simp
    ring
  have : 0 ≤ (13 / 12 - 1 / (2 * Real.log 2)) * (1 - d - q) :=
    mul_nonneg hβ.le (by linarith)
  linarith

theorem split_term_lower {d q E A t : ℝ} (hE : 0 < E) (hEi : E ≤ 11 / 200) (hq : 0 ≤ q)
    (hq' : q ≤ 11 / 25) (hdq : d ≤ 1 - q) (hA : 0 ≤ A) (hA' : A ≤ 13 * q / (3 * E))
    (ht : |t| < 1) :
    -((1 / 5) * (q ^ 2 / E)) ≤
      endpointCoefficient d * barrier t + E * t * A / 2 + (13 * q / 6) * (tilt t - t) := by
  obtain ⟨hk, hsplit⟩ := split_bound hq hq'
  have hc0 := c0_pos hq
  have hcc := endpointCoefficient_ge_c0 hdq
  have hcpos : 0 < endpointCoefficient d := hc0.trans_le hcc
  have hloss : (40 / 11) * q ^ 2 ≤ (1 / 5) * (q ^ 2 / E) := by
    rw [mul_div_assoc', le_div_iff₀ hE]
    nlinarith [sq_nonneg q]
  have hti := abs_lt.mp ht
  by_cases ht0 : 0 ≤ t
  · have h1 : 0 ≤ endpointCoefficient d * barrier t := mul_nonneg hcpos.le (barrier_nonneg ht)
    have h2 : 0 ≤ E * t * A / 2 := by positivity
    have h3 : 0 ≤ (13 * q / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 hti.2))
    have h4 : 0 ≤ (1 / 5) * (q ^ 2 / E) := by positivity
    linarith
  · have htn : t < 0 := lt_of_not_ge ht0
    have hEA : E * A ≤ 13 * q / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hA'
      nlinarith
    have hlin : 13 * q / 3 * t ≤ E * A * t := mul_le_mul_of_nonpos_right hEA htn.le
    have hk2 : |13 * q / 6| < 2 * endpointCoefficient d := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    obtain ⟨_, hval, hmin⟩ := objective_minimum hcpos hk2
    have hs : |(-t)| < 1 := by rwa [abs_neg]
    have hobj := hmin (-t) hs
    rw [hval] at hobj
    have hk0 : |13 * q / 6| < 2 * c0 q := by rw [abs_of_nonneg (by positivity)]; exact hk
    have hanti := loss_antitone hc0 hcc hk0
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

end CKLaneN4
