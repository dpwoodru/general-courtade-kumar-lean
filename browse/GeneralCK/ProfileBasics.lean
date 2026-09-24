import GeneralCK.BellmanStatement

namespace GeneralCK

theorem H_strictMonoOn : StrictMonoOn H (Set.Icc 0 (1 / 2)) := by
  intro a ha b hb hab
  exact div_lt_div_of_pos_right
    (Real.binEntropy_strictMonoOn (by simpa using ha) (by simpa using hb) hab)
    log_two_pos

theorem H_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) : 0 < H p :=
  div_pos (Real.binEntropy_pos hp hp') log_two_pos

theorem entropyInverse_H_lower {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    entropyInverse (H v) = v := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun _ hx => hx.1⟩
    · exact ⟨hv, hv', le_rfl⟩
  · apply le_csInf
    · exact ⟨v, hv, hv', le_rfl⟩
    · intro b hb
      by_contra hn
      have := H_strictMonoOn ⟨hb.1, hb.2.1⟩ ⟨hv, hv'⟩ (lt_of_not_ge hn)
      exact (not_lt_of_ge hb.2.2) this

theorem entropyInverse_H {m : ℝ} (hm : 0 ≤ m) (hm' : m ≤ 1) :
    entropyInverse (H m) = min m (1 - m) := by
  by_cases hl : m ≤ 1 / 2
  · rw [entropyInverse_H_lower hm hl, min_eq_left (by linarith)]
  · rw [← H_complement m, entropyInverse_H_lower (by linarith) (by linarith),
      min_eq_right (by linarith)]

@[simp] theorem eta_one : eta 1 = 0 := by simp [eta]

theorem radialContact_H_lower {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    radialContact (1 - 2 * v) (H v) = v := by
  have hHv : 0 < H v := H_pos hv (by linarith)
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧
      (1 - 2 * v) * H u = H v * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hu', heq⟩
      rcases lt_trichotomy u v with h | h | h
      · have hH := H_strictMonoOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ h
        have hmul : (1 - 2 * v) * H u < (1 - 2 * v) * H v :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * v) < H v * (1 - 2 * u) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
      · exact h
      · have hH := H_strictMonoOn ⟨hv.le, hv'.le⟩ ⟨hu.le, hu'.le⟩ h
        have hmul : (1 - 2 * v) * H v < (1 - 2 * v) * H u :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * u) < H v * (1 - 2 * v) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
    · rintro rfl
      exact ⟨hv, hv', mul_comm _ _⟩
  unfold radialContact
  rw [hset, csInf_singleton]

theorem B_H_lower {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1 / 2) : B m (H m) = 0 := by
  by_cases heq : m = 1 / 2
  · subst m
    norm_num [B, phi, psi, F, eta_one]
  · have hlt : m < 1 / 2 := lt_of_le_of_ne hm' heq
    have hH : H m < 1 := by
      calc H m < H (1 / 2) := H_strictMonoOn ⟨hm.le, hm'⟩ ⟨by norm_num, le_rfl⟩ hlt
           _ = 1 := H_half
    have hz : |1 - 2 * m| = 1 - 2 * m := abs_of_pos (by linarith)
    have hz' : 1 - 2 * m ≠ 0 := by linarith
    simp [B, phi, psi, eta, ne_of_lt hH, entropyInverse_H_lower hm.le hm',
      hz, F, hz', radialContact_H_lower hm hlt]

theorem B_complement (m h : ℝ) : B (1 - m) h = B m h := by
  have hz : |1 - 2 * (1 - m)| = |1 - 2 * m| := by
    rw [show 1 - 2 * (1 - m) = -(1 - 2 * m) by ring, abs_neg]
  simp only [B, phi, psi, H_complement, hz]

theorem B_H {m : ℝ} (hm : 0 < m) (hm' : m < 1) : B m (H m) = 0 := by
  by_cases hl : m ≤ 1 / 2
  · exact B_H_lower hm hl
  · rw [← B_complement m (H m), ← H_complement m]
    exact B_H_lower (by linarith) (by linarith)

end GeneralCK
