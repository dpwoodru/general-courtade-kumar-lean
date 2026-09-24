import GeneralCK.PsiNormalizedLowEntropy

/-!
# The opposite-corner and opposite-boundary scalar owners are false

This file refutes, in the **scalar-owner form** only,

    ResidualPsiScalarOwner oppositeCornerResidualRegion,
    ResidualPsiScalarOwner oppositeBoundaryResidualRegion,

    oppositeCornerResidualRegion   a b E := 1/2 ≤ b ∧ a + 1 - b ≤ 1/8192,
    oppositeBoundaryResidualRegion a b E := 1/2 ≤ b ∧ a ≤ 1/268435456.

Both are refuted by explicit witnesses at which *every* hypothesis of
`ResidualPsiScalarOwner` holds — including the psi-active hypothesis
`phi < psi`, which is what rules out the vacuity shortcut — and at which the
conclusion `residualPsiScalarBound a b E ≤ interiorCost a b` fails.

The witness shape is the one introduced in `PsiNormalizedLowEntropy`:
`a = v - q`, `b = 1 - v`, so `H b = H v` exactly and `1 - a - b = q`, with `q`
pinned by the contact equation so that `radialContact q E = 9/20` and therefore
`F q E = q * J (9/20)` exactly.

This does **not** contradict the archived opposite-corner or boundary
mathematics.  It says that the three-variable reduction
`residualPsiScalarBound ≤ interiorCost` is too lossy to carry those regions:
the parent profile `eta (E + C q)` blows up as `E → 0` while `interiorCost a b`
stays bounded by `J a`.

Consequently `residualPsiScalarBound_le_interiorCost_of_oppositeCorner` in
`PsiBoundaryAnalyticBridge` is conditional on a **false** hypothesis, and is
therefore vacuous rather than usable.
-/

namespace GeneralCK
open Set

/-! ## 1. Generic witness lemmas

Both refutations use the same two lemmas, instantiated at different
`(v, q, E)`.  Nothing here is specific to a region. -/

/-- Every `ResidualPsiScalarOwner` hypothesis at the witness `(v - q, 1 - v, E)`,
given the psi-active hypothesis. -/
theorem witness_owner_hypotheses {v q E : ℝ}
    (hv0 : 0 < v) (hv2 : v < 1 / 2) (hq0 : 0 < q) (hvq : q < v)
    (hE0 : 0 < E) (h2E : 2 * E ≤ H v) (hq10 : q ≤ 1 / 10) (hE100 : E ≤ 1 / 100)
    (hactive : phi (((v - q) + (1 - v)) / 2) E < psi (((v - q) + (1 - v)) / 2) E) :
    0 < v - q ∧ v - q < 1 - v ∧ (1 : ℝ) - v < 1 ∧ (v - q) + (1 - v) ≤ 1 ∧ 0 < E ∧
      E ≤ (H (v - q) + H (1 - v)) / 2 ∧ 1 / 16 < (v - q) + (1 - v) ∧
      1 / 100 < H (((v - q) + (1 - v)) / 2) - E ∧
      phi (((v - q) + (1 - v)) / 2) E < psi (((v - q) + (1 - v)) / 2) E := by
  have ha0 : 0 < v - q := by linarith
  have hHb : H (1 - v) = H v := H_complement v
  have hHa0 : 0 ≤ H (v - q) := H_nonneg ha0.le (by linarith)
  have hmid : ((v - q) + (1 - v)) / 2 = (1 - q) / 2 := by ring
  have hpar := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
  have hdef : 1 - H ((1 - q) / 2) ≤ q ^ 2 := by nlinarith
  have hq2 : q ^ 2 ≤ 1 / 100 := by nlinarith
  refine ⟨ha0, by linarith, by linarith, by linarith, hE0, ?_, by linarith, ?_, hactive⟩
  · rw [hHb]; linarith
  · rw [hmid]; linarith

/-- The owner conclusion fails at the witness `(v - q, 1 - v, E)` whenever the
parent profile lower bound `pl` exceeds the cost bound `cp` plus the child
anchor bound `cc`. -/
theorem witness_violation {v w q E cp cc pl : ℝ}
    (hv0 : 0 < v) (hv2 : v < 1 / 2) (hq0 : 0 < q) (hvq : q < v)
    (hE0 : 0 < E) (h2E : 2 * E ≤ H v)
    (hw0 : 0 < w) (hw2 : w < 1 / 2) (hHw : H w ≤ 1 - H v)
    (hanchor : (1 - 2 * w) * J w ≤ cc)
    (hcost : interiorCost (v - q) (1 - v) ≤ cp)
    (hparent : pl ≤ eta (E + (1 - H ((1 - q) / 2))))
    (hgap : cp + cc < pl) :
    interiorCost (v - q) (1 - v) < residualPsiScalarBound (v - q) (1 - v) E := by
  have ha0 : 0 < v - q := by linarith
  have ha2 : v - q ≤ 1 / 2 := by linarith
  have hHb : H (1 - v) = H v := H_complement v
  have hHa : H (v - q) ≤ H v :=
    H_strictMonoOn.monotoneOn ⟨ha0.le, ha2⟩ ⟨hv0.le, hv2.le⟩ (by linarith)
  have hHa0 : 0 ≤ H (v - q) := H_nonneg ha0.le (by linarith)
  have hEcap : E ≤ (H (v - q) + H (1 - v)) / 2 := by rw [hHb]; linarith
  obtain ⟨h1, h2⟩ := residualPsi_profile_args_mem hHa0 hE0 hEcap
  have hrmax : 0 ≤ max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)) := le_max_left _ _
  have hm1 : (1 : ℝ) - ((H (v - q) + H (1 - v)) / 2 - E -
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith [h1.2], by linarith [h1.1]⟩
  have hm2 : (1 : ℝ) - ((H (v - q) + H (1 - v)) / 2 - E +
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith [h2.2], by linarith [h2.1]⟩
  have hanti := eta_antitoneOn hm2 hm1 (by linarith)
  have hwmem : H w ∈ Ioc (0 : ℝ) 1 := ⟨H_pos hw0 (by linarith), H_le_one _⟩
  have hHwle : H w ≤ 1 - ((H (v - q) + H (1 - v)) / 2 - E +
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) := by
    rcases le_total ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)) 0 with hc | hc
    · rw [max_eq_left hc, hHb]; linarith
    · rw [max_eq_right hc, hHb]; linarith
  have hchild : eta (1 - ((H (v - q) + H (1 - v)) / 2 - E +
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)))) ≤ cc := by
    have hetaw : eta (H w) = (1 - 2 * w) * J w := Comparison.eta_H hw0 hw2
    have hstep := eta_antitoneOn hwmem hm2 hHwle
    rw [hetaw] at hstep
    linarith
  have hrp : residualPsiScalarBound (v - q) (1 - v) E =
      Scalar.P (H (((v - q) + (1 - v)) / 2) - E) -
        (Scalar.P ((H (v - q) + H (1 - v)) / 2 - E -
            max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) +
          Scalar.P ((H (v - q) + H (1 - v)) / 2 - E +
            max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)))) / 2 := rfl
  have hPparent : Scalar.P (H (((v - q) + (1 - v)) / 2) - E) =
      eta (E + (1 - H ((1 - q) / 2))) := by
    rw [show ((v - q) + (1 - v)) / 2 = (1 - q) / 2 from by ring]
    show eta (1 - (H ((1 - q) / 2) - E)) = eta (E + (1 - H ((1 - q) / 2)))
    congr 1
    ring
  have hP1 : Scalar.P ((H (v - q) + H (1 - v)) / 2 - E -
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) =
      eta (1 - ((H (v - q) + H (1 - v)) / 2 - E -
        max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)))) := rfl
  have hP2 : Scalar.P ((H (v - q) + H (1 - v)) / 2 - E +
      max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q))) =
      eta (1 - ((H (v - q) + H (1 - v)) / 2 - E +
        max 0 ((H (v - q) + H (1 - v)) / 2 - E - H (v - q)))) := rfl
  rw [hrp, hPparent, hP1, hP2]
  linarith

/-! ## 2. The corner witness

`v = 2⁻¹⁴`, `E = H (2⁻²⁵)`, `q = nleQ`.  Then

    a + 1 - b = 2 * 2⁻¹⁴ - q = 2⁻¹³ - q < 1/8192,

so the witness sits inside `oppositeCornerResidualRegion`.  The cost is bounded
by `J` at the two dyadic ends and the parent profile is the already-certified
`eta (nleE + C q) ≥ 22.99`. -/

theorem H_pow14_ge : (8 : ℝ) / 10000 ≤ H (1 / 16384) := by
  have hp : (0 : ℝ) < 1 / 16384 := by norm_num
  have hp1 : (1 : ℝ) / 16384 < 1 := by norm_num
  have hlog : Real.log ((1 / 16384 : ℝ))⁻¹ = 14 * Real.log 2 :=
    log_inv_two_pow 14 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_pow14_le : H (1 / 16384) ≤ 1 / 1000 := by
  have hp : (0 : ℝ) < 1 / 16384 := by norm_num
  have hp1 : (1 : ℝ) / 16384 < 1 := by norm_num
  have hlog : Real.log ((1 / 16384 : ℝ))⁻¹ = 14 * Real.log 2 :=
    log_inv_two_pow 14 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem J_pow14_le : J (1 / 16384 : ℝ) ≤ 14 := by
  have := J_le_pow (u := (1 / 16384 : ℝ)) 14 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_pow14_shift_le : J (1 / 16384 - nleQ) ≤ 15 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hu : (0 : ℝ) < 1 / 16384 - nleQ := by linarith
  have hb : (1 - (1 / 16384 - nleQ)) / (1 / 16384 - nleQ) ≤ 2 ^ (15 : ℕ) := by
    rw [div_le_iff₀ hu]
    norm_num
    linarith
  have := J_le_pow (u := (1 / 16384 - nleQ)) 15 hu (by linarith) hb
  simpa using this

theorem J_pow14_shift_nonneg : 0 ≤ J (1 / 16384 - nleQ) := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  exact J_nonneg (by linarith) (by linarith)

theorem corner_cost : interiorCost (1 / 16384 - nleQ) (1 - 1 / 16384) ≤ 15 := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hJb : J (1 - 1 / 16384 : ℝ) = - J (1 / 16384 : ℝ) := J_complement _
  have hJ14 := J_pow14_le
  have hJa := J_pow14_shift_le
  have hJa0 := J_pow14_shift_nonneg
  have hJ140 : 0 ≤ J (1 / 16384 : ℝ) := J_nonneg (by norm_num) (by norm_num)
  unfold interiorCost
  rw [hJb]
  nlinarith

theorem corner_violation :
    interiorCost (1 / 16384 - nleQ) (1 - 1 / 16384) <
      residualPsiScalarBound (1 / 16384 - nleQ) (1 - 1 / 16384) nleE := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hE0 : 0 < nleE := nleE_pos
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  exact witness_violation (v := 1 / 16384) (w := 1 / 16) (q := nleQ) (E := nleE)
    (cp := 15) (cc := 4) (pl := 2299 / 100)
    (by norm_num) (by norm_num) hq0 (by linarith) hE0
    (by linarith [H_pow14_ge]) (by norm_num) (by norm_num)
    (by linarith [H_sixteenth_le, H_pow14_le]) nle_anchor8 corner_cost
    eta_parent_ge (by norm_num)

/-- **The scalar owner of the opposite corner is false.** -/
theorem not_residualPsiScalarOwner_oppositeCorner :
    ¬ ResidualPsiScalarOwner oppositeCornerResidualRegion := by
  intro hown
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hE0 : 0 < nleE := nleE_pos
  have hEle : nleE ≤ 78806 / 100000000000 := nleE_le
  have hmid : ((1 / 16384 - nleQ) + (1 - 1 / 16384)) / 2 = (1 - nleQ) / 2 := by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    witness_owner_hypotheses (v := 1 / 16384) (q := nleQ) (E := nleE)
      (by norm_num) (by norm_num) hq0 (by linarith) hE0
      (by linarith [H_pow14_ge]) (by linarith) (by linarith) (nle_active hmid)
  have hregion : oppositeCornerResidualRegion (1 / 16384 - nleQ) (1 - 1 / 16384) nleE :=
    ⟨by norm_num, by linarith⟩
  have hconc := hown (1 / 16384 - nleQ) (1 - 1 / 16384) nleE h1 h2 h3 h4 h5 h6 h7 h8
    hregion h9
  linarith [corner_violation]

/-! ## 3. The boundary witness

The boundary region forces `a ≤ 2⁻²⁸`, hence `J a ≥ 28`, hence a cost near `28`.
The corner witness of section 2 is therefore too weak, and a smaller entropy
anchor is used: `E = H (2⁻⁴⁰)`, giving a parent profile near `40`.

    a = 2⁻²⁸,  q = cbQ,  v = q + 2⁻²⁸,  b = 1 - v = 1 - q - 2⁻²⁸.

This witness lies in `oppositeBoundaryResidualRegion` **and** in
`oppositeCornerResidualRegion`. -/

theorem log_pow39 : Real.log 549755813888 = 39 * Real.log 2 := by
  have h : (549755813888 : ℝ) = 2 ^ (39 : ℕ) := by norm_num
  rw [h, Real.log_pow]
  norm_num

theorem log_pow40 : Real.log 1099511627776 = 40 * Real.log 2 := by
  have h : (1099511627776 : ℝ) = 2 ^ (40 : ℕ) := by norm_num
  rw [h, Real.log_pow]
  norm_num

theorem H_pow28_ge : (1 : ℝ) / 10000000 ≤ H (1 / 268435456) := by
  have hp : (0 : ℝ) < 1 / 268435456 := by norm_num
  have hp1 : (1 : ℝ) / 268435456 < 1 := by norm_num
  have hlog : Real.log ((1 / 268435456 : ℝ))⁻¹ = 28 * Real.log 2 :=
    log_inv_two_pow 28 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_pow39_ge : (7356483 : ℝ) / 100000000000000000 ≤ H (1 / 549755813888) := by
  have hp : (0 : ℝ) < 1 / 549755813888 := by norm_num
  have hp1 : (1 : ℝ) / 549755813888 < 1 := by norm_num
  have hlog : Real.log ((1 / 549755813888 : ℝ))⁻¹ = 39 * Real.log 2 :=
    log_inv_two_pow 39 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_pow40_ge : (3769191 : ℝ) / 100000000000000000 ≤ H (1 / 1099511627776) := by
  have hp : (0 : ℝ) < 1 / 1099511627776 := by norm_num
  have hp1 : (1 : ℝ) / 1099511627776 < 1 := by norm_num
  have hlog : Real.log ((1 / 1099511627776 : ℝ))⁻¹ = 40 * Real.log 2 :=
    log_inv_two_pow 40 _ (by norm_num)
  have h := H_mul_log_two_ge hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, log_two_pos']

theorem H_pow40_le : H (1 / 1099511627776) ≤ 3769192 / 100000000000000000 := by
  have hp : (0 : ℝ) < 1 / 1099511627776 := by norm_num
  have hp1 : (1 : ℝ) / 1099511627776 < 1 := by norm_num
  have hlog : Real.log ((1 / 1099511627776 : ℝ))⁻¹ = 40 * Real.log 2 :=
    log_inv_two_pow 40 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem H_pow41_le : H (1 / 2199023255552) ≤ 1930071 / 100000000000000000 := by
  have hp : (0 : ℝ) < 1 / 2199023255552 := by norm_num
  have hp1 : (1 : ℝ) / 2199023255552 < 1 := by norm_num
  have hlog : Real.log ((1 / 2199023255552 : ℝ))⁻¹ = 41 * Real.log 2 :=
    log_inv_two_pow 41 _ (by norm_num)
  have h := H_mul_log_two_le hp hp1
  rw [hlog] at h
  nlinarith [log_two_lower, log_two_upper, H_nonneg hp.le hp1.le, log_two_pos']

theorem J_pow40_ge : (39999999 : ℝ) / 1000000 ≤ J (1 / 1099511627776) := by
  have hval : ((1 - 1 / 1099511627776) / (1 / 1099511627776) : ℝ) = 1099511627775 := by
    norm_num
  have hgap : Real.log 1099511627776 - Real.log 1099511627775 ≤ 1 / 1099511627775 := by
    have h := Real.log_le_sub_one_of_pos
      (x := (1099511627776 : ℝ) / 1099511627775) (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    have he : (1099511627776 : ℝ) / 1099511627775 - 1 = 1 / 1099511627775 := by norm_num
    linarith [he ▸ h]
  unfold J
  rw [hval, le_div_iff₀ log_two_pos']
  nlinarith [log_two_lower, log_two_upper, log_pow40]

theorem J_pow40_le : J (1 / 1099511627776 : ℝ) ≤ 40 := by
  have := J_le_pow (u := (1 / 1099511627776 : ℝ)) 40 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_pow41_le : J (1 / 2199023255552 : ℝ) ≤ 41 := by
  have := J_le_pow (u := (1 / 2199023255552 : ℝ)) 41 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_pow41_nonneg : 0 ≤ J (1 / 2199023255552 : ℝ) :=
  J_nonneg (by norm_num) (by norm_num)

theorem J_pow39_ge : (38 : ℝ) ≤ J (1 / 549755813888) := by
  have := J_ge_pow (u := (1 / 549755813888 : ℝ)) 38 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_pow28_le : J (1 / 268435456 : ℝ) ≤ 28 := by
  have := J_le_pow (u := (1 / 268435456 : ℝ)) 28 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

/-- The boundary entropy anchor `E = H (2⁻⁴⁰)`. -/
noncomputable def cbE : ℝ := H (1 / 1099511627776)

/-- The boundary mean gap, pinned by the contact equation at `9/20`. -/
noncomputable def cbQ : ℝ := cbE / (10 * H (9 / 20))

theorem cbE_ge : (3769191 : ℝ) / 100000000000000000 ≤ cbE := H_pow40_ge
theorem cbE_le : cbE ≤ 3769192 / 100000000000000000 := H_pow40_le
theorem cbE_pos : 0 < cbE := by have := cbE_ge; unfold cbE at *; linarith

theorem cbQ_pos : 0 < cbQ := by
  apply div_pos cbE_pos
  linarith [H920_gt]

theorem cbQ_mul : cbQ * H (9 / 20) = cbE / 10 := by
  have h : H (9 / 20) ≠ 0 := ne_of_gt (by linarith [H920_gt] : (0 : ℝ) < H (9 / 20))
  unfold cbQ
  field_simp

theorem cbQ_le : cbQ ≤ 3808 / 1000000000000000 := by
  have h1 : (99 : ℝ) / 100 < H (9 / 20) := H920_gt
  have h2 := cbE_le
  have h3 : (0 : ℝ) < 10 * H (9 / 20) := by linarith
  unfold cbQ
  rw [div_le_iff₀ h3]
  nlinarith [cbE_pos]

theorem cb_radialContact : radialContact cbQ cbE = 9 / 20 := by
  refine radialContact_eq_of_equation cbQ_pos cbE_pos (by norm_num) (by norm_num) ?_
  have hten : cbE * (1 - 2 * (9 / 20 : ℝ)) = cbE / 10 := by ring
  rw [cbQ_mul, hten]

theorem cb_F : F cbQ cbE = cbQ * J (9 / 20) := by
  simp only [F, if_neg (ne_of_gt cbQ_pos), cb_radialContact]

theorem eta_cbE_ge : (39999998 : ℝ) / 1000000 ≤ eta cbE := by
  have h : eta (H (1 / 1099511627776)) =
      (1 - 2 * (1 / 1099511627776)) * J (1 / 1099511627776) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  unfold cbE
  rw [h]
  nlinarith [J_pow40_ge, J_pow40_le]

theorem eta_pow41_le : eta (H (1 / 2199023255552)) ≤ 41 := by
  have h : eta (H (1 / 2199023255552)) =
      (1 - 2 * (1 / 2199023255552)) * J (1 / 2199023255552) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  rw [h]
  nlinarith [J_pow41_le, J_pow41_nonneg]

theorem eta_pow39_ge : (3799 : ℝ) / 100 ≤ eta (H (1 / 549755813888)) := by
  have h : eta (H (1 / 549755813888)) =
      (1 - 2 * (1 / 549755813888)) * J (1 / 549755813888) :=
    Comparison.eta_H (by norm_num) (by norm_num)
  rw [h]
  nlinarith [J_pow39_ge]

theorem cb_parentDefect_pos : 0 < 1 - H ((1 - cbQ) / 2) := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have h := H_strictMonoOn (a := (1 - cbQ) / 2) (b := 1 / 2)
    ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
  rw [H_half] at h
  linarith

theorem cb_parentDefect : 1 - H ((1 - cbQ) / 2) ≤ cbQ ^ 2 := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have h := H_gt_parabola (p := (1 - cbQ) / 2) (by linarith) (by linarith)
  nlinarith

theorem eta_cbparent_ge : (3799 : ℝ) / 100 ≤ eta (cbE + (1 - H ((1 - cbQ) / 2))) := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hc := cb_parentDefect
  have hc0 := cb_parentDefect_pos
  have hE0 : 0 < cbE := cbE_pos
  have hEle := cbE_le
  have hB := H_pow39_ge
  have hA : cbE + (1 - H ((1 - cbQ) / 2)) ≤ H (1 / 549755813888) := by nlinarith
  have hA0 : 0 < cbE + (1 - H ((1 - cbQ) / 2)) := by linarith
  have hA1 : cbE + (1 - H ((1 - cbQ) / 2)) ≤ 1 := by nlinarith
  have hB0 : 0 < H (1 / 549755813888) := H_pos (by norm_num) (by norm_num)
  have hB1 : H (1 / 549755813888) ≤ 1 := H_le_one _
  exact le_trans eta_pow39_ge (eta_antitoneOn ⟨hA0, hA1⟩ ⟨hB0, hB1⟩ hA)

/-- The parent is psi-active at the boundary witness. -/
theorem cb_active {m : ℝ} (hm : m = (1 - cbQ) / 2) : phi m cbE < psi m cbE := by
  subst hm
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hEge := cbE_ge
  have hEle := cbE_le
  have hE0 : 0 < cbE := cbE_pos
  have habs : |1 - 2 * ((1 - cbQ) / 2)| = cbQ := by
    rw [show (1 : ℝ) - 2 * ((1 - cbQ) / 2) = cbQ by ring, abs_of_pos hq0]
  have hm2 : (1 - cbQ) / 2 < 1 / 2 := by linarith
  have hm0 : 0 < (1 - cbQ) / 2 := by linarith
  have hc0 := cb_parentDefect_pos
  have hcq := cb_parentDefect
  set p' := H (1 / 2199023255552) with hp'
  have hp'0 : 0 < p' := H_pos (by norm_num) (by norm_num)
  have hp'1 : p' ≤ 1 := H_le_one _
  have hp'le : p' ≤ 1930071 / 100000000000000000 := H_pow41_le
  have hD : 0 < cbE - p' := by linarith
  have hDge : (1839119 : ℝ) / 100000000000000000 ≤ cbE - p' := by linarith
  have hz1 : cbE + (1 - H ((1 - cbQ) / 2)) ≤ 1 := by nlinarith
  have hslope := (Scalar.eta_convexOn_Ioc).slope_mono_adjacent
    (x := p') (z := cbE + (1 - H ((1 - cbQ) / 2))) ⟨hp'0, hp'1⟩ ⟨by linarith, hz1⟩
    (show p' < cbE by linarith) (show cbE < cbE + (1 - H ((1 - cbQ) / 2)) by linarith)
  rw [show cbE + (1 - H ((1 - cbQ) / 2)) - cbE = 1 - H ((1 - cbQ) / 2) by ring] at hslope
  rw [div_le_div_iff₀ hD hc0] at hslope
  have hN : eta p' - eta cbE ≤ 1000002 / 1000000 := by
    have h1 : eta p' ≤ 41 := by rw [hp']; exact eta_pow41_le
    have h2 := eta_cbE_ge
    linarith
  have hX : (eta cbE - eta (cbE + (1 - H ((1 - cbQ) / 2)))) * (cbE - p') ≤
      (1000002 / 1000000) * cbQ ^ 2 := by
    nlinarith [hslope, hcq, hc0, hN]
  have hJ := J920_ge
  have hkey : (eta cbE - eta (cbE + (1 - H ((1 - cbQ) / 2)))) * (cbE - p') <
      (cbQ * J (9 / 20)) * (cbE - p') := by
    have hstep : (1000002 / 1000000 : ℝ) * cbQ ^ 2 < (cbQ * J (9 / 20)) * (cbE - p') := by
      have hsq : cbQ ^ 2 ≤ (3808 / 1000000000000000 : ℝ) * cbQ := by
        nlinarith [mul_le_mul_of_nonneg_left hqle hq0.le]
      have hJ0 : (0 : ℝ) ≤ cbQ * J (9 / 20) := mul_nonneg hq0.le (by linarith)
      have hB : (cbQ * (2895 / 10000 : ℝ)) * (1839119 / 100000000000000000) ≤
          (cbQ * J (9 / 20)) * (cbE - p') :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJ hq0.le) hDge (by norm_num) hJ0
      linarith
    linarith
  have hfinal : eta cbE - eta (cbE + (1 - H ((1 - cbQ) / 2))) < cbQ * J (9 / 20) :=
    lt_of_mul_lt_mul_right hkey hD.le
  unfold phi psi
  rw [habs, cb_F]
  rw [show cbE + 1 - H ((1 - cbQ) / 2) = cbE + (1 - H ((1 - cbQ) / 2)) by ring]
  linarith

/-! ### The boundary witness violates the owner conclusion -/

theorem boundary_H_v_ge : (1 : ℝ) / 10000000 ≤ H (cbQ + 1 / 268435456) := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hmono := H_strictMonoOn.monotoneOn (a := (1 / 268435456 : ℝ))
    (b := cbQ + 1 / 268435456) ⟨by norm_num, by norm_num⟩
    ⟨by linarith, by linarith⟩ (by linarith)
  linarith [H_pow28_ge]

theorem boundary_H_v_le : H (cbQ + 1 / 268435456) ≤ 3402 / 10000 := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hmono := H_strictMonoOn.monotoneOn (a := cbQ + 1 / 268435456) (b := (1 / 16 : ℝ))
    ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith)
  linarith [H_sixteenth_le]

theorem J_boundary_shift_le : J (cbQ + 1 / 268435456) ≤ 28 := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hu : (0 : ℝ) < cbQ + 1 / 268435456 := by linarith
  have hb : (1 - (cbQ + 1 / 268435456)) / (cbQ + 1 / 268435456) ≤ 2 ^ (28 : ℕ) := by
    rw [div_le_iff₀ hu]
    norm_num
    linarith
  have := J_le_pow (u := cbQ + 1 / 268435456) 28 hu (by linarith) hb
  simpa using this

theorem J_boundary_shift_nonneg : 0 ≤ J (cbQ + 1 / 268435456) := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  exact J_nonneg (by linarith) (by linarith)

theorem boundary_cost :
    interiorCost (cbQ + 1 / 268435456 - cbQ) (1 - (cbQ + 1 / 268435456)) ≤ 28 := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  rw [show cbQ + 1 / 268435456 - cbQ = (1 : ℝ) / 268435456 from by ring]
  have hJb : J (1 - (cbQ + 1 / 268435456)) = - J (cbQ + 1 / 268435456) :=
    J_complement _
  have hJa := J_pow28_le
  have hJa0 : 0 ≤ J (1 / 268435456 : ℝ) := J_nonneg (by norm_num) (by norm_num)
  have hJv := J_boundary_shift_le
  have hJv0 := J_boundary_shift_nonneg
  unfold interiorCost
  rw [hJb]
  nlinarith

theorem boundary_violation :
    interiorCost (cbQ + 1 / 268435456 - cbQ) (1 - (cbQ + 1 / 268435456)) <
      residualPsiScalarBound (cbQ + 1 / 268435456 - cbQ)
        (1 - (cbQ + 1 / 268435456)) cbE := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hE0 : 0 < cbE := cbE_pos
  have hEle := cbE_le
  exact witness_violation (v := cbQ + 1 / 268435456) (w := 1 / 16) (q := cbQ) (E := cbE)
    (cp := 28) (cc := 4) (pl := 3799 / 100)
    (by linarith) (by linarith) hq0 (by linarith) hE0
    (by linarith [boundary_H_v_ge]) (by norm_num) (by norm_num)
    (by linarith [H_sixteenth_le, boundary_H_v_le]) nle_anchor8 boundary_cost
    eta_cbparent_ge (by norm_num)

/-- The same violation with the witness in normal form:
`a = 2⁻²⁸`, `b = 1 - cbQ - 2⁻²⁸`, `E = H (2⁻⁴⁰)`. -/
theorem boundary_violation' :
    interiorCost (1 / 268435456) (1 - cbQ - 1 / 268435456) <
      residualPsiScalarBound (1 / 268435456) (1 - cbQ - 1 / 268435456) cbE := by
  have h := boundary_violation
  rw [show cbQ + 1 / 268435456 - cbQ = (1 : ℝ) / 268435456 from by ring,
    show 1 - (cbQ + 1 / 268435456) = 1 - cbQ - (1 : ℝ) / 268435456 from by ring] at h
  exact h

/-- **The scalar owner of the opposite boundary is false.** -/
theorem not_residualPsiScalarOwner_oppositeBoundary :
    ¬ ResidualPsiScalarOwner oppositeBoundaryResidualRegion := by
  intro hown
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hE0 : 0 < cbE := cbE_pos
  have hEle := cbE_le
  have hmid : ((cbQ + 1 / 268435456 - cbQ) + (1 - (cbQ + 1 / 268435456))) / 2 =
      (1 - cbQ) / 2 := by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    witness_owner_hypotheses (v := cbQ + 1 / 268435456) (q := cbQ) (E := cbE)
      (by linarith) (by linarith) hq0 (by linarith) hE0
      (by linarith [boundary_H_v_ge]) (by linarith) (by linarith) (cb_active hmid)
  have hregion : oppositeBoundaryResidualRegion (cbQ + 1 / 268435456 - cbQ)
      (1 - (cbQ + 1 / 268435456)) cbE := ⟨by linarith, by linarith⟩
  have hconc := hown (cbQ + 1 / 268435456 - cbQ) (1 - (cbQ + 1 / 268435456)) cbE
    h1 h2 h3 h4 h5 h6 h7 h8 hregion h9
  linarith [boundary_violation]

/-- The same witness also refutes the corner owner, independently of section 2. -/
theorem not_residualPsiScalarOwner_oppositeCorner' :
    ¬ ResidualPsiScalarOwner oppositeCornerResidualRegion := by
  intro hown
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  have hE0 : 0 < cbE := cbE_pos
  have hEle := cbE_le
  have hmid : ((cbQ + 1 / 268435456 - cbQ) + (1 - (cbQ + 1 / 268435456))) / 2 =
      (1 - cbQ) / 2 := by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    witness_owner_hypotheses (v := cbQ + 1 / 268435456) (q := cbQ) (E := cbE)
      (by linarith) (by linarith) hq0 (by linarith) hE0
      (by linarith [boundary_H_v_ge]) (by linarith) (by linarith) (cb_active hmid)
  have hregion : oppositeCornerResidualRegion (cbQ + 1 / 268435456 - cbQ)
      (1 - (cbQ + 1 / 268435456)) cbE := ⟨by linarith, by linarith⟩
  have hconc := hown (cbQ + 1 / 268435456 - cbQ) (1 - (cbQ + 1 / 268435456)) cbE
    h1 h2 h3 h4 h5 h6 h7 h8 hregion h9
  linarith [boundary_violation]

/-! ## 4. Negative controls

Deliberate *failures*, to check that the witnesses are tested against the real
region predicates and that the two refutations are independent. -/

theorem J_pow14_ge : (13 : ℝ) ≤ J (1 / 16384) := by
  have := J_ge_pow (u := (1 / 16384 : ℝ)) 13 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

theorem J_pow28_ge : (27 : ℝ) ≤ J (1 / 268435456) := by
  have := J_ge_pow (u := (1 / 268435456 : ℝ)) 27 (by norm_num) (by norm_num) (by norm_num)
  simpa using this

/-- The section-2 corner witness is **not** in the boundary region: its `a` is
`2⁻¹⁴ - q`, far above `2⁻²⁸`.  Section 3 is therefore not redundant. -/
theorem corner_witness_not_in_boundary :
    ¬ oppositeBoundaryResidualRegion (1 / 16384 - nleQ) (1 - 1 / 16384) nleE := by
  rintro ⟨-, h⟩
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  linarith

/-- Neither witness is in the same-side region. -/
theorem corner_witness_not_sameSide :
    ¬ sameSideResidualRegion (1 / 16384 - nleQ) (1 - 1 / 16384) nleE := by
  rintro ⟨h, -⟩
  norm_num at h

theorem boundary_witness_not_sameSide :
    ¬ sameSideResidualRegion (cbQ + 1 / 268435456 - cbQ)
        (1 - (cbQ + 1 / 268435456)) cbE := by
  rintro ⟨h, -⟩
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  linarith

/-- The cost at the corner witness is strictly positive: the violation is not
an artefact of a degenerate cost. -/
theorem corner_cost_pos : 0 < interiorCost (1 / 16384 - nleQ) (1 - 1 / 16384) := by
  have hq0 : 0 < nleQ := nleQ_pos
  have hqle : nleQ ≤ 79603 / 1000000000000 := nleQ_le
  have hJb : J (1 - 1 / 16384 : ℝ) = - J (1 / 16384 : ℝ) := J_complement _
  have hJ14 := J_pow14_ge
  have hJa0 := J_pow14_shift_nonneg
  unfold interiorCost
  rw [hJb]
  nlinarith

/-- The cost at the boundary witness is strictly positive. -/
theorem boundary_cost_pos :
    0 < interiorCost (cbQ + 1 / 268435456 - cbQ) (1 - (cbQ + 1 / 268435456)) := by
  have hq0 : 0 < cbQ := cbQ_pos
  have hqle : cbQ ≤ 3808 / 1000000000000000 := cbQ_le
  rw [show cbQ + 1 / 268435456 - cbQ = (1 : ℝ) / 268435456 from by ring]
  have hJb : J (1 - (cbQ + 1 / 268435456)) = - J (cbQ + 1 / 268435456) := J_complement _
  have hJa := J_pow28_ge
  have hJv0 := J_boundary_shift_nonneg
  unfold interiorCost
  rw [hJb]
  nlinarith

/-- Both witnesses really are psi-active; neither refutation is a vacuity
artefact.  (Restated for the record; this is the hypothesis that the
factor-eight vacuity shortcut cannot supply.) -/
theorem witnesses_are_psi_active :
    phi ((1 - nleQ) / 2) nleE < psi ((1 - nleQ) / 2) nleE ∧
      phi ((1 - cbQ) / 2) cbE < psi ((1 - cbQ) / 2) cbE :=
  ⟨nle_active rfl, cb_active rfl⟩

#print axioms corner_witness_not_in_boundary
#print axioms corner_cost_pos
#print axioms boundary_cost_pos
#print axioms witnesses_are_psi_active

#print axioms cbE_ge
#print axioms cbQ_le
#print axioms cb_radialContact
#print axioms eta_cbE_ge
#print axioms eta_cbparent_ge
#print axioms cb_active
#print axioms boundary_cost
#print axioms boundary_violation
#print axioms boundary_violation'
#print axioms not_residualPsiScalarOwner_oppositeBoundary
#print axioms not_residualPsiScalarOwner_oppositeCorner'

#print axioms witness_owner_hypotheses
#print axioms witness_violation
#print axioms H_pow14_ge
#print axioms H_pow14_le
#print axioms corner_cost
#print axioms corner_violation
#print axioms not_residualPsiScalarOwner_oppositeCorner

end GeneralCK
