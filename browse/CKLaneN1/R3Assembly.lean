import CKLaneN1.R3Excl

/-!
# Lane N1 — CE-stat row 3: assembly of `TransverseCurvatureOwner` from the numeric cover

`CoverStmt` is the stationarity-free statement the numeric cover (M07) certifies on the normalized
domain `2^-17 ≤ a < 1/100` in coordinates `(a, z, y)`, `b = a + z y`, `c = a + y`.

* `transverse_of_cover : CoverStmt → TransverseCurvatureOwner` — every row-3 point satisfies the
  cover hypotheses (`a_lower`, `b < t_C ≤ 1/100`, `A ≤ 1/20`, retained cutoff), and
  `canonicalPureGap ≥ gapLB` (M07 `gapLB_le`, no stationarity used).
* `cover_of_octaves` — the octave dispatch: `CoverStmt` from `Sem` on the dyadic octave roots
  `[2^-k, 2^-(k-1)] × [0,1] × [0, Y_k]` together with the height exclusion `y_upper`.

Both are CONDITIONAL adapters; the closure instantiates them with the compiled cover.
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK CKLaneN1 CKLaneE.FP GeneralCK.SmallMeanPhiCutoff

/-- the stationarity-free statement of the numeric cover -/
def CoverStmt : Prop :=
  ∀ a z y : ℝ, 1 / 131072 ≤ a → a < 1 / 100 → 0 < z → z < 1 → 0 < y → a + y < 1 / 2 →
    y ≤ (H a + H (a + z * y)) / 20 → 1 / 10000 < 2 * a + y → a + z * y < 1 / 100 →
    0 ≤ CKLaneM07.CE.gapLB (H a) (H (a + z * y)) (a + y)

theorem retainedCutoff_eq : retainedCutoff = 1 / 10000 := rfl

/-- **Row-3 assembly** (conditional on the cover). -/
theorem transverse_of_cover (hcov : CoverStmt) : CKLaneN1.CEStat.TransverseCurvatureOwner := by
  intro e f c hp _h1 h2 hA
  obtain ⟨hpf, hret⟩ := hp
  have hpf' := hpf
  obtain ⟨he, hef, hf, hbc, hc, _hs⟩ := hpf'
  have hlb := CKLaneM07.CE.gapLB_le hpf
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < entropyInverse e := entropyInverse_pos he (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f := entropyInverse_strictMonoOn
    ⟨he.le, hef.le.trans hf⟩ ⟨(he.trans hef).le, hf⟩ hef
  have htc := CKLaneN1.CEStat.chart_order hpf
  have hb100 : entropyInverse f < 1 / 100 := lt_of_lt_of_le htc.1 h2
  set a := entropyInverse e with ha_def
  set b := entropyInverse f with hb_def
  have hEF : 0 < e + f := by linarith
  have hA' : c - a ≤ (H a + H b) / 20 := by
    unfold CKLaneN1.CEStat.chartA at hA
    rw [← ha_def, div_le_iff₀ hEF] at hA
    rw [hie.2.2, hif.2.2]
    linarith
  have hret' : 1 / 10000 < a + c := by rw [retainedCutoff_eq] at hret; linarith
  have hlo := a_lower ha hab hbc hc hret' hA'
  have hlo' : (1 : ℝ) / 131072 ≤ a := by
    have : ((alo : ℚ) : ℝ) = 1 / 131072 := by simp [alo]
    linarith
  have hy : 0 < c - a := by linarith
  set y := c - a with hy_def
  set z := (b - a) / y with hz_def
  have hz0 : 0 < z := div_pos (by linarith) hy
  have hz1 : z < 1 := by rw [hz_def, div_lt_one hy]; linarith
  have hbz : a + z * y = b := by rw [hz_def]; field_simp; ring
  have hcy : a + y = c := by rw [hy_def]; ring
  have key := hcov a z y hlo' (by linarith) hz0 hz1 hy (by linarith) (by rw [hbz]; linarith)
    (by linarith) (by rw [hbz]; exact hb100)
  rw [hbz, hcy, hie.2.2, hif.2.2] at key
  linarith

/-! ## Octave dispatch -/

/-- the octave root box `[a₀, a₁] × [0,1] × [0, Y]` -/
def octBox (a0 a1 Y : ℚ) : B3 := ⟨a0, a1, 0, 1, 0, Y⟩

/-- one octave: the cover on the root box, plus the height exclusion for its `Y` -/
theorem cover_octave {a0 a1 Y : ℚ} (hsem : Sem (octBox a0 a1 Y)) (hup : yupOK a1 Y = true)
    {a z y : ℝ} (ha0 : (a0 : ℝ) ≤ a) (ha1 : a ≤ (a1 : ℝ)) (hapos : 0 < a) (hz0 : 0 < z)
    (hz1 : z < 1) (hy : 0 < y) (hc : a + y < 1 / 2) (hA : y ≤ (H a + H (a + z * y)) / 20)
    (hret : 1 / 10000 < 2 * a + y) (htc : a + z * y < 1 / 100) :
    0 ≤ CKLaneM07.CE.gapLB (H a) (H (a + z * y)) (a + y) := by
  have hzy : z * y < y := by nlinarith
  have hYy := y_upper hup hapos ha1 hy (by nlinarith : a < a + z * y) (by linarith) hc hA
  refine hsem a z y ⟨ha0, ha1, ?_, ?_, ?_, hYy⟩ hz0 hz1 hy hA hret htc
  · simp [octBox]; exact hz0.le
  · simp [octBox]; exact hz1.le
  · simp [octBox]; exact hy.le

end CKLaneN1.R3
