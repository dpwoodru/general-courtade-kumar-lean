import GeneralCK.PsiSameSideTail8SmallMeanRegionClosure

/-!
# Lane E: chart hypotheses, boxes and the coverage predicate

`ChartHyp μ` bundles exactly the premises of `GeneralCK.SameSidePsiTail8SmallMeanChartOwner`.
A `Box3` is a rational box in the law coordinates `(a/b, b, meanEntropy)`, and
`Good B` states the owner's conclusion for every chart law in `B`.  Splitting a box at any
rational value on any axis preserves `Good` (no side condition), so a finite binary tree of
certified leaves proves `Good` of its root.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.Chart

open GeneralCK

structure ChartHyp {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop where
  hab : μ.a < μ.b
  hsum : μ.a + μ.b < 1
  hmean : 1 / 16 < μ.a + μ.b
  hinfo : 1 / 100 < μ.information
  hE : 1 / 1000000 < μ.meanEntropy
  hside : μ.b ≤ 1 / 2
  hratio : 1 / 32768 < μ.a / μ.b
  hstrip : μ.b ≤ 17 / 40 → 1 / 16384 < μ.a / μ.b
  hsmall : μ.a + μ.b ≤ 1 / 4 → 1 / 256 < μ.a / μ.b
  hactive : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

structure Box3 where
  r1 : ℚ
  r2 : ℚ
  b1 : ℚ
  b2 : ℚ
  E1 : ℚ
  E2 : ℚ
  deriving Repr, DecidableEq

def InBox (B : Box3) {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  (B.r1 : ℝ) ≤ μ.a / μ.b ∧ μ.a / μ.b ≤ (B.r2 : ℝ) ∧ (B.b1 : ℝ) ≤ μ.b ∧ μ.b ≤ (B.b2 : ℝ) ∧
    (B.E1 : ℝ) ≤ μ.meanEntropy ∧ μ.meanEntropy ≤ (B.E2 : ℝ)

def Good (B : Box3) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), ChartHyp μ → InBox B μ → μ.gap ≤ μ.cost

/-- Lower / upper halves of a box at value `c` on axis `ax` (0 = ratio, 1 = b, 2 = entropy). -/
def Box3.lower (B : Box3) (ax : ℕ) (c : ℚ) : Box3 :=
  if ax = 0 then { B with r2 := c } else if ax = 1 then { B with b2 := c } else { B with E2 := c }

def Box3.upper (B : Box3) (ax : ℕ) (c : ℚ) : Box3 :=
  if ax = 0 then { B with r1 := c } else if ax = 1 then { B with b1 := c } else { B with E1 := c }

theorem good_split (B : Box3) (ax : ℕ) (c : ℚ) (hl : Good (B.lower ax c))
    (hu : Good (B.upper ax c)) : Good B := by
  intro k μ hμ hin
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  by_cases h0 : ax = 0
  · subst h0
    rcases le_total (μ.a / μ.b) (c : ℝ) with hc | hc
    · exact hl k μ hμ (by simp only [Box3.lower, if_true]; exact ⟨h1, hc, h3, h4, h5, h6⟩)
    · exact hu k μ hμ (by simp only [Box3.upper, if_true]; exact ⟨hc, h2, h3, h4, h5, h6⟩)
  · by_cases h1' : ax = 1
    · subst h1'
      rcases le_total μ.b (c : ℝ) with hc | hc
      · exact hl k μ hμ (by simp only [Box3.lower, if_neg h0, if_true]; exact ⟨h1, h2, h3, hc, h5, h6⟩)
      · exact hu k μ hμ (by simp only [Box3.upper, if_neg h0, if_true]; exact ⟨h1, h2, hc, h4, h5, h6⟩)
    · rcases le_total μ.meanEntropy (c : ℝ) with hc | hc
      · exact hl k μ hμ (by
          simp only [Box3.lower, if_neg h0, if_neg h1']; exact ⟨h1, h2, h3, h4, h5, hc⟩)
      · exact hu k μ hμ (by
          simp only [Box3.upper, if_neg h0, if_neg h1']; exact ⟨h1, h2, h3, h4, hc, h6⟩)

/-- The root box contains every chart law. -/
def root : Box3 := ⟨1 / 32768, 1, 1 / 32, 1 / 2, 0, 1⟩

theorem inBox_root {k : ℕ} (μ : InteriorLaw (Fin k)) (h : ChartHyp μ) : InBox root μ := by
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hE0 : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  have hEle : μ.meanEntropy ≤ 1 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap, H_le_one μ.a, H_le_one μ.b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [root]; push_cast; linarith [h.hratio]
  · simp only [root]; push_cast
    rw [div_le_one hb0]; exact h.hab.le
  · simp only [root]; push_cast; linarith [h.hmean, h.hab]
  · simp only [root]; push_cast; exact h.hside
  · simp only [root]; push_cast; exact hE0.le
  · simp only [root]; push_cast; exact hEle

theorem owner_of_good_root (h : Good root) : SameSidePsiTail8SmallMeanChartOwner := by
  intro k μ hab hsum hmean hinfo hE hside hratio hstrip hsmall hactive
  have hμ : ChartHyp μ := ⟨hab, hsum, hmean, hinfo, hE, hside, hratio, hstrip, hsmall, hactive⟩
  exact h k μ hμ (inBox_root μ hμ)

end CKLaneE.Chart

#check @CKLaneE.Chart.good_split
#check @CKLaneE.Chart.owner_of_good_root
#print axioms CKLaneE.Chart.good_split
#print axioms CKLaneE.Chart.owner_of_good_root
