import CKLaneM07.CE.R3Sound2
import CKLaneN1.Tree

/-!
# Lane N1 — CE-stat row 3: leaf predicate and tree soundness

Leaf predicate over boxes `B` in coordinates `(a, z, y)` (`b = a + z y`, `c = a + y`):

* `retVac B`  — `2 a₁ + c₁ ≤ 1/10000`: then `a + c = 2a + y ≤ S` contradicts the retained cutoff;
* `tcVac B`   — `1/100 ≤ a₀ + b₀ c₀` (with `0 ≤ b₀, c₀`): then `b ≥ 1/100`, contradicting `b < t_C ≤ 1/100`;
* M07's frozen checker `CKLaneM07.CE.R3.r3BoxOK` (soundness `r3Box_sound`, stationarity-free bound
  `0 ≤ gapLB (H a) (H b) c` under `A ≤ 1/20`).

`Sem B` is the semantic statement of a box; `sem_of_tree` turns a Boolean check of every leaf of a
partition tree of `B` into `Sem B`, and `sem_of_skeleton` glues sub-boxes.
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK CKLaneN1

/-- retained-cutoff vacuity -/
def retVac (B : B3) : Bool := decide (2 * B.a1 + B.c1 ≤ 1 / 10000)

/-- `t_C ≤ 1/100` vacuity (`b < t_C`) -/
def tcVac (B : B3) : Bool :=
  decide (0 ≤ B.b0) && decide (0 ≤ B.c0) && decide (1 / 100 ≤ B.a0 + B.b0 * B.c0)

/-- the row-3 leaf predicate -/
def leafOK (B : B3) (w : CKLaneM07.CE.R3.RWit) : Bool :=
  retVac B || tcVac B || CKLaneM07.CE.R3.r3BoxOK B w

/-- the semantic content of a box -/
def Sem (B : B3) : Prop :=
  ∀ a z y : ℝ, B.Mem a z y → 0 < z → z < 1 → 0 < y → y ≤ (H a + H (a + z * y)) / 20 →
    1 / 10000 < 2 * a + y → a + z * y < 1 / 100 →
    0 ≤ CKLaneM07.CE.gapLB (H a) (H (a + z * y)) (a + y)

theorem leafOK_sound {B : B3} {w : CKLaneM07.CE.R3.RWit} (h : leafOK B w = true) : Sem B := by
  intro a z y hm hz0 hz1 hy hA hret htc
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := hm
  simp only [leafOK, Bool.or_eq_true] at h
  rcases h with (hr | ht) | hb
  · exfalso
    simp only [retVac, decide_eq_true_eq] at hr
    have hrR : (2 : ℝ) * (B.a1 : ℝ) + (B.c1 : ℝ) ≤ 1 / 10000 := by
      have := (Rat.cast_le (K := ℝ)).mpr hr
      push_cast at this
      linarith
    linarith
  · exfalso
    simp only [tcVac, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨hb00, hc00⟩, hlo⟩ := ht
    have hb00R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hb00
    have hc00R : (0 : ℝ) ≤ (B.c0 : ℝ) := by exact_mod_cast hc00
    have hloR : (1 : ℝ) / 100 ≤ (B.a0 : ℝ) + (B.b0 : ℝ) * (B.c0 : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hlo
      push_cast at this
      linarith
    have hzy : (B.b0 : ℝ) * (B.c0 : ℝ) ≤ z * y := mul_le_mul hb0 hc0 hc00R (hb00R.trans hb0)
    linarith
  · exact CKLaneM07.CE.R3.r3Box_sound hb ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ hz0 hz1 hy hA

/-- a partition tree of `R` whose leaves all pass `leafOK` proves `Sem R` -/
theorem sem_of_tree (R : B3) (T : PT CKLaneM07.CE.R3.RWit)
    (h : T.allLeaves (fun p w => leafOK (R.ofPath p) w) = true) : Sem R := by
  intro a z y hm
  obtain ⟨q, hq, hmq⟩ := PT.cover R T hm
  exact leafOK_sound (PT.allLeaves_sound h q hq) a z y hmq

/-- gluing: if every leaf box of a partition tree of `R` satisfies `Sem`, so does `R` -/
theorem sem_of_skeleton (R : B3) (T : PT Unit) (h : ∀ q ∈ T.leaves, Sem (R.ofPath q.1)) :
    Sem R := by
  intro a z y hm
  obtain ⟨q, hq, hmq⟩ := PT.cover R T hm
  exact h q hq a z y hmq

end CKLaneN1.R3
