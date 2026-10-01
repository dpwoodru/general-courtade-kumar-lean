import GeneralCK.PureGapE8AxisConsumers

/-!
# Exact partition kernel for the E8 t-axis family

The historical search produced a binary subdivision tree.  This file proves
once and for all that a tree whose split points lie inside their parent boxes
covers its parent rectangle.  Generated files need only instantiate the tree
and provide one analytic proof at each leaf.
-/

namespace GeneralCK.Certificates.E8TAxisPartitionKernel

open GeneralCK

structure Rect where
  s0 : ℝ
  s1 : ℝ
  t0 : ℝ
  t1 : ℝ

def Rect.Covers (r : Rect) (s t : ℝ) : Prop :=
  r.s0 ≤ s ∧ s ≤ r.s1 ∧ r.t0 ≤ t ∧ t ≤ r.t1

inductive Tree where
  | leaf
  | splitS (x : ℚ) (left right : Tree)
  | splitT (x : ℚ) (lower upper : Tree)

def Tree.leafCount : Tree → ℕ
  | .leaf => 1
  | .splitS _ left right | .splitT _ left right => left.leafCount + right.leafCount

def Rect.leftS (r : Rect) (x : ℚ) : Rect := { r with s1 := x }
def Rect.rightS (r : Rect) (x : ℚ) : Rect := { r with s0 := x }
def Rect.lowerT (r : Rect) (x : ℚ) : Rect := { r with t1 := x }
def Rect.upperT (r : Rect) (x : ℚ) : Rect := { r with t0 := x }

def AllLeaves (P : Rect → Prop) : Tree → Rect → Prop
  | .leaf, r => P r
  | .splitS x left right, r =>
      r.s0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ r.s1 ∧
        AllLeaves P left (r.leftS x) ∧ AllLeaves P right (r.rightS x)
  | .splitT x lower upper, r =>
      r.t0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ r.t1 ∧
        AllLeaves P lower (r.lowerT x) ∧ AllLeaves P upper (r.upperT x)

theorem locate_leaf {P : Rect → Prop} {tree : Tree} {r : Rect} {s t : ℝ}
    (hall : AllLeaves P tree r) (hpoint : r.Covers s t) :
    ∃ leaf, P leaf ∧ leaf.Covers s t := by
  induction tree generalizing r with
  | leaf => exact ⟨r, hall, hpoint⟩
  | splitS x left right ihl ihr =>
      rcases hall with ⟨hx0, hx1, hl, hr⟩
      by_cases hs : s ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hs, hpoint.2.2⟩
      · apply ihr hr
        exact ⟨le_of_not_ge hs, hpoint.2.1, hpoint.2.2⟩
  | splitT x lower upper ihl ihu =>
      rcases hall with ⟨hx0, hx1, hl, hu⟩
      by_cases ht : t ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hpoint.2.1, hpoint.2.2.1, ht⟩
      · apply ihu hu
        exact ⟨hpoint.1, hpoint.2.1, le_of_not_ge ht, hpoint.2.2.2⟩

def CellPositive (r : Rect) : Prop :=
  ∀ s t : ℝ, E8Admissible s t → r.Covers s t → 0 < e8RegularDeltaT s t

noncomputable def domain : Rect := ⟨3 / 50, 63 / 20, 0, 1 / 50⟩

theorem derivativeBound_of_tree {tree : Tree}
    (hall : AllLeaves CellPositive tree domain) : E8TAxisDerivativeBound := by
  intro s t hadm hs0 hs1 ht1
  have ht0 : 0 ≤ t := hadm.2.1.le
  obtain ⟨leaf, hleaf, hcover⟩ := locate_leaf hall
    (r := domain) (s := s) (t := t) ⟨hs0, hs1, ht0, ht1⟩
  exact hleaf s t hadm hcover

#print axioms locate_leaf
#print axioms derivativeBound_of_tree

end GeneralCK.Certificates.E8TAxisPartitionKernel
