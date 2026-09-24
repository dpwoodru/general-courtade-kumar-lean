import CKLaneM06.CapSound

/-!
# Lane M06: cap cover trees (exact halving of the archived 2-D mean roots)

* `cstep`, `cpathBox` : archived path recursion (`SAME_SIDE_CAP_COVER.reconstruct` /
  `EXPANDED_CAP_COVER`), digit `d = 2*axis + side`, axis `0 = a`, `1 = b`, side `0` = lower half.
* `ssRoot = [1/10,1/2]²` (SAME_SIDE_CAP root), `xhRoot = [1/10,1/2] × [1/2,9/10]` (EXPANDED_CAP root).
* `CapOn.merge` : the claim on both halves gives the claim on the parent box.
* `CTree` : a refinement tree whose leaves carry checker witnesses, or `vac` (no canonical law in the
  box: `a0 + b0 > 1` or `b1 ≤ a0`); `CTree.check` / `CTree.sound` : one reflective Boolean check of a
  whole subtree gives `CapOn` on its root box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK

/-- One exact halving step of an archived 2-D path digit `d = 2 * axis + side`. -/
def cstep (B : CBox) (d : ℕ) : CBox :=
  match d with
  | 0 => { B with a1 := (B.a0 + B.a1) / 2 }
  | 1 => { B with a0 := (B.a0 + B.a1) / 2 }
  | 2 => { B with b1 := (B.b0 + B.b1) / 2 }
  | 3 => { B with b0 := (B.b0 + B.b1) / 2 }
  | _ => B

/-- The exact box of an archived path below a root box. -/
def cpathBox (R : CBox) (p : List ℕ) : CBox := p.foldl cstep R

/-- `SAME_SIDE_CAP` root `[1/10,1/2] × [1/10,1/2]`. -/
def ssRoot : CBox := ⟨1 / 10, 1 / 2, 1 / 10, 1 / 2⟩

/-- `EXPANDED_CAP` root `[1/10,1/2] × [1/2,9/10]`. -/
def xhRoot : CBox := ⟨1 / 10, 1 / 2, 1 / 2, 9 / 10⟩

theorem cpathBox_append (R : CBox) (p : List ℕ) (d : ℕ) :
    cpathBox R (p ++ [d]) = cstep (cpathBox R p) d := by
  simp only [cpathBox, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The two halves of a halving step cover the parent box. -/
theorem CapOn.merge {B : CBox} {S : ℚ} {ax : ℕ} (hax : ax < 2)
    (h0 : CapOn (cstep B (2 * ax)) S) (h1 : CapOn (cstep B (2 * ax + 1)) S) : CapOn B S := by
  intro k μ hab hsum ha0 ha1 hb0 hb1 hs
  rcases ax with _ | _ | ax
  · have h0' : CapOn (cstep B 0) S := h0
    have h1' : CapOn (cstep B 1) S := h1
    rcases le_total μ.a (((B.a0 + B.a1) / 2 : ℚ) : ℝ) with hm | hm
    · exact h0' k μ hab hsum ha0 hm hb0 hb1 hs
    · exact h1' k μ hab hsum hm ha1 hb0 hb1 hs
  · have h0' : CapOn (cstep B 2) S := h0
    have h1' : CapOn (cstep B 3) S := h1
    rcases le_total μ.b (((B.b0 + B.b1) / 2 : ℚ) : ℝ) with hm | hm
    · exact h0' k μ hab hsum ha0 ha1 hb0 hm hs
    · exact h1' k μ hab hsum ha0 ha1 hm hb1 hs
  · omega

/-- Merge on archived paths. -/
theorem CapOn.merge_path {R : CBox} {S : ℚ} {p : List ℕ} {ax : ℕ} (hax : ax < 2)
    (h0 : CapOn (cpathBox R (p ++ [2 * ax])) S) (h1 : CapOn (cpathBox R (p ++ [2 * ax + 1])) S) :
    CapOn (cpathBox R p) S := by
  rw [cpathBox_append] at h0 h1
  exact CapOn.merge hax h0 h1

/-- Vacuous boxes: no canonical law (`a + b ≤ 1`, `a < b`) has its means there. -/
def vacOk (B : CBox) : Bool := decide (1 < B.a0 + B.b0 ∨ B.b1 ≤ B.a0)

theorem vac_sound {B : CBox} {S : ℚ} (h : vacOk B = true) : CapOn B S := by
  intro k μ hab hsum ha0 _ hb0 hb1 _
  exfalso
  simp only [vacOk, decide_eq_true_eq] at h
  rcases h with h1 | h1
  · have := qlt h1
    push_cast at this
    linarith
  · have := qle h1
    linarith

/-- A refinement tree with checker witnesses at its leaves. -/
inductive CTree where
  | leaf (w : CWit)
  | vac
  | node (ax : ℕ) (l r : CTree)
  deriving Repr

/-- One reflective Boolean check of a whole refinement subtree. -/
def CTree.check (S : ℚ) : CTree → CBox → Bool
  | leaf w, B => Cap.check B S w
  | vac, B => vacOk B
  | node ax l r, B => decide (ax < 2) && l.check S (cstep B (2 * ax)) && r.check S (cstep B (2 * ax + 1))

theorem CTree.sound (S : ℚ) : ∀ (T : CTree) (B : CBox), T.check S B = true → CapOn B S
  | leaf _, _, h => check_sound h
  | vac, _, h => vac_sound h
  | node ax l r, B, h => by
      simp only [CTree.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hax, hl⟩, hr⟩ := h
      exact CapOn.merge hax (CTree.sound S l _ hl) (CTree.sound S r _ hr)

/-- Per archived node: a checked refinement subtree certifies the node's exact box. -/
theorem CTree.sound_path {R : CBox} {S : ℚ} {p : List ℕ} {T : CTree}
    (h : T.check S (cpathBox R p) = true) : CapOn (cpathBox R p) S :=
  CTree.sound S T _ h

end CKLaneM06.Cap
