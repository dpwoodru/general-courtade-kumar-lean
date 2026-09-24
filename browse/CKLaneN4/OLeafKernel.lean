import CKLaneN4.LowEntropy25
import CKLaneD.OCompact

/-!
# Lane N4: (O) leaf obligations for the archived labels 4, 7, 8, 9

Per-leaf obligation `CKLaneD.OCompact.OLeafOK (uvtBox p)` (the OP_Compact-region form of BRIEF §7) on
the full archived leaf image `CKLaneD.InUVT (uvtBox p)`.

* Label 4 (`global_eight_ratio`, OUTER_OPPOSITE.py): the archived method checks, on the whole leaf,
  `E.b ≤ 11/200`, `q.b ≤ 2/5`, `d.a ≥ 8 E.b`; the leaf is then owned by the union of the global
  eight-ratio theorem (`q ≤ 8E`) and PARENT8 (`q ≥ 8E`), with the `q = 0` face by parent equality.
  `checkL4 p w = true → OLeafOK (uvtBox p)` (`checkL4_sound`), unconditional: the witness is a rational
  box bound to the archived path by `CKLaneD.imageCheck` plus two log certificates.
* Labels 7, 8, 9 (`global_parent8`, `global_low_entropy_025`, `global_parent16`): every leaf image lies
  in `E ≤ 1/25` (Lane G1 `CKLaneG1.E25All.all_le`), where `OP_LowEntropy25` applies
  (`oLeafOK_of_le25`).
-/

namespace CKLaneN4

open GeneralCK CKLaneD CKLaneD.OCompact

/-- The clipped physical image of a leaf lies in a rational box certified by `imageCheck`
(copied from Lane M12 `CKLaneM12.inBox_of_imageCheck`). -/
theorem inBox_of_imageCheck {U : UVT} {B : Box} (h : imageCheck U B = true) {a b E : ℝ}
    (hin : InUVT U a b E) : InBox B a b E := by
  unfold imageCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ht0, ht1⟩, hal⟩, hah⟩, hbl⟩, hbh⟩ := h
  unfold InUVT at hin
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hin
  have hal' := pow2LowerOK_sound hal
  have hbl' := pow2UpperOK_sound hbl
  push_cast at hbl'
  refine ⟨hal'.trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hah with hah | hah
    · exact h2.trans (pow2UpperOK_sound hah)
    · have hq : ((1 / 10 : ℚ) : ℝ) ≤ (B.ahi : ℝ) := Rat.cast_le.mpr hah
      have h10 : ((1 / 10 : ℚ) : ℝ) = 1 / 10 := by norm_num
      rw [h10] at hq
      linarith
  · linarith
  · rcases hbh with hbh | hbh
    · have := pow2LowerOK_sound hbh
      push_cast at this
      linarith
    · have : (1 : ℝ) - (B.alo : ℝ) ≤ (B.bhi : ℝ) := by exact_mod_cast hbh
      linarith [hal'.trans h1]
  · rw [ht0]; exact h7
  · rw [ht1]; exact h8

/-! ## Labels 7, 8, 9: the low-entropy corollary -/

theorem oLeafOK_of_le25 {U : UVT} (h : ∀ a b E : ℝ, InUVT U a b E → E ≤ 1 / 25) : OLeafOK U := by
  intro k μ hab hsum hb ha _ _ _ hin hact
  exact opLowEntropy25 k μ hab hsum hb ha (h _ _ _ hin) hact

/-! ## Label 4: eight-ratio ∪ PARENT8 on the full leaf image -/

/-- Untrusted label-4 witness: rational box and log certificates at `ahi`, `blo`. -/
structure L4Witness where
  box : Box
  pa : PtCert
  pb : PtCert
  deriving Repr, DecidableEq

def l4BoxOK (B : Box) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧ B.bhi < 1 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1)

/-- Certified upper bound of the mean entropy on the box. -/
def l4EHi (w : L4Witness) : ℚ :=
  EMIN + w.box.t1 * ((Hhi w.box.ahi w.pa + Hhi w.box.blo w.pb) / 2 - EMIN)

/-- The archived label-4 acceptance test (`E.b ≤ 11/200`, `q.b ≤ 2/5`, `d.a ≥ 8 E.b`) bound to the
archived path `p`. -/
def checkL4 (p : List ℕ) (w : L4Witness) : Bool :=
  imageCheck (uvtBox p) w.box && l4BoxOK w.box && checkPt w.box.ahi w.pa &&
  checkPt w.box.blo w.pb &&
  decide (l4EHi w ≤ 11 / 200) && decide (1 - w.box.alo - w.box.blo ≤ 2 / 5) &&
  decide (8 * l4EHi w ≤ w.box.blo - w.box.ahi)

theorem checkL4_sound {p : List ℕ} {w : L4Witness} (h : checkL4 p w = true) :
    OLeafOK (uvtBox p) := by
  intro k μ hab hsum hb ha _ _ _ hin hact
  unfold checkL4 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨himg, hbox⟩, hpa⟩, hpb⟩, hEle⟩, hq25⟩, hd8⟩ := h
  unfold l4BoxOK at hbox
  simp only [decide_eq_true_eq] at hbox
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9⟩ := hbox
  obtain ⟨ha0, ha1, hb0, hb1, _, hE1⟩ := inBox_of_imageCheck himg hin
  obtain ⟨_, _, _, hHa, _, _⟩ := checkPt_bounds hpa
  obtain ⟨_, _, _, hHb, _, _⟩ := checkPt_bounds hpb
  have rB1 : (0 : ℝ) < w.box.alo := by exact_mod_cast hB1
  have rB3 : 2 * (w.box.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (w.box.blo : ℝ) := by exact_mod_cast hB4
  have rB6 : (w.box.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB7 : (0 : ℝ) ≤ w.box.t0 := by exact_mod_cast hB7
  have rB8 : (w.box.t0 : ℝ) ≤ w.box.t1 := by exact_mod_cast hB8
  -- mean entropy upper bound
  have hHa' : H μ.a ≤ H (w.box.ahi : ℝ) :=
    H_mono_left (by linarith [μ.a_interior.1]) ha1 (by linarith)
  have hHb' : H μ.b ≤ H (w.box.blo : ℝ) := H_anti_right (by linarith) hb0 (by linarith)
  have eE : ((l4EHi w : ℚ) : ℝ) = (EMIN : ℝ) + (w.box.t1 : ℝ) *
      (((Hhi w.box.ahi w.pa : ℚ) : ℝ) / 2 + ((Hhi w.box.blo w.pb : ℚ) : ℝ) / 2 - (EMIN : ℝ)) := by
    unfold l4EHi; push_cast; ring
  have hEup : μ.meanEntropy ≤ ((l4EHi w : ℚ) : ℝ) := by
    rw [eE]
    have ht1 : (0 : ℝ) ≤ w.box.t1 := rB7.trans rB8
    have := mul_le_mul_of_nonneg_left
      (show (H μ.a + H μ.b) / 2 - (EMIN : ℝ) ≤ ((Hhi w.box.ahi w.pa : ℚ) : ℝ) / 2 +
        ((Hhi w.box.blo w.pb : ℚ) : ℝ) / 2 - (EMIN : ℝ) by linarith) ht1
    linarith
  have rEle : ((l4EHi w : ℚ) : ℝ) ≤ 11 / 200 := by
    have := (Rat.cast_le (K := ℝ)).mpr hEle
    push_cast at this
    linarith
  have rq25 : 1 - (w.box.alo : ℝ) - (w.box.blo : ℝ) ≤ 2 / 5 := by
    have := (Rat.cast_le (K := ℝ)).mpr hq25
    push_cast at this
    linarith
  have rd8 : 8 * ((l4EHi w : ℚ) : ℝ) ≤ (w.box.blo : ℝ) - (w.box.ahi : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hd8
    push_cast at this
    linarith
  -- the law's parameters
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hEi : μ.meanEntropy ≤ 11 / 200 := hEup.trans rEle
  have hd : 8 * μ.meanEntropy ≤ μ.b - μ.a := by linarith
  have hq25' : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have hact' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy <
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmid]
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  rcases hq0.eq_or_lt with hz | hqpos
  · exfalso
    have h2 : (1 - (1 - μ.a - μ.b)) / 2 = 1 / 2 := by rw [← hz]; norm_num
    rw [h2, phi_eq_psi_half] at hact'
    exact lt_irrefl _ hact'
  by_cases h8 : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
  · exact absurd (parent8 _ _ hE hqpos hq25' h8) (not_lt.mpr hact'.le)
  · exact globalEightPsi_law μ hsum hEi hd (lt_of_not_ge h8).le hact.le

/-- A list of label-4 witnesses, all accepted, gives the obligation on every listed leaf. -/
theorem l4_list_sound (L : List (List ℕ × L4Witness))
    (h : (L.all fun x => checkL4 x.1 x.2) = true) : ∀ x ∈ L, OLeafOK (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkL4_sound (h x hx)

end CKLaneN4
