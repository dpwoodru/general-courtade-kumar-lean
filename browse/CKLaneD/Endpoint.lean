import CKLaneD.Checker

/-!
# Lane D: endpoint witnesses (cell trees) and the unconditional endpoint soundness theorem

`endpoint_check_sound (w) (hw : checkEndpoint w = true) : Sem w.box` has no other hypotheses.
-/

namespace CKLaneD

open GeneralCK

/-- A certificate tree: a single cell or a binary split of the box along `a`, `b` or `t`. -/
inductive Cert where
  | cell (c : CellCert)
  | splitA (m : ℚ) (l r : Cert)
  | splitB (m : ℚ) (l r : Cert)
  | splitT (m : ℚ) (l r : Cert)
  deriving Repr

def checkTree : Box → Cert → Bool
  | B, .cell c => checkCell B c
  | B, .splitA m l r =>
      decide (B.alo ≤ m ∧ m ≤ B.ahi) && checkTree { B with ahi := m } l &&
        checkTree { B with alo := m } r
  | B, .splitB m l r =>
      decide (B.blo ≤ m ∧ m ≤ B.bhi) && checkTree { B with bhi := m } l &&
        checkTree { B with blo := m } r
  | B, .splitT m l r =>
      decide (B.t0 ≤ m ∧ m ≤ B.t1) && checkTree { B with t1 := m } l &&
        checkTree { B with t0 := m } r

theorem sem_splitA {B : Box} {m : ℚ} (hl : Sem { B with ahi := m })
    (hr : Sem { B with alo := m }) : Sem B := by
  intro k μ hbox
  unfold InBox at hbox
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.a (m : ℝ) with h | h
  · exact hl k μ ⟨h1, h, h3, h4, h5, h6⟩
  · exact hr k μ ⟨h, h2, h3, h4, h5, h6⟩

theorem sem_splitB {B : Box} {m : ℚ} (hl : Sem { B with bhi := m })
    (hr : Sem { B with blo := m }) : Sem B := by
  intro k μ hbox
  unfold InBox at hbox
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.b (m : ℝ) with h | h
  · exact hl k μ ⟨h1, h2, h3, h, h5, h6⟩
  · exact hr k μ ⟨h1, h2, h, h4, h5, h6⟩

theorem sem_splitT {B : Box} {m : ℚ} (hl : Sem { B with t1 := m })
    (hr : Sem { B with t0 := m }) : Sem B := by
  intro k μ hbox
  unfold InBox at hbox
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbox
  rcases le_total μ.meanEntropy
      ((EMIN : ℝ) + (m : ℝ) * ((H μ.a + H μ.b) / 2 - (EMIN : ℝ))) with h | h
  · exact hl k μ ⟨h1, h2, h3, h4, h5, h⟩
  · exact hr k μ ⟨h1, h2, h3, h4, h, h6⟩

theorem checkTree_sound : ∀ (B : Box) (t : Cert), checkTree B t = true → Sem B
  | B, .cell c, h => checkCell_sound h
  | B, .splitA m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitA (checkTree_sound _ l h.1.2) (checkTree_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitB (checkTree_sound _ l h.1.2) (checkTree_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkTree, Bool.and_eq_true] at h
      exact sem_splitT (checkTree_sound _ l h.1.2) (checkTree_sound _ r h.2)

/-- An endpoint witness: the exact box together with its certificate tree. -/
structure EndpointWitness where
  box : Box
  cert : Cert
  deriving Repr

/-- The Boolean endpoint checker. -/
def checkEndpoint (w : EndpointWitness) : Bool := checkTree w.box w.cert

/-- Unconditional semantic soundness of the endpoint checker. -/
theorem endpoint_check_sound (w : EndpointWitness) (hw : checkEndpoint w = true) :
    Sem w.box :=
  checkTree_sound w.box w.cert hw

/-- Owner form: on the box and when psi is (weakly) active at the parent, `μ.gap ≤ μ.cost`. -/
theorem sem_gap_le_cost {B : Box} (hB : Sem B) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hbox : InBox B μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (hB k μ hbox)

end CKLaneD
