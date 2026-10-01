import CKLaneC3.CompactTreeB
import CKLaneC3.CompactBridge
import GeneralCK.PureGapE8SAxisOriginClosure
import GeneralCK.PureGapE8CertificateReduction

/-!
# Lane C3 — the `compact` field of `GeneralCK.E8CertificateOwners`

The compact box `[1/50, 63/20] × [1/50, 12]` is covered, by an exact rational split
tree (`CompactTreeA.tree_valid` and `CompactTreeA.leaves_eqR`, both `decide +kernel`, and the
per-batch slice identities `CompactSliceBB.slice_eq`, assembled in `CompactTreeB.leaves_eq`), by
6907 cubic Taylor cell certificates (each `decide +kernel`, sound by
`CompactCell.CellW.check_sound`) over a checked slope table of 957 pieces
(`CompactTable.T_valid`), and by 21 origin rectangles (`s1 + t1 ≤ 2/25`) owned by the
unconditional origin second-`s`-derivative theorem `e8RegularDeltaSS_pos_on_origin`.
The cell checks are evaluated with memoised chains (`CompactCoverF.checkF`, interior slope
pieces read from the full-jet table, each entry checked by recomputation in `CompactFull*`);
`CompactCoverF.checkF_eq` proves this equals `CellW.check`, so the semantics is unchanged.  The
batches evaluate over the data tables `CompactData.T/F`, which `CompactBridge` proves equal (`rfl`)
to the checked tables `CompactTable.T` / `CompactFullTable.F`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.Compact

open GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisRationalTreeBridgeKernel
open CKLaneC3.CompactCover

/-- Origin sub-owner from the unconditional origin second-`s`-derivative bound. -/
theorem originOwner : E8PositiveOn fun s t => s + t ≤ 2 / 25 := by
  intro s t hadm hR
  have hR' : s + t ≤ 2 / 25 := hR
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact e8RegularDeltaSS_pos_on_origin (hadm.mono_s hu.1 hu.2.le) (by linarith [hu.2, hR'])

/-- The `compact` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem compact :
    E8PositiveOn fun s t => (1 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ (1 / 50 : ℝ) ≤ t ∧ t ≤ 12 := by
  intro s t hadm h
  apply CKLaneC3.CompactCoverF.positive_of_coverF CKLaneC3.CompactBridge.T_valid
    CKLaneC3.CompactBridge.F_valid originOwner
    CKLaneC3.CompactTreeA.tree_valid CKLaneC3.CompactTreeB.leaves_eq
    CKLaneC3.CompactTreeB.allTags_ok s t hadm
  simp only [CKLaneC3.CompactTreeA.D, E8TAxisGeneratedGeometry.RatRect.real, Rect.Covers]
  push_cast
  exact h

end CKLaneC3.Compact
