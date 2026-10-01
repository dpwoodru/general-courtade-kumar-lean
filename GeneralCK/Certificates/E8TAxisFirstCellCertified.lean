import GeneralCK.Certificates.E8TAxisFirstCellCertifiedArithmetic
import GeneralCK.Certificates.E8TAxisFirstCellEndpointWitnesses
import GeneralCK.Certificates.E8TAxisPartitionKernel

/-! Unconditional enclosure and positivity on the exact historical first cell.
The widened coefficient boxes are outputs of checked stable interval graphs. -/

namespace GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor

theorem centerBoxes_contains : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerA_covers
    have hh := E8TAxisFirstCellGraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerB_covers
    have hh := E8TAxisFirstCellGraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerC_covers
    have hh := E8TAxisFirstCellGraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisFirstCellEndpointWitnesses.centerD_covers
    have hh := E8TAxisFirstCellGraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

theorem wholeBoxes_contains {s t : ℝ} (h : InFirstCell s t) :
    wholeBoxes.ContainsAt s t := by
  rcases h with ⟨hsl, hsu, htl, htu⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeA_covers_slope (s := t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeB_covers_slope (s := 2*s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeC_covers_slope (s := s+t)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ :=
      E8TAxisFirstCellEndpointWitnesses.wholeD_covers_slope (s := s)
        ⟨by linarith, by linarith⟩
    have hh := E8TAxisFirstCellGraphWholeD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh

/-- Ten center and five whole-cell mixed derivative bounds, with no assumptions. -/
def MixedBounds : Prop :=
  data.CenterEnclosed (mixed qJet centerS centerT) ∧
    ∀ s t, InFirstCell s t → data.RemainderEnclosed (mixed qJet s t)

theorem mixedBounds : MixedBounds :=
  ⟨centerEnclosed_of_contains centerBoxes_contains,
    fun _ _ h => wholeEnclosed_of_contains (wholeBoxes_contains h)⟩

theorem centeredReplay_contains {s t : ℝ} (h : InFirstCell s t) :
    data.replay.Contains (e8RegularDeltaT s t) :=
  Data.firstCell_contains rfl rfl mixedBounds.1 mixedBounds.2 h

theorem positive {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t :=
  Data.firstCell_positive rfl rfl mixedBounds.1 mixedBounds.2 replay_positive h

noncomputable def rectangle : E8TAxisPartitionKernel.Rect :=
  ⟨sLower, 3 / 40, tLower, 1 / 50⟩

theorem cellPositive : E8TAxisPartitionKernel.CellPositive rectangle := by
  intro s t _ h
  exact positive h

#print axioms centerBoxes_contains
#print axioms wholeBoxes_contains
#print axioms mixedBounds
#print axioms centeredReplay_contains
#print axioms positive
#print axioms cellPositive
end GeneralCK.Certificates.E8TAxisFirstCellCertified
