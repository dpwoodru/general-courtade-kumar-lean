import GeneralCK.Certificates.E8TAxisFirstCellCertified
import GeneralCK.Certificates.E8TAxisGeneratedGeometry

/-! Identifies the certified first-cell theorem with its exact retained-ledger
record. -/

namespace GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge

open E8TAxisPartitionKernel E8TAxisGeneratedGeometry

theorem certifiedFirstCell_real :
    certifiedFirstCell.real = E8TAxisFirstCellCertified.rectangle := by
  congr 1 <;>
    norm_num [certifiedFirstCell, RatRect.real,
      E8TAxisFirstCellCertified.rectangle,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower]

theorem certifiedFirstCell_positive : CellPositive certifiedFirstCell.real := by
  rw [certifiedFirstCell_real]
  exact E8TAxisFirstCellCertified.cellPositive

#print axioms certifiedFirstCell_real
#print axioms certifiedFirstCell_positive

end GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge
