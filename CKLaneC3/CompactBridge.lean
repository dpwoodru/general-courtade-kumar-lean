import CKLaneC3.CompactData
import CKLaneC3.CompactFullTable

/-! Lane C3: the data tables are (definitionally) the checked tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBridge
open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF
open CKLaneC3

theorem T_eq : CompactData.T = CompactTable.T := rfl

theorem F_eq : CompactData.F = CompactFullTable.F := rfl

theorem T_valid : TableValid CompactData.T := T_eq ▸ CompactTable.T_valid

theorem F_valid : FullValid CompactData.T CompactData.F := by
  rw [T_eq, F_eq]; exact CompactFullTable.F_valid

end CKLaneC3.CompactBridge
