import CKLaneM07.CE.R3Roots
import CKLaneM07.CE.R3Glue
import CKLaneM07.CE.R3Cells.K9.S0000

/-! Lane M07 row-3 octave k=9: 1 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K9

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root9 :=
  sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K9.S0000.sem

end CKLaneM07.CE.R3Oct.K9
