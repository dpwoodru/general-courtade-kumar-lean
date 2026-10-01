import CKLaneM07.CE.R3Roots
import CKLaneM07.CE.R3Glue
import CKLaneM07.CE.R3Cells.K11.S0000
import CKLaneM07.CE.R3Cells.K11.S0001

/-! Lane M07 row-3 octave k=11: 2 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K11

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root11 :=
  sem_node 0
    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K11.S0000.sem)
    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K11.S0001.sem)

end CKLaneM07.CE.R3Oct.K11
