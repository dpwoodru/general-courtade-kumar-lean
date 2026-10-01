import CKLaneM07.CE.R3Roots
import CKLaneM07.CE.R3Glue
import CKLaneM07.CE.R3Cells.K14.S0000
import CKLaneM07.CE.R3Cells.K14.S0001
import CKLaneM07.CE.R3Cells.K14.S0002
import CKLaneM07.CE.R3Cells.K14.S0003
import CKLaneM07.CE.R3Cells.K14.S0004
import CKLaneM07.CE.R3Cells.K14.S0005
import CKLaneM07.CE.R3Cells.K14.S0006
import CKLaneM07.CE.R3Cells.K14.S0007
import CKLaneM07.CE.R3Cells.K14.S0008

/-! Lane M07 row-3 octave k=14: 9 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K14

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root14 :=
  sem_node 0
    (sem_node 1
      (sem_node 1
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0000.sem)
        (sem_node 2
          (sem_node 2
            (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0001.sem)
            (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0002.sem))
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0003.sem)))
      (sem_node 2
        (sem_node 2
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0004.sem)
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0005.sem))
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0006.sem)))
    (sem_node 1
      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0007.sem)
      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K14.S0008.sem))

end CKLaneM07.CE.R3Oct.K14
