import CKLaneM07.CE.R3Roots
import CKLaneM07.CE.R3Glue
import CKLaneM07.CE.R3Cells.K16.S0000
import CKLaneM07.CE.R3Cells.K16.S0001
import CKLaneM07.CE.R3Cells.K16.S0002
import CKLaneM07.CE.R3Cells.K16.S0003
import CKLaneM07.CE.R3Cells.K16.S0004
import CKLaneM07.CE.R3Cells.K16.S0005
import CKLaneM07.CE.R3Cells.K16.S0006
import CKLaneM07.CE.R3Cells.K16.S0007
import CKLaneM07.CE.R3Cells.K16.S0008
import CKLaneM07.CE.R3Cells.K16.S0009
import CKLaneM07.CE.R3Cells.K16.S0010
import CKLaneM07.CE.R3Cells.K16.S0011
import CKLaneM07.CE.R3Cells.K16.S0012
import CKLaneM07.CE.R3Cells.K16.S0013
import CKLaneM07.CE.R3Cells.K16.S0014
import CKLaneM07.CE.R3Cells.K16.S0015
import CKLaneM07.CE.R3Cells.K16.S0016
import CKLaneM07.CE.R3Cells.K16.S0017
import CKLaneM07.CE.R3Cells.K16.S0018
import CKLaneM07.CE.R3Cells.K16.S0019
import CKLaneM07.CE.R3Cells.K16.S0020
import CKLaneM07.CE.R3Cells.K16.S0021
import CKLaneM07.CE.R3Cells.K16.S0022
import CKLaneM07.CE.R3Cells.K16.S0023

/-! Lane M07 row-3 octave k=16: 24 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K16

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root16 :=
  sem_node 2
    (sem_node 1
      (sem_node 2
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0000.sem)
        (sem_node 1
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0001.sem)
          (sem_node 1
            (sem_node 0
              (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0002.sem)
              (sem_node 2
                (sem_node 1
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0003.sem)
                  (sem_node 0
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0004.sem)
                    (sem_node 2
                      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0005.sem)
                      (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0006.sem))))
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0007.sem)))
            (sem_node 2
              (sem_node 0
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0008.sem)
                (sem_node 1
                  (sem_node 2
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0009.sem)
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0010.sem))
                  (sem_node 2
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0011.sem)
                    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0012.sem))))
              (sem_node 1
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0013.sem)
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0014.sem))))))
      (sem_node 2
        (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0015.sem)
        (sem_node 1
          (sem_node 1
            (sem_node 2
              (sem_node 0
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0016.sem)
                (sem_node 1
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0017.sem)
                  (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0018.sem)))
              (sem_node 1
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0019.sem)
                (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0020.sem)))
            (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0021.sem))
          (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0022.sem))))
    (sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K16.S0023.sem)

end CKLaneM07.CE.R3Oct.K16
