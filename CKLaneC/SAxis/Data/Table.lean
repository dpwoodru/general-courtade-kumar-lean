import CKLaneC.SAxis.Data.Tab00
import CKLaneC.SAxis.Data.Tab01
import CKLaneC.SAxis.Data.Tab02
import CKLaneC.SAxis.Data.Tab03
import CKLaneC.SAxis.Data.Tab04
import CKLaneC.SAxis.Data.Tab05
import CKLaneC.SAxis.Data.Tab06
import CKLaneC.SAxis.Data.Tab07
import CKLaneC.SAxis.Data.Tab08
import CKLaneC.SAxis.Data.Tab09
import CKLaneC.SAxis.Data.Tab10
import CKLaneC.SAxis.Data.Tab11
import CKLaneC.SAxis.Data.Tab12
import CKLaneC.SAxis.Data.Tab13

set_option autoImplicit false

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain

namespace CKLaneC.SAxis.Data

/-- The checked slope table of the sAxis certificate. -/
def T : List (List Piece) := [tab00, tab01, tab02, tab03, tab04, tab05, tab06, tab07, tab08, tab09, tab10, tab11, tab12, tab13]

theorem T_valid : TableValid T :=
  (tableValid_cons tab00_valid (tableValid_cons tab01_valid (tableValid_cons tab02_valid (tableValid_cons tab03_valid (tableValid_cons tab04_valid (tableValid_cons tab05_valid (tableValid_cons tab06_valid (tableValid_cons tab07_valid (tableValid_cons tab08_valid (tableValid_cons tab09_valid (tableValid_cons tab10_valid (tableValid_cons tab11_valid (tableValid_cons tab12_valid (tableValid_cons tab13_valid tableValid_nil))))))))))))))

end CKLaneC.SAxis.Data
