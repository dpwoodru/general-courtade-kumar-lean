import CKLaneC3.CompactTable
import CKLaneC3.CompactFull00
import CKLaneC3.CompactFull01
import CKLaneC3.CompactFull02
import CKLaneC3.CompactFull03
import CKLaneC3.CompactFull04
import CKLaneC3.CompactFull05
import CKLaneC3.CompactFull06
import CKLaneC3.CompactFull07
import CKLaneC3.CompactFull08
import CKLaneC3.CompactFull09
import CKLaneC3.CompactFull10
import CKLaneC3.CompactFull11
import CKLaneC3.CompactFull12
import CKLaneC3.CompactFull13
import CKLaneC3.CompactFull14
import CKLaneC3.CompactFull15
import CKLaneC3.CompactFull16
import CKLaneC3.CompactFull17
import CKLaneC3.CompactFull18
import CKLaneC3.CompactFull19
import CKLaneC3.CompactFull20
import CKLaneC3.CompactFull21
import CKLaneC3.CompactFull22
import CKLaneC3.CompactFull23
import CKLaneC3.CompactFull24
import CKLaneC3.CompactFull25
import CKLaneC3.CompactFull26
import CKLaneC3.CompactFull27
import CKLaneC3.CompactFull28
import CKLaneC3.CompactFull29
import CKLaneC3.CompactFull30
import CKLaneC3.CompactFull31
import CKLaneC3.CompactFull32
import CKLaneC3.CompactFull33
import CKLaneC3.CompactFull34
import CKLaneC3.CompactFull35
import CKLaneC3.CompactFull36
import CKLaneC3.CompactFull37
import CKLaneC3.CompactFull38
import CKLaneC3.CompactFull39

/-! Lane C3 compact full-piece jet table (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactFullTable
open GeneralCK GeneralCK.Certificates
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF
open CKLaneC3

def F : JTable := [CompactFull00.fchunk, CompactFull01.fchunk, CompactFull02.fchunk, CompactFull03.fchunk, CompactFull04.fchunk, CompactFull05.fchunk, CompactFull06.fchunk, CompactFull07.fchunk, CompactFull08.fchunk, CompactFull09.fchunk, CompactFull10.fchunk, CompactFull11.fchunk, CompactFull12.fchunk, CompactFull13.fchunk, CompactFull14.fchunk, CompactFull15.fchunk, CompactFull16.fchunk, CompactFull17.fchunk, CompactFull18.fchunk, CompactFull19.fchunk, CompactFull20.fchunk, CompactFull21.fchunk, CompactFull22.fchunk, CompactFull23.fchunk, CompactFull24.fchunk, CompactFull25.fchunk, CompactFull26.fchunk, CompactFull27.fchunk, CompactFull28.fchunk, CompactFull29.fchunk, CompactFull30.fchunk, CompactFull31.fchunk, CompactFull32.fchunk, CompactFull33.fchunk, CompactFull34.fchunk, CompactFull35.fchunk, CompactFull36.fchunk, CompactFull37.fchunk, CompactFull38.fchunk, CompactFull39.fchunk]

theorem F_valid : FullValid CompactTable.T F :=
  fullValid_of_forall2 (.cons CompactFull00.fchunk_ok (.cons CompactFull01.fchunk_ok (.cons CompactFull02.fchunk_ok (.cons CompactFull03.fchunk_ok (.cons CompactFull04.fchunk_ok (.cons CompactFull05.fchunk_ok (.cons CompactFull06.fchunk_ok (.cons CompactFull07.fchunk_ok (.cons CompactFull08.fchunk_ok (.cons CompactFull09.fchunk_ok (.cons CompactFull10.fchunk_ok (.cons CompactFull11.fchunk_ok (.cons CompactFull12.fchunk_ok (.cons CompactFull13.fchunk_ok (.cons CompactFull14.fchunk_ok (.cons CompactFull15.fchunk_ok (.cons CompactFull16.fchunk_ok (.cons CompactFull17.fchunk_ok (.cons CompactFull18.fchunk_ok (.cons CompactFull19.fchunk_ok (.cons CompactFull20.fchunk_ok (.cons CompactFull21.fchunk_ok (.cons CompactFull22.fchunk_ok (.cons CompactFull23.fchunk_ok (.cons CompactFull24.fchunk_ok (.cons CompactFull25.fchunk_ok (.cons CompactFull26.fchunk_ok (.cons CompactFull27.fchunk_ok (.cons CompactFull28.fchunk_ok (.cons CompactFull29.fchunk_ok (.cons CompactFull30.fchunk_ok (.cons CompactFull31.fchunk_ok (.cons CompactFull32.fchunk_ok (.cons CompactFull33.fchunk_ok (.cons CompactFull34.fchunk_ok (.cons CompactFull35.fchunk_ok (.cons CompactFull36.fchunk_ok (.cons CompactFull37.fchunk_ok (.cons CompactFull38.fchunk_ok (.cons CompactFull39.fchunk_ok (.nil)))))))))))))))))))))))))))))))))))))))))

end CKLaneC3.CompactFullTable
