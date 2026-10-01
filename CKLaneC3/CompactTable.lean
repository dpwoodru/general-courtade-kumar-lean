import CKLaneC3.CompactChunk00
import CKLaneC3.CompactChunk01
import CKLaneC3.CompactChunk02
import CKLaneC3.CompactChunk03
import CKLaneC3.CompactChunk04
import CKLaneC3.CompactChunk05
import CKLaneC3.CompactChunk06
import CKLaneC3.CompactChunk07
import CKLaneC3.CompactChunk08
import CKLaneC3.CompactChunk09
import CKLaneC3.CompactChunk10
import CKLaneC3.CompactChunk11
import CKLaneC3.CompactChunk12
import CKLaneC3.CompactChunk13
import CKLaneC3.CompactChunk14
import CKLaneC3.CompactChunk15
import CKLaneC3.CompactChunk16
import CKLaneC3.CompactChunk17
import CKLaneC3.CompactChunk18
import CKLaneC3.CompactChunk19
import CKLaneC3.CompactChunk20
import CKLaneC3.CompactChunk21
import CKLaneC3.CompactChunk22
import CKLaneC3.CompactChunk23
import CKLaneC3.CompactChunk24
import CKLaneC3.CompactChunk25
import CKLaneC3.CompactChunk26
import CKLaneC3.CompactChunk27
import CKLaneC3.CompactChunk28
import CKLaneC3.CompactChunk29
import CKLaneC3.CompactChunk30
import CKLaneC3.CompactChunk31
import CKLaneC3.CompactChunk32
import CKLaneC3.CompactChunk33
import CKLaneC3.CompactChunk34
import CKLaneC3.CompactChunk35
import CKLaneC3.CompactChunk36
import CKLaneC3.CompactChunk37
import CKLaneC3.CompactChunk38
import CKLaneC3.CompactChunk39

/-! Lane C3 compact slope table (generated). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactTable
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain
open CKLaneC3

def T : List (List Piece) := [CompactChunk00.chunk, CompactChunk01.chunk, CompactChunk02.chunk, CompactChunk03.chunk, CompactChunk04.chunk, CompactChunk05.chunk, CompactChunk06.chunk, CompactChunk07.chunk, CompactChunk08.chunk, CompactChunk09.chunk, CompactChunk10.chunk, CompactChunk11.chunk, CompactChunk12.chunk, CompactChunk13.chunk, CompactChunk14.chunk, CompactChunk15.chunk, CompactChunk16.chunk, CompactChunk17.chunk, CompactChunk18.chunk, CompactChunk19.chunk, CompactChunk20.chunk, CompactChunk21.chunk, CompactChunk22.chunk, CompactChunk23.chunk, CompactChunk24.chunk, CompactChunk25.chunk, CompactChunk26.chunk, CompactChunk27.chunk, CompactChunk28.chunk, CompactChunk29.chunk, CompactChunk30.chunk, CompactChunk31.chunk, CompactChunk32.chunk, CompactChunk33.chunk, CompactChunk34.chunk, CompactChunk35.chunk, CompactChunk36.chunk, CompactChunk37.chunk, CompactChunk38.chunk, CompactChunk39.chunk]

theorem T_all : T.all (fun c => c.all Piece.check) = true := by
  simp only [T, List.all_cons, List.all_nil, CompactChunk00.chunk_ok, CompactChunk01.chunk_ok, CompactChunk02.chunk_ok, CompactChunk03.chunk_ok, CompactChunk04.chunk_ok, CompactChunk05.chunk_ok, CompactChunk06.chunk_ok, CompactChunk07.chunk_ok, CompactChunk08.chunk_ok, CompactChunk09.chunk_ok, CompactChunk10.chunk_ok, CompactChunk11.chunk_ok, CompactChunk12.chunk_ok, CompactChunk13.chunk_ok, CompactChunk14.chunk_ok, CompactChunk15.chunk_ok, CompactChunk16.chunk_ok, CompactChunk17.chunk_ok, CompactChunk18.chunk_ok, CompactChunk19.chunk_ok, CompactChunk20.chunk_ok, CompactChunk21.chunk_ok, CompactChunk22.chunk_ok, CompactChunk23.chunk_ok, CompactChunk24.chunk_ok, CompactChunk25.chunk_ok, CompactChunk26.chunk_ok, CompactChunk27.chunk_ok, CompactChunk28.chunk_ok, CompactChunk29.chunk_ok, CompactChunk30.chunk_ok, CompactChunk31.chunk_ok, CompactChunk32.chunk_ok, CompactChunk33.chunk_ok, CompactChunk34.chunk_ok, CompactChunk35.chunk_ok, CompactChunk36.chunk_ok, CompactChunk37.chunk_ok, CompactChunk38.chunk_ok, CompactChunk39.chunk_ok, Bool.and_self]

theorem T_valid : TableValid T := by
  intro c hc p hp
  exact List.all_eq_true.mp (List.all_eq_true.mp T_all c hc) p hp

end CKLaneC3.CompactTable
