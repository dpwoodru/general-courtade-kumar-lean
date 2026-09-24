import CKLaneC3.CompactSlice00
import CKLaneC3.CompactSlice01
import CKLaneC3.CompactSlice02
import CKLaneC3.CompactSlice03
import CKLaneC3.CompactSlice04
import CKLaneC3.CompactSlice05
import CKLaneC3.CompactSlice06
import CKLaneC3.CompactSlice07
import CKLaneC3.CompactSlice08
import CKLaneC3.CompactSlice09
import CKLaneC3.CompactSlice10
import CKLaneC3.CompactSlice11
import CKLaneC3.CompactSlice12
import CKLaneC3.CompactSlice13
import CKLaneC3.CompactSlice14
import CKLaneC3.CompactSlice15
import CKLaneC3.CompactSlice16
import CKLaneC3.CompactSlice17
import CKLaneC3.CompactSlice18
import CKLaneC3.CompactSlice19
import CKLaneC3.CompactSlice20
import CKLaneC3.CompactSlice21
import CKLaneC3.CompactSlice22
import CKLaneC3.CompactSlice23
import CKLaneC3.CompactSlice24
import CKLaneC3.CompactSlice25
import CKLaneC3.CompactSlice26
import CKLaneC3.CompactSlice27
import CKLaneC3.CompactSlice28
import CKLaneC3.CompactSlice29
import CKLaneC3.CompactSlice30
import CKLaneC3.CompactSlice31
import CKLaneC3.CompactSlice32
import CKLaneC3.CompactSlice33
import CKLaneC3.CompactSlice34
import CKLaneC3.CompactSlice35
import CKLaneC3.CompactSlice36
import CKLaneC3.CompactSlice37
import CKLaneC3.CompactSlice38
import CKLaneC3.CompactSlice39
import CKLaneC3.CompactSlice40
import CKLaneC3.CompactSlice41
import CKLaneC3.CompactSlice42
import CKLaneC3.CompactSlice43
import CKLaneC3.CompactSlice44
import CKLaneC3.CompactSlice45
import CKLaneC3.CompactSlice46
import CKLaneC3.CompactSlice47
import CKLaneC3.CompactSlice48
import CKLaneC3.CompactSlice49
import CKLaneC3.CompactSlice50
import CKLaneC3.CompactSlice51
import CKLaneC3.CompactSlice52
import CKLaneC3.CompactSlice53
import CKLaneC3.CompactSlice54
import CKLaneC3.CompactSlice55
import CKLaneC3.CompactSlice56
import CKLaneC3.CompactSlice57

/-! Lane C3 compact cover tree, part B (generated): the certified tag list and its
leaf identity, assembled structurally from the per-batch slice identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactTreeB
open GeneralCK.Certificates E8TAxisPartitionKernel E8TAxisRationalTreeBridgeKernel CKLaneC3.CompactCover CKLaneC3.CompactCoverF
open E8TAxisGeneratedGeometry (RatRect)

def allTags : List Tag := CompactBatch00.tags ++ (CompactBatch01.tags ++ (CompactBatch02.tags ++ (CompactBatch03.tags ++ (CompactBatch04.tags ++ (CompactBatch05.tags ++ (CompactBatch06.tags ++ (CompactBatch07.tags ++ (CompactBatch08.tags ++ (CompactBatch09.tags ++ (CompactBatch10.tags ++ (CompactBatch11.tags ++ (CompactBatch12.tags ++ (CompactBatch13.tags ++ (CompactBatch14.tags ++ (CompactBatch15.tags ++ (CompactBatch16.tags ++ (CompactBatch17.tags ++ (CompactBatch18.tags ++ (CompactBatch19.tags ++ (CompactBatch20.tags ++ (CompactBatch21.tags ++ (CompactBatch22.tags ++ (CompactBatch23.tags ++ (CompactBatch24.tags ++ (CompactBatch25.tags ++ (CompactBatch26.tags ++ (CompactBatch27.tags ++ (CompactBatch28.tags ++ (CompactBatch29.tags ++ (CompactBatch30.tags ++ (CompactBatch31.tags ++ (CompactBatch32.tags ++ (CompactBatch33.tags ++ (CompactBatch34.tags ++ (CompactBatch35.tags ++ (CompactBatch36.tags ++ (CompactBatch37.tags ++ (CompactBatch38.tags ++ (CompactBatch39.tags ++ (CompactBatch40.tags ++ (CompactBatch41.tags ++ (CompactBatch42.tags ++ (CompactBatch43.tags ++ (CompactBatch44.tags ++ (CompactBatch45.tags ++ (CompactBatch46.tags ++ (CompactBatch47.tags ++ (CompactBatch48.tags ++ (CompactBatch49.tags ++ (CompactBatch50.tags ++ (CompactBatch51.tags ++ (CompactBatch52.tags ++ (CompactBatch53.tags ++ (CompactBatch54.tags ++ (CompactBatch55.tags ++ (CompactBatch56.tags ++ (CompactBatch57.tags)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem leaves_eq : qLeaves CompactTreeA.tree CompactTreeA.D = allTags.map tagRect := by
  rw [CompactTreeA.leaves_eqR]
  simp only [allTags, CompactTreeA.rects, List.map_append, CompactSlice00.slice_eq, CompactSlice01.slice_eq, CompactSlice02.slice_eq, CompactSlice03.slice_eq, CompactSlice04.slice_eq, CompactSlice05.slice_eq, CompactSlice06.slice_eq, CompactSlice07.slice_eq, CompactSlice08.slice_eq, CompactSlice09.slice_eq, CompactSlice10.slice_eq, CompactSlice11.slice_eq, CompactSlice12.slice_eq, CompactSlice13.slice_eq, CompactSlice14.slice_eq, CompactSlice15.slice_eq, CompactSlice16.slice_eq, CompactSlice17.slice_eq, CompactSlice18.slice_eq, CompactSlice19.slice_eq, CompactSlice20.slice_eq, CompactSlice21.slice_eq, CompactSlice22.slice_eq, CompactSlice23.slice_eq, CompactSlice24.slice_eq, CompactSlice25.slice_eq, CompactSlice26.slice_eq, CompactSlice27.slice_eq, CompactSlice28.slice_eq, CompactSlice29.slice_eq, CompactSlice30.slice_eq, CompactSlice31.slice_eq, CompactSlice32.slice_eq, CompactSlice33.slice_eq, CompactSlice34.slice_eq, CompactSlice35.slice_eq, CompactSlice36.slice_eq, CompactSlice37.slice_eq, CompactSlice38.slice_eq, CompactSlice39.slice_eq, CompactSlice40.slice_eq, CompactSlice41.slice_eq, CompactSlice42.slice_eq, CompactSlice43.slice_eq, CompactSlice44.slice_eq, CompactSlice45.slice_eq, CompactSlice46.slice_eq, CompactSlice47.slice_eq, CompactSlice48.slice_eq, CompactSlice49.slice_eq, CompactSlice50.slice_eq, CompactSlice51.slice_eq, CompactSlice52.slice_eq, CompactSlice53.slice_eq, CompactSlice54.slice_eq, CompactSlice55.slice_eq, CompactSlice56.slice_eq, CompactSlice57.slice_eq]

theorem allTags_ok : allTags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [allTags, List.all_append, CompactBatch00.tags_ok, CompactBatch01.tags_ok, CompactBatch02.tags_ok, CompactBatch03.tags_ok, CompactBatch04.tags_ok, CompactBatch05.tags_ok, CompactBatch06.tags_ok, CompactBatch07.tags_ok, CompactBatch08.tags_ok, CompactBatch09.tags_ok, CompactBatch10.tags_ok, CompactBatch11.tags_ok, CompactBatch12.tags_ok, CompactBatch13.tags_ok, CompactBatch14.tags_ok, CompactBatch15.tags_ok, CompactBatch16.tags_ok, CompactBatch17.tags_ok, CompactBatch18.tags_ok, CompactBatch19.tags_ok, CompactBatch20.tags_ok, CompactBatch21.tags_ok, CompactBatch22.tags_ok, CompactBatch23.tags_ok, CompactBatch24.tags_ok, CompactBatch25.tags_ok, CompactBatch26.tags_ok, CompactBatch27.tags_ok, CompactBatch28.tags_ok, CompactBatch29.tags_ok, CompactBatch30.tags_ok, CompactBatch31.tags_ok, CompactBatch32.tags_ok, CompactBatch33.tags_ok, CompactBatch34.tags_ok, CompactBatch35.tags_ok, CompactBatch36.tags_ok, CompactBatch37.tags_ok, CompactBatch38.tags_ok, CompactBatch39.tags_ok, CompactBatch40.tags_ok, CompactBatch41.tags_ok, CompactBatch42.tags_ok, CompactBatch43.tags_ok, CompactBatch44.tags_ok, CompactBatch45.tags_ok, CompactBatch46.tags_ok, CompactBatch47.tags_ok, CompactBatch48.tags_ok, CompactBatch49.tags_ok, CompactBatch50.tags_ok, CompactBatch51.tags_ok, CompactBatch52.tags_ok, CompactBatch53.tags_ok, CompactBatch54.tags_ok, CompactBatch55.tags_ok, CompactBatch56.tags_ok, CompactBatch57.tags_ok, Bool.and_self]

end CKLaneC3.CompactTreeB
