import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C035_0002

open CKLaneP

def tree : STree :=
  STree.leaf (SLeaf.v 7920570736649 10987341938904 54579304028088 110438350926290 110437700024649 7920452747191 465977954204871616)

theorem check : STree.check (1 / 200000 : ℚ) tree (687 / 100000000 : ℚ) (953 / 100000000 : ℚ) (1 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C035_0002
