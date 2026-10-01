import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C034_0005

open CKLaneP

def tree : STree :=
  STree.leaf (SLeaf.v 5706961447803 7920570736650 55432465941497 111798798301726 111798322659519 5706900318437 458445957944841280)

theorem check : STree.check (1 / 200000 : ℚ) tree (99 / 20000000 : ℚ) (687 / 100000000 : ℚ) (1 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C034_0005
