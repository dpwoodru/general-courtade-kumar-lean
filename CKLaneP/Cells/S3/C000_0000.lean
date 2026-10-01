import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C000_0000

open CKLaneP

def tree : STree :=
  STree.st (49999 / 500000 : ℚ)
    (STree.leaf SLeaf.tq)
    (STree.leaf (SLeaf.v 0 115292151 5764480701899 115292265752836 115292265843028 0 91696373138268448))

theorem check : STree.check (1 / 200000 : ℚ) tree (0 : ℚ) (1 / 10000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C000_0000
