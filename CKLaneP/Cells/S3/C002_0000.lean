import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C002_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 6250000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (3 / 20000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 160256089 172938226 3458914393616 5764764435652 5765949712814 160255627 53128990264723416))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 172938225 184467441 3458926383999 5764774696653 5765959975690 172937763 53129584116160760)))))
          (STree.leaf (SLeaf.v 160256089 184467441 5764749332379 17293958959717 17297164190830 160255627 91706229691946544)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (9 / 50000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 184467440 207525871 3458936529709 5764796602161 5765981885368 184466978 53130110257452880))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 207525870 222513851 3458958688860 5764809284298 5765994569741 207525408 53131191070845848)))))
          (STree.leaf (SLeaf.v 184467440 222513851 5764769739089 17293989742721 17297194977782 184466978 91707350622348560))))
      (STree.leaf (SLeaf.v 160256089 222513851 17293916071036 57646137488104 57652484838099 160255627 246804652109565472)))
    (STree.leaf (SLeaf.v 160256089 222513851 57646012972581 115292052462357 115292052564308 160255627 436199656108441088))

theorem check : STree.check (1 / 200000 : ℚ) tree (139 / 1000000000000 : ℚ) (193 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C002_0000
