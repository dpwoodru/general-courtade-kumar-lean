import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C001_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 25000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (11 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 115292150 126821366 3458872196689 5764722815185 5765908084674 115291688 53126878555977008))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 126821365 138350581 3458883034151 5764733191479 5765918462877 126820903 53127422220830744)))))
          (STree.leaf (SLeaf.v 115292150 138350581 5764708980126 17293926332039 17297131559598 115291688 91704093611731120)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (13 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 138350580 149879796 3458893871613 5764743567772 5765928841080 138350118 53127964502187272))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 149879795 160256090 3458904778250 5764752791144 5765938066135 149879333 53128506675874048)))))
          (STree.leaf (SLeaf.v 138350580 160256090 5764729848005 17293941320018 17297146549131 138350118 91705194403255840))))
      (STree.leaf (SLeaf.v 115292150 160256090 17293889784426 57646120194282 57652467549211 115291688 246803291751113632)))
    (STree.leaf (SLeaf.v 115292150 160256090 57646030266403 115292080132473 115292080238258 115291688 436199380713921792))

theorem check : STree.check (1 / 200000 : ℚ) tree (1 / 10000000000 : ℚ) (139 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C001_0000
