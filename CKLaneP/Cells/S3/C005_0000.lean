import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C005_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 2500000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (39 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 427733878 449639387 3459165269335 5765014389034 5766199712306 427733415 53141294114940312))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 449639386 461168602 3459186483091 5765023727698 5766209052564 449638923 53142300351591760)))))
          (STree.leaf (SLeaf.v 427733878 461168602 5764989140052 17294155417542 17297360670160 427733415 91718670295206160)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (9 / 20000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 461168601 518814678 3459194553541 5765080220852 5766265556669 461168138 53142777475753728))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 518814677 592601654 3459247772398 5765148243220 5766333591750 518814214 53145373386355056)))))
          (STree.leaf (SLeaf.v 461168601 592601654 5765009431470 17294276820176 17297482090396 461168138 91720045161096208))))
      (STree.leaf (SLeaf.v 427733878 592601654 17294072522484 57646240098118 57652587418761 427733415 246812567151341184)))
    (STree.leaf (SLeaf.v 427733878 592601654 57645910362567 115291887594582 115291887673783 427733415 436201255188398592))

theorem check : STree.check (1 / 200000 : ℚ) tree (371 / 1000000000000 : ℚ) (257 / 500000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C005_0000
