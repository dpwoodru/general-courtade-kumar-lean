import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C004_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 10000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (7 / 25000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 307830041 322818022 3459052974780 5764899558052 5766084860109 307829579 53135821886327800))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 322818021 345876452 3459066579254 5764921117684 5766106423805 322817559 53136501615068184)))))
          (STree.leaf (SLeaf.v 307830041 345876452 5764880765430 17294076096542 17297281340867 307829579 91713120595610896)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (33 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 345876451 380464097 3459087562426 5764953399486 5766138711687 345875989 53137546467991928))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 380464096 427733879 3459119313884 5764997210503 5766182530919 380463634 53139114629413096)))))
          (STree.leaf (SLeaf.v 345876451 427733879 5764910626097 17294146540046 17297351793974 345875989 91714812689344096))))
      (STree.leaf (SLeaf.v 307830041 427733879 17294002078980 57646195134179 57652542467981 307829579 246809044091039840)))
    (STree.leaf (SLeaf.v 307830041 427733879 57645955326505 115291962534480 115291962623650 307829579 436200542554340096))

theorem check : STree.check (1 / 200000 : ℚ) tree (267 / 1000000000000 : ℚ) (371 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C004_0000
