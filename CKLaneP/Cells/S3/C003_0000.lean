import CKLaneP.SeamTree

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C003_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (23 / 100000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (1 / 5000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 222513850 230584301 3458973192612 5764815855951 5766001142521 222513388 53131893444906296))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 230584300 265171947 3458979187804 5764849636551 5766034929656 230583838 53132240656027360)))))
          (STree.leaf (SLeaf.v 222513850 265171947 5764803519690 17294020986894 17297226225522 222513388 91709131851648688)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (1 / 4000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 265171946 288230377 3459012391944 5764869236216 5766054532790 265171484 53133850603754256))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 288230376 307830042 3459034274394 5764886530039 5766071829754 288229914 53134916290459920)))))
          (STree.leaf (SLeaf.v 265171946 307830042 5764841911976 17294050847561 17297256089393 265171484 91711127077207920))))
      (STree.leaf (SLeaf.v 222513850 307830042 17293952733940 57646160546534 57652507889696 222513388 246806519610037536)))
    (STree.leaf (SLeaf.v 222513850 307830042 57645989914151 115292013263026 115292013359864 222513388 436200035033870272))

theorem check : STree.check (1 / 200000 : ℚ) tree (193 / 1000000000000 : ℚ) (267 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C003_0000
