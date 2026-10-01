import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1032 : RatBall :=
  ⟨⟨57/160, 19/160⟩, 3/320⟩
def center1032 : GaussianRat :=
  ⟨239711471/1000000000, 72866371/1000000000⟩
def contact1032 : RatBall := localContactBall tau1032 center1032
def work1032 : RoundedTauEval :=
  evalTau precision tau1032 contact1032 logTwoBall

theorem center_sq1032 : (center1032.re : ℝ)^2 +
    (center1032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1032 : work1032.theta.ok = true ∧
    work1032.jac.invOK = true ∧ acceptsUnitSq work1032.out = true := by
  norm_num [work1032, contact1032, tau1032, center1032, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1032 : CellCertificate where
  tauBall := tau1032
  contactCenter := center1032
  contactBall := contact1032
  work := work1032
  center_sq := center_sq1032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1032.1
  jac_ok := checks1032.2.1
  accepted := checks1032.2.2

def tau1033 : RatBall :=
  ⟨⟨59/160, 19/160⟩, 3/320⟩
def center1033 : GaussianRat :=
  ⟨247383851/1000000000, 72251673/1000000000⟩
def contact1033 : RatBall := localContactBall tau1033 center1033
def work1033 : RoundedTauEval :=
  evalTau precision tau1033 contact1033 logTwoBall

theorem center_sq1033 : (center1033.re : ℝ)^2 +
    (center1033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1033 : work1033.theta.ok = true ∧
    work1033.jac.invOK = true ∧ acceptsUnitSq work1033.out = true := by
  norm_num [work1033, contact1033, tau1033, center1033, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1033 : CellCertificate where
  tauBall := tau1033
  contactCenter := center1033
  contactBall := contact1033
  work := work1033
  center_sq := center_sq1033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1033.1
  jac_ok := checks1033.2.1
  accepted := checks1033.2.2

def tau1034 : RatBall :=
  ⟨⟨61/160, 17/160⟩, 3/320⟩
def center1034 : GaussianRat :=
  ⟨254392641/1000000000, 20019/312500⟩
def contact1034 : RatBall := localContactBall tau1034 center1034
def work1034 : RoundedTauEval :=
  evalTau precision tau1034 contact1034 logTwoBall

theorem center_sq1034 : (center1034.re : ℝ)^2 +
    (center1034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1034 : work1034.theta.ok = true ∧
    work1034.jac.invOK = true ∧ acceptsUnitSq work1034.out = true := by
  norm_num [work1034, contact1034, tau1034, center1034, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1034 : CellCertificate where
  tauBall := tau1034
  contactCenter := center1034
  contactBall := contact1034
  work := work1034
  center_sq := center_sq1034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1034.1
  jac_ok := checks1034.2.1
  accepted := checks1034.2.2

def tau1035 : RatBall :=
  ⟨⟨61/160, 19/160⟩, 3/320⟩
def center1035 : GaussianRat :=
  ⟨31873559/125000000, 7162653/100000000⟩
def contact1035 : RatBall := localContactBall tau1035 center1035
def work1035 : RoundedTauEval :=
  evalTau precision tau1035 contact1035 logTwoBall

theorem center_sq1035 : (center1035.re : ℝ)^2 +
    (center1035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1035 : work1035.theta.ok = true ∧
    work1035.jac.invOK = true ∧ acceptsUnitSq work1035.out = true := by
  norm_num [work1035, contact1035, tau1035, center1035, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1035 : CellCertificate where
  tauBall := tau1035
  contactCenter := center1035
  contactBall := contact1035
  work := work1035
  center_sq := center_sq1035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1035.1
  jac_ok := checks1035.2.1
  accepted := checks1035.2.2

def tau1036 : RatBall :=
  ⟨⟨57/160, 21/160⟩, 3/320⟩
def center1036 : GaussianRat :=
  ⟨120177071/500000000, 16115617/200000000⟩
def contact1036 : RatBall := localContactBall tau1036 center1036
def work1036 : RoundedTauEval :=
  evalTau precision tau1036 contact1036 logTwoBall

theorem center_sq1036 : (center1036.re : ℝ)^2 +
    (center1036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1036 : work1036.theta.ok = true ∧
    work1036.jac.invOK = true ∧ acceptsUnitSq work1036.out = true := by
  norm_num [work1036, contact1036, tau1036, center1036, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1036 : CellCertificate where
  tauBall := tau1036
  contactCenter := center1036
  contactBall := contact1036
  work := work1036
  center_sq := center_sq1036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1036.1
  jac_ok := checks1036.2.1
  accepted := checks1036.2.2

def tau1037 : RatBall :=
  ⟨⟨59/160, 21/160⟩, 3/320⟩
def center1037 : GaussianRat :=
  ⟨124018963/500000000, 79895753/1000000000⟩
def contact1037 : RatBall := localContactBall tau1037 center1037
def work1037 : RoundedTauEval :=
  evalTau precision tau1037 contact1037 logTwoBall

theorem center_sq1037 : (center1037.re : ℝ)^2 +
    (center1037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1037 : work1037.theta.ok = true ∧
    work1037.jac.invOK = true ∧ acceptsUnitSq work1037.out = true := by
  norm_num [work1037, contact1037, tau1037, center1037, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1037 : CellCertificate where
  tauBall := tau1037
  contactCenter := center1037
  contactBall := contact1037
  work := work1037
  center_sq := center_sq1037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1037.1
  jac_ok := checks1037.2.1
  accepted := checks1037.2.2

def tau1038 : RatBall :=
  ⟨⟨57/160, 23/160⟩, 3/320⟩
def center1038 : GaussianRat :=
  ⟨30133041/125000000, 17660441/200000000⟩
def contact1038 : RatBall := localContactBall tau1038 center1038
def work1038 : RoundedTauEval :=
  evalTau precision tau1038 contact1038 logTwoBall

theorem center_sq1038 : (center1038.re : ℝ)^2 +
    (center1038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1038 : work1038.theta.ok = true ∧
    work1038.jac.invOK = true ∧ acceptsUnitSq work1038.out = true := by
  norm_num [work1038, contact1038, tau1038, center1038, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1038 : CellCertificate where
  tauBall := tau1038
  contactCenter := center1038
  contactBall := contact1038
  work := work1038
  center_sq := center_sq1038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1038.1
  jac_ok := checks1038.2.1
  accepted := checks1038.2.2

def tau1039 : RatBall :=
  ⟨⟨59/160, 23/160⟩, 3/320⟩
def center1039 : GaussianRat :=
  ⟨248760621/1000000000, 43775671/500000000⟩
def contact1039 : RatBall := localContactBall tau1039 center1039
def work1039 : RoundedTauEval :=
  evalTau precision tau1039 contact1039 logTwoBall

theorem center_sq1039 : (center1039.re : ℝ)^2 +
    (center1039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1039 : work1039.theta.ok = true ∧
    work1039.jac.invOK = true ∧ acceptsUnitSq work1039.out = true := by
  norm_num [work1039, contact1039, tau1039, center1039, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell1039 : CellCertificate where
  tauBall := tau1039
  contactCenter := center1039
  contactBall := contact1039
  work := work1039
  center_sq := center_sq1039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1039.1
  jac_ok := checks1039.2.1
  accepted := checks1039.2.2

def cells : List CellCertificate := [cell1032, cell1033, cell1034, cell1035, cell1036, cell1037, cell1038, cell1039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129
