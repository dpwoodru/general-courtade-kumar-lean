import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1000 : RatBall :=
  ⟨⟨61/160, 3/32⟩, 3/320⟩
def center1000 : GaussianRat :=
  ⟨50772973/200000000, 14125933/250000000⟩
def contact1000 : RatBall := localContactBall tau1000 center1000
def work1000 : RoundedTauEval :=
  evalTau precision tau1000 contact1000 logTwoBall

theorem center_sq1000 : (center1000.re : ℝ)^2 +
    (center1000.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1000 : work1000.theta.ok = true ∧
    work1000.jac.invOK = true ∧ acceptsUnitSq work1000.out = true := by
  norm_num [work1000, contact1000, tau1000, center1000, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1000 : CellCertificate where
  tauBall := tau1000
  contactCenter := center1000
  contactBall := contact1000
  work := work1000
  center_sq := center_sq1000
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1000.1
  jac_ok := checks1000.2.1
  accepted := checks1000.2.2

def tau1001 : RatBall :=
  ⟨⟨63/160, 3/32⟩, 3/320⟩
def center1001 : GaussianRat :=
  ⟨65346019/250000000, 28003013/500000000⟩
def contact1001 : RatBall := localContactBall tau1001 center1001
def work1001 : RoundedTauEval :=
  evalTau precision tau1001 contact1001 logTwoBall

theorem center_sq1001 : (center1001.re : ℝ)^2 +
    (center1001.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1001]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1001 : work1001.theta.ok = true ∧
    work1001.jac.invOK = true ∧ acceptsUnitSq work1001.out = true := by
  norm_num [work1001, contact1001, tau1001, center1001, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1001 : CellCertificate where
  tauBall := tau1001
  contactCenter := center1001
  contactBall := contact1001
  work := work1001
  center_sq := center_sq1001
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1001.1
  jac_ok := checks1001.2.1
  accepted := checks1001.2.2

def tau1002 : RatBall :=
  ⟨⟨37/160, 29/160⟩, 3/320⟩
def center1002 : GaussianRat :=
  ⟨81239917/500000000, 60019727/500000000⟩
def contact1002 : RatBall := localContactBall tau1002 center1002
def work1002 : RoundedTauEval :=
  evalTau precision tau1002 contact1002 logTwoBall

theorem center_sq1002 : (center1002.re : ℝ)^2 +
    (center1002.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1002]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1002 : work1002.theta.ok = true ∧
    work1002.jac.invOK = true ∧ acceptsUnitSq work1002.out = true := by
  norm_num [work1002, contact1002, tau1002, center1002, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1002 : CellCertificate where
  tauBall := tau1002
  contactCenter := center1002
  contactBall := contact1002
  work := work1002
  center_sq := center_sq1002
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1002.1
  jac_ok := checks1002.2.1
  accepted := checks1002.2.2

def tau1003 : RatBall :=
  ⟨⟨39/160, 29/160⟩, 3/320⟩
def center1003 : GaussianRat :=
  ⟨2135923/12500000, 119305389/1000000000⟩
def contact1003 : RatBall := localContactBall tau1003 center1003
def work1003 : RoundedTauEval :=
  evalTau precision tau1003 contact1003 logTwoBall

theorem center_sq1003 : (center1003.re : ℝ)^2 +
    (center1003.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1003]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1003 : work1003.theta.ok = true ∧
    work1003.jac.invOK = true ∧ acceptsUnitSq work1003.out = true := by
  norm_num [work1003, contact1003, tau1003, center1003, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1003 : CellCertificate where
  tauBall := tau1003
  contactCenter := center1003
  contactBall := contact1003
  work := work1003
  center_sq := center_sq1003
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1003.1
  jac_ok := checks1003.2.1
  accepted := checks1003.2.2

def tau1004 : RatBall :=
  ⟨⟨37/160, 31/160⟩, 3/320⟩
def center1004 : GaussianRat :=
  ⟨163226979/1000000000, 128476919/1000000000⟩
def contact1004 : RatBall := localContactBall tau1004 center1004
def work1004 : RoundedTauEval :=
  evalTau precision tau1004 contact1004 logTwoBall

theorem center_sq1004 : (center1004.re : ℝ)^2 +
    (center1004.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1004]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1004 : work1004.theta.ok = true ∧
    work1004.jac.invOK = true ∧ acceptsUnitSq work1004.out = true := by
  norm_num [work1004, contact1004, tau1004, center1004, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1004 : CellCertificate where
  tauBall := tau1004
  contactCenter := center1004
  contactBall := contact1004
  work := work1004
  center_sq := center_sq1004
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1004.1
  jac_ok := checks1004.2.1
  accepted := checks1004.2.2

def tau1005 : RatBall :=
  ⟨⟨39/160, 31/160⟩, 3/320⟩
def center1005 : GaussianRat :=
  ⟨10728219/62500000, 127685733/1000000000⟩
def contact1005 : RatBall := localContactBall tau1005 center1005
def work1005 : RoundedTauEval :=
  evalTau precision tau1005 contact1005 logTwoBall

theorem center_sq1005 : (center1005.re : ℝ)^2 +
    (center1005.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1005]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1005 : work1005.theta.ok = true ∧
    work1005.jac.invOK = true ∧ acceptsUnitSq work1005.out = true := by
  norm_num [work1005, contact1005, tau1005, center1005, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1005 : CellCertificate where
  tauBall := tau1005
  contactCenter := center1005
  contactBall := contact1005
  work := work1005
  center_sq := center_sq1005
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1005.1
  jac_ok := checks1005.2.1
  accepted := checks1005.2.2

def tau1006 : RatBall :=
  ⟨⟨9/32, 5/32⟩, 3/320⟩
def center1006 : GaussianRat :=
  ⟨194169161/1000000000, 100614871/1000000000⟩
def contact1006 : RatBall := localContactBall tau1006 center1006
def work1006 : RoundedTauEval :=
  evalTau precision tau1006 contact1006 logTwoBall

theorem center_sq1006 : (center1006.re : ℝ)^2 +
    (center1006.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1006]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1006 : work1006.theta.ok = true ∧
    work1006.jac.invOK = true ∧ acceptsUnitSq work1006.out = true := by
  norm_num [work1006, contact1006, tau1006, center1006, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1006 : CellCertificate where
  tauBall := tau1006
  contactCenter := center1006
  contactBall := contact1006
  work := work1006
  center_sq := center_sq1006
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1006.1
  jac_ok := checks1006.2.1
  accepted := checks1006.2.2

def tau1007 : RatBall :=
  ⟨⟨47/160, 5/32⟩, 3/320⟩
def center1007 : GaussianRat :=
  ⟨202276259/1000000000, 49949641/500000000⟩
def contact1007 : RatBall := localContactBall tau1007 center1007
def work1007 : RoundedTauEval :=
  evalTau precision tau1007 contact1007 logTwoBall

theorem center_sq1007 : (center1007.re : ℝ)^2 +
    (center1007.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1007]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1007 : work1007.theta.ok = true ∧
    work1007.jac.invOK = true ∧ acceptsUnitSq work1007.out = true := by
  norm_num [work1007, contact1007, tau1007, center1007, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1007 : CellCertificate where
  tauBall := tau1007
  contactCenter := center1007
  contactBall := contact1007
  work := work1007
  center_sq := center_sq1007
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1007.1
  jac_ok := checks1007.2.1
  accepted := checks1007.2.2

def cells : List CellCertificate := [cell1000, cell1001, cell1002, cell1003, cell1004, cell1005, cell1006, cell1007]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125
