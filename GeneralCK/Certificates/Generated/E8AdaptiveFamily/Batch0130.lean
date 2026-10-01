import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1040 : RatBall :=
  ⟨⟨61/160, 21/160⟩, 3/320⟩
def center1040 : GaussianRat :=
  ⟨15978319/62500000, 79201909/1000000000⟩
def contact1040 : RatBall := localContactBall tau1040 center1040
def work1040 : RoundedTauEval :=
  evalTau precision tau1040 contact1040 logTwoBall

theorem center_sq1040 : (center1040.re : ℝ)^2 +
    (center1040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1040 : work1040.theta.ok = true ∧
    work1040.jac.invOK = true ∧ acceptsUnitSq work1040.out = true := by
  norm_num [work1040, contact1040, tau1040, center1040, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1040 : CellCertificate where
  tauBall := tau1040
  contactCenter := center1040
  contactBall := contact1040
  work := work1040
  center_sq := center_sq1040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1040.1
  jac_ok := checks1040.2.1
  accepted := checks1040.2.2

def tau1041 : RatBall :=
  ⟨⟨61/160, 23/160⟩, 3/320⟩
def center1041 : GaussianRat :=
  ⟨64096843/250000000, 86787913/1000000000⟩
def contact1041 : RatBall := localContactBall tau1041 center1041
def work1041 : RoundedTauEval :=
  evalTau precision tau1041 contact1041 logTwoBall

theorem center_sq1041 : (center1041.re : ℝ)^2 +
    (center1041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1041 : work1041.theta.ok = true ∧
    work1041.jac.invOK = true ∧ acceptsUnitSq work1041.out = true := by
  norm_num [work1041, contact1041, tau1041, center1041, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1041 : CellCertificate where
  tauBall := tau1041
  contactCenter := center1041
  contactBall := contact1041
  work := work1041
  center_sq := center_sq1041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1041.1
  jac_ok := checks1041.2.1
  accepted := checks1041.2.2

def tau1042 : RatBall :=
  ⟨⟨49/160, 5/32⟩, 3/320⟩
def center1042 : GaussianRat :=
  ⟨52580197/250000000, 1239543/12500000⟩
def contact1042 : RatBall := localContactBall tau1042 center1042
def work1042 : RoundedTauEval :=
  evalTau precision tau1042 contact1042 logTwoBall

theorem center_sq1042 : (center1042.re : ℝ)^2 +
    (center1042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1042 : work1042.theta.ok = true ∧
    work1042.jac.invOK = true ∧ acceptsUnitSq work1042.out = true := by
  norm_num [work1042, contact1042, tau1042, center1042, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1042 : CellCertificate where
  tauBall := tau1042
  contactCenter := center1042
  contactBall := contact1042
  work := work1042
  center_sq := center_sq1042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1042.1
  jac_ok := checks1042.2.1
  accepted := checks1042.2.2

def tau1043 : RatBall :=
  ⟨⟨51/160, 5/32⟩, 3/320⟩
def center1043 : GaussianRat :=
  ⟨5457529/25000000, 49204231/500000000⟩
def contact1043 : RatBall := localContactBall tau1043 center1043
def work1043 : RoundedTauEval :=
  evalTau precision tau1043 contact1043 logTwoBall

theorem center_sq1043 : (center1043.re : ℝ)^2 +
    (center1043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1043 : work1043.theta.ok = true ∧
    work1043.jac.invOK = true ∧ acceptsUnitSq work1043.out = true := by
  norm_num [work1043, contact1043, tau1043, center1043, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1043 : CellCertificate where
  tauBall := tau1043
  contactCenter := center1043
  contactBall := contact1043
  work := work1043
  center_sq := center_sq1043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1043.1
  jac_ok := checks1043.2.1
  accepted := checks1043.2.2

def tau1044 : RatBall :=
  ⟨⟨49/160, 27/160⟩, 3/320⟩
def center1044 : GaussianRat :=
  ⟨211098659/1000000000, 10718597/100000000⟩
def contact1044 : RatBall := localContactBall tau1044 center1044
def work1044 : RoundedTauEval :=
  evalTau precision tau1044 contact1044 logTwoBall

theorem center_sq1044 : (center1044.re : ℝ)^2 +
    (center1044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1044 : work1044.theta.ok = true ∧
    work1044.jac.invOK = true ∧ acceptsUnitSq work1044.out = true := by
  norm_num [work1044, contact1044, tau1044, center1044, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1044 : CellCertificate where
  tauBall := tau1044
  contactCenter := center1044
  contactBall := contact1044
  work := work1044
  center_sq := center_sq1044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1044.1
  jac_ok := checks1044.2.1
  accepted := checks1044.2.2

def tau1045 : RatBall :=
  ⟨⟨51/160, 27/160⟩, 3/320⟩
def center1045 : GaussianRat :=
  ⟨219098349/1000000000, 53182749/500000000⟩
def contact1045 : RatBall := localContactBall tau1045 center1045
def work1045 : RoundedTauEval :=
  evalTau precision tau1045 contact1045 logTwoBall

theorem center_sq1045 : (center1045.re : ℝ)^2 +
    (center1045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1045 : work1045.theta.ok = true ∧
    work1045.jac.invOK = true ∧ acceptsUnitSq work1045.out = true := by
  norm_num [work1045, contact1045, tau1045, center1045, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1045 : CellCertificate where
  tauBall := tau1045
  contactCenter := center1045
  contactBall := contact1045
  work := work1045
  center_sq := center_sq1045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1045.1
  jac_ok := checks1045.2.1
  accepted := checks1045.2.2

def tau1046 : RatBall :=
  ⟨⟨53/160, 5/32⟩, 3/320⟩
def center1046 : GaussianRat :=
  ⟨226215887/1000000000, 24408867/250000000⟩
def contact1046 : RatBall := localContactBall tau1046 center1046
def work1046 : RoundedTauEval :=
  evalTau precision tau1046 contact1046 logTwoBall

theorem center_sq1046 : (center1046.re : ℝ)^2 +
    (center1046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1046 : work1046.theta.ok = true ∧
    work1046.jac.invOK = true ∧ acceptsUnitSq work1046.out = true := by
  norm_num [work1046, contact1046, tau1046, center1046, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1046 : CellCertificate where
  tauBall := tau1046
  contactCenter := center1046
  contactBall := contact1046
  work := work1046
  center_sq := center_sq1046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1046.1
  jac_ok := checks1046.2.1
  accepted := checks1046.2.2

def tau1047 : RatBall :=
  ⟨⟨11/32, 5/32⟩, 3/320⟩
def center1047 : GaussianRat :=
  ⟨234063587/1000000000, 96845571/1000000000⟩
def contact1047 : RatBall := localContactBall tau1047 center1047
def work1047 : RoundedTauEval :=
  evalTau precision tau1047 contact1047 logTwoBall

theorem center_sq1047 : (center1047.re : ℝ)^2 +
    (center1047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1047 : work1047.theta.ok = true ∧
    work1047.jac.invOK = true ∧ acceptsUnitSq work1047.out = true := by
  norm_num [work1047, contact1047, tau1047, center1047, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1047 : CellCertificate where
  tauBall := tau1047
  contactCenter := center1047
  contactBall := contact1047
  work := work1047
  center_sq := center_sq1047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1047.1
  jac_ok := checks1047.2.1
  accepted := checks1047.2.2

def cells : List CellCertificate := [cell1040, cell1041, cell1042, cell1043, cell1044, cell1045, cell1046, cell1047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130
