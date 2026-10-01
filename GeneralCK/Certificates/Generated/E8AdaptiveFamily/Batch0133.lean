import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1064 : RatBall :=
  ⟨⟨11/160, 9/32⟩, 3/320⟩
def center1064 : GaussianRat :=
  ⟨25896777/500000000, 199440199/1000000000⟩
def contact1064 : RatBall := localContactBall tau1064 center1064
def work1064 : RoundedTauEval :=
  evalTau precision tau1064 contact1064 logTwoBall

theorem center_sq1064 : (center1064.re : ℝ)^2 +
    (center1064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1064 : work1064.theta.ok = true ∧
    work1064.jac.invOK = true ∧ acceptsUnitSq work1064.out = true := by
  norm_num [work1064, contact1064, tau1064, center1064, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1064 : CellCertificate where
  tauBall := tau1064
  contactCenter := center1064
  contactBall := contact1064
  work := work1064
  center_sq := center_sq1064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1064.1
  jac_ok := checks1064.2.1
  accepted := checks1064.2.2

def tau1065 : RatBall :=
  ⟨⟨9/160, 47/160⟩, 3/320⟩
def center1065 : GaussianRat :=
  ⟨42754839/1000000000, 41848559/200000000⟩
def contact1065 : RatBall := localContactBall tau1065 center1065
def work1065 : RoundedTauEval :=
  evalTau precision tau1065 contact1065 logTwoBall

theorem center_sq1065 : (center1065.re : ℝ)^2 +
    (center1065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1065 : work1065.theta.ok = true ∧
    work1065.jac.invOK = true ∧ acceptsUnitSq work1065.out = true := by
  norm_num [work1065, contact1065, tau1065, center1065, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1065 : CellCertificate where
  tauBall := tau1065
  contactCenter := center1065
  contactBall := contact1065
  work := work1065
  center_sq := center_sq1065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1065.1
  jac_ok := checks1065.2.1
  accepted := checks1065.2.2

def tau1066 : RatBall :=
  ⟨⟨11/160, 47/160⟩, 3/320⟩
def center1066 : GaussianRat :=
  ⟨13053307/250000000, 208849073/1000000000⟩
def contact1066 : RatBall := localContactBall tau1066 center1066
def work1066 : RoundedTauEval :=
  evalTau precision tau1066 contact1066 logTwoBall

theorem center_sq1066 : (center1066.re : ℝ)^2 +
    (center1066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1066 : work1066.theta.ok = true ∧
    work1066.jac.invOK = true ∧ acceptsUnitSq work1066.out = true := by
  norm_num [work1066, contact1066, tau1066, center1066, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1066 : CellCertificate where
  tauBall := tau1066
  contactCenter := center1066
  contactBall := contact1066
  work := work1066
  center_sq := center_sq1066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1066.1
  jac_ok := checks1066.2.1
  accepted := checks1066.2.2

def tau1067 : RatBall :=
  ⟨⟨13/160, 9/32⟩, 3/320⟩
def center1067 : GaussianRat :=
  ⟨30576347/500000000, 99498463/500000000⟩
def contact1067 : RatBall := localContactBall tau1067 center1067
def work1067 : RoundedTauEval :=
  evalTau precision tau1067 contact1067 logTwoBall

theorem center_sq1067 : (center1067.re : ℝ)^2 +
    (center1067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1067 : work1067.theta.ok = true ∧
    work1067.jac.invOK = true ∧ acceptsUnitSq work1067.out = true := by
  norm_num [work1067, contact1067, tau1067, center1067, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1067 : CellCertificate where
  tauBall := tau1067
  contactCenter := center1067
  contactBall := contact1067
  work := work1067
  center_sq := center_sq1067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1067.1
  jac_ok := checks1067.2.1
  accepted := checks1067.2.2

def tau1068 : RatBall :=
  ⟨⟨3/32, 9/32⟩, 3/320⟩
def center1068 : GaussianRat :=
  ⟨17620809/250000000, 24810311/125000000⟩
def contact1068 : RatBall := localContactBall tau1068 center1068
def work1068 : RoundedTauEval :=
  evalTau precision tau1068 contact1068 logTwoBall

theorem center_sq1068 : (center1068.re : ℝ)^2 +
    (center1068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1068 : work1068.theta.ok = true ∧
    work1068.jac.invOK = true ∧ acceptsUnitSq work1068.out = true := by
  norm_num [work1068, contact1068, tau1068, center1068, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1068 : CellCertificate where
  tauBall := tau1068
  contactCenter := center1068
  contactBall := contact1068
  work := work1068
  center_sq := center_sq1068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1068.1
  jac_ok := checks1068.2.1
  accepted := checks1068.2.2

def tau1069 : RatBall :=
  ⟨⟨13/160, 47/160⟩, 3/320⟩
def center1069 : GaussianRat :=
  ⟨61646237/1000000000, 5209469/25000000⟩
def contact1069 : RatBall := localContactBall tau1069 center1069
def work1069 : RoundedTauEval :=
  evalTau precision tau1069 contact1069 logTwoBall

theorem center_sq1069 : (center1069.re : ℝ)^2 +
    (center1069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1069 : work1069.theta.ok = true ∧
    work1069.jac.invOK = true ∧ acceptsUnitSq work1069.out = true := by
  norm_num [work1069, contact1069, tau1069, center1069, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1069 : CellCertificate where
  tauBall := tau1069
  contactCenter := center1069
  contactBall := contact1069
  work := work1069
  center_sq := center_sq1069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1069.1
  jac_ok := checks1069.2.1
  accepted := checks1069.2.2

def tau1070 : RatBall :=
  ⟨⟨3/32, 47/160⟩, 3/320⟩
def center1070 : GaussianRat :=
  ⟨71049459/1000000000, 207833009/1000000000⟩
def contact1070 : RatBall := localContactBall tau1070 center1070
def work1070 : RoundedTauEval :=
  evalTau precision tau1070 contact1070 logTwoBall

theorem center_sq1070 : (center1070.re : ℝ)^2 +
    (center1070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1070 : work1070.theta.ok = true ∧
    work1070.jac.invOK = true ∧ acceptsUnitSq work1070.out = true := by
  norm_num [work1070, contact1070, tau1070, center1070, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1070 : CellCertificate where
  tauBall := tau1070
  contactCenter := center1070
  contactBall := contact1070
  work := work1070
  center_sq := center_sq1070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1070.1
  jac_ok := checks1070.2.1
  accepted := checks1070.2.2

def tau1071 : RatBall :=
  ⟨⟨5/32, 37/160⟩, 3/320⟩
def center1071 : GaussianRat :=
  ⟨113439149/1000000000, 158939613/1000000000⟩
def contact1071 : RatBall := localContactBall tau1071 center1071
def work1071 : RoundedTauEval :=
  evalTau precision tau1071 contact1071 logTwoBall

theorem center_sq1071 : (center1071.re : ℝ)^2 +
    (center1071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1071 : work1071.theta.ok = true ∧
    work1071.jac.invOK = true ∧ acceptsUnitSq work1071.out = true := by
  norm_num [work1071, contact1071, tau1071, center1071, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1071 : CellCertificate where
  tauBall := tau1071
  contactCenter := center1071
  contactBall := contact1071
  work := work1071
  center_sq := center_sq1071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1071.1
  jac_ok := checks1071.2.1
  accepted := checks1071.2.2

def cells : List CellCertificate := [cell1064, cell1065, cell1066, cell1067, cell1068, cell1069, cell1070, cell1071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133
