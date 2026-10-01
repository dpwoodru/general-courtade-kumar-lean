import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1024 : RatBall :=
  ⟨⟨49/160, 23/160⟩, 3/320⟩
def center1024 : GaussianRat :=
  ⟨209607093/1000000000, 22790011/250000000⟩
def contact1024 : RatBall := localContactBall tau1024 center1024
def work1024 : RoundedTauEval :=
  evalTau precision tau1024 contact1024 logTwoBall

theorem center_sq1024 : (center1024.re : ℝ)^2 +
    (center1024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1024 : work1024.theta.ok = true ∧
    work1024.jac.invOK = true ∧ acceptsUnitSq work1024.out = true := by
  norm_num [work1024, contact1024, tau1024, center1024, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1024 : CellCertificate where
  tauBall := tau1024
  contactCenter := center1024
  contactBall := contact1024
  work := work1024
  center_sq := center_sq1024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1024.1
  jac_ok := checks1024.2.1
  accepted := checks1024.2.2

def tau1025 : RatBall :=
  ⟨⟨51/160, 23/160⟩, 3/320⟩
def center1025 : GaussianRat :=
  ⟨6799051/31250000, 90469443/1000000000⟩
def contact1025 : RatBall := localContactBall tau1025 center1025
def work1025 : RoundedTauEval :=
  evalTau precision tau1025 contact1025 logTwoBall

theorem center_sq1025 : (center1025.re : ℝ)^2 +
    (center1025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1025 : work1025.theta.ok = true ∧
    work1025.jac.invOK = true ∧ acceptsUnitSq work1025.out = true := by
  norm_num [work1025, contact1025, tau1025, center1025, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1025 : CellCertificate where
  tauBall := tau1025
  contactCenter := center1025
  contactBall := contact1025
  work := work1025
  center_sq := center_sq1025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1025.1
  jac_ok := checks1025.2.1
  accepted := checks1025.2.2

def tau1026 : RatBall :=
  ⟨⟨53/160, 21/160⟩, 3/320⟩
def center1026 : GaussianRat :=
  ⟨224785281/1000000000, 4095231/50000000⟩
def contact1026 : RatBall := localContactBall tau1026 center1026
def work1026 : RoundedTauEval :=
  evalTau precision tau1026 contact1026 logTwoBall

theorem center_sq1026 : (center1026.re : ℝ)^2 +
    (center1026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1026 : work1026.theta.ok = true ∧
    work1026.jac.invOK = true ∧ acceptsUnitSq work1026.out = true := by
  norm_num [work1026, contact1026, tau1026, center1026, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1026 : CellCertificate where
  tauBall := tau1026
  contactCenter := center1026
  contactBall := contact1026
  work := work1026
  center_sq := center_sq1026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1026.1
  jac_ok := checks1026.2.1
  accepted := checks1026.2.2

def tau1027 : RatBall :=
  ⟨⟨11/32, 21/160⟩, 3/320⟩
def center1027 : GaussianRat :=
  ⟨232602861/1000000000, 81248009/1000000000⟩
def contact1027 : RatBall := localContactBall tau1027 center1027
def work1027 : RoundedTauEval :=
  evalTau precision tau1027 contact1027 logTwoBall

theorem center_sq1027 : (center1027.re : ℝ)^2 +
    (center1027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1027 : work1027.theta.ok = true ∧
    work1027.jac.invOK = true ∧ acceptsUnitSq work1027.out = true := by
  norm_num [work1027, contact1027, tau1027, center1027, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1027 : CellCertificate where
  tauBall := tau1027
  contactCenter := center1027
  contactBall := contact1027
  work := work1027
  center_sq := center_sq1027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1027.1
  jac_ok := checks1027.2.1
  accepted := checks1027.2.2

def tau1028 : RatBall :=
  ⟨⟨53/160, 23/160⟩, 3/320⟩
def center1028 : GaussianRat :=
  ⟨225467593/1000000000, 89762261/1000000000⟩
def contact1028 : RatBall := localContactBall tau1028 center1028
def work1028 : RoundedTauEval :=
  evalTau precision tau1028 contact1028 logTwoBall

theorem center_sq1028 : (center1028.re : ℝ)^2 +
    (center1028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1028 : work1028.theta.ok = true ∧
    work1028.jac.invOK = true ∧ acceptsUnitSq work1028.out = true := by
  norm_num [work1028, contact1028, tau1028, center1028, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1028 : CellCertificate where
  tauBall := tau1028
  contactCenter := center1028
  contactBall := contact1028
  work := work1028
  center_sq := center_sq1028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1028.1
  jac_ok := checks1028.2.1
  accepted := checks1028.2.2

def tau1029 : RatBall :=
  ⟨⟨11/32, 23/160⟩, 3/320⟩
def center1029 : GaussianRat :=
  ⟨58324897/250000000, 11129939/125000000⟩
def contact1029 : RatBall := localContactBall tau1029 center1029
def work1029 : RoundedTauEval :=
  evalTau precision tau1029 contact1029 logTwoBall

theorem center_sq1029 : (center1029.re : ℝ)^2 +
    (center1029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1029 : work1029.theta.ok = true ∧
    work1029.jac.invOK = true ∧ acceptsUnitSq work1029.out = true := by
  norm_num [work1029, contact1029, tau1029, center1029, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1029 : CellCertificate where
  tauBall := tau1029
  contactCenter := center1029
  contactBall := contact1029
  work := work1029
  center_sq := center_sq1029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1029.1
  jac_ok := checks1029.2.1
  accepted := checks1029.2.2

def tau1030 : RatBall :=
  ⟨⟨57/160, 17/160⟩, 3/320⟩
def center1030 : GaussianRat :=
  ⟨119567729/500000000, 32582953/500000000⟩
def contact1030 : RatBall := localContactBall tau1030 center1030
def work1030 : RoundedTauEval :=
  evalTau precision tau1030 contact1030 logTwoBall

theorem center_sq1030 : (center1030.re : ℝ)^2 +
    (center1030.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1030]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1030 : work1030.theta.ok = true ∧
    work1030.jac.invOK = true ∧ acceptsUnitSq work1030.out = true := by
  norm_num [work1030, contact1030, tau1030, center1030, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1030 : CellCertificate where
  tauBall := tau1030
  contactCenter := center1030
  contactBall := contact1030
  work := work1030
  center_sq := center_sq1030
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1030.1
  jac_ok := checks1030.2.1
  accepted := checks1030.2.2

def tau1031 : RatBall :=
  ⟨⟨59/160, 17/160⟩, 3/320⟩
def center1031 : GaussianRat :=
  ⟨15424847/62500000, 32309019/500000000⟩
def contact1031 : RatBall := localContactBall tau1031 center1031
def work1031 : RoundedTauEval :=
  evalTau precision tau1031 contact1031 logTwoBall

theorem center_sq1031 : (center1031.re : ℝ)^2 +
    (center1031.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1031]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1031 : work1031.theta.ok = true ∧
    work1031.jac.invOK = true ∧ acceptsUnitSq work1031.out = true := by
  norm_num [work1031, contact1031, tau1031, center1031, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1031 : CellCertificate where
  tauBall := tau1031
  contactCenter := center1031
  contactBall := contact1031
  work := work1031
  center_sq := center_sq1031
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1031.1
  jac_ok := checks1031.2.1
  accepted := checks1031.2.2

def cells : List CellCertificate := [cell1024, cell1025, cell1026, cell1027, cell1028, cell1029, cell1030, cell1031]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128
