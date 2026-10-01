import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0968 : RatBall :=
  ⟨⟨-9/160, 11/32⟩, 3/320⟩
def center0968 : GaussianRat :=
  ⟨-44352537/1000000000, 61948059/250000000⟩
def contact0968 : RatBall := localContactBall tau0968 center0968
def work0968 : RoundedTauEval :=
  evalTau precision tau0968 contact0968 logTwoBall

theorem center_sq0968 : (center0968.re : ℝ)^2 +
    (center0968.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0968]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0968 : work0968.theta.ok = true ∧
    work0968.jac.invOK = true ∧ acceptsUnitSq work0968.out = true := by
  norm_num [work0968, contact0968, tau0968, center0968, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0968 : CellCertificate where
  tauBall := tau0968
  contactCenter := center0968
  contactBall := contact0968
  work := work0968
  center_sq := center_sq0968
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0968.1
  jac_ok := checks0968.2.1
  accepted := checks0968.2.2

def tau0969 : RatBall :=
  ⟨⟨-7/160, 49/160⟩, 3/320⟩
def center0969 : GaussianRat :=
  ⟨-16780473/500000000, 219087113/1000000000⟩
def contact0969 : RatBall := localContactBall tau0969 center0969
def work0969 : RoundedTauEval :=
  evalTau precision tau0969 contact0969 logTwoBall

theorem center_sq0969 : (center0969.re : ℝ)^2 +
    (center0969.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0969]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0969 : work0969.theta.ok = true ∧
    work0969.jac.invOK = true ∧ acceptsUnitSq work0969.out = true := by
  norm_num [work0969, contact0969, tau0969, center0969, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0969 : CellCertificate where
  tauBall := tau0969
  contactCenter := center0969
  contactBall := contact0969
  work := work0969
  center_sq := center_sq0969
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0969.1
  jac_ok := checks0969.2.1
  accepted := checks0969.2.2

def tau0970 : RatBall :=
  ⟨⟨-1/32, 49/160⟩, 3/320⟩
def center0970 : GaussianRat :=
  ⟨-2398433/100000000, 219339251/1000000000⟩
def contact0970 : RatBall := localContactBall tau0970 center0970
def work0970 : RoundedTauEval :=
  evalTau precision tau0970 contact0970 logTwoBall

theorem center_sq0970 : (center0970.re : ℝ)^2 +
    (center0970.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0970]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0970 : work0970.theta.ok = true ∧
    work0970.jac.invOK = true ∧ acceptsUnitSq work0970.out = true := by
  norm_num [work0970, contact0970, tau0970, center0970, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0970 : CellCertificate where
  tauBall := tau0970
  contactCenter := center0970
  contactBall := contact0970
  work := work0970
  center_sq := center_sq0970
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0970.1
  jac_ok := checks0970.2.1
  accepted := checks0970.2.2

def tau0971 : RatBall :=
  ⟨⟨-7/160, 51/160⟩, 3/320⟩
def center0971 : GaussianRat :=
  ⟨-1693169/50000000, 228698347/1000000000⟩
def contact0971 : RatBall := localContactBall tau0971 center0971
def work0971 : RoundedTauEval :=
  evalTau precision tau0971 contact0971 logTwoBall

theorem center_sq0971 : (center0971.re : ℝ)^2 +
    (center0971.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0971]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0971 : work0971.theta.ok = true ∧
    work0971.jac.invOK = true ∧ acceptsUnitSq work0971.out = true := by
  norm_num [work0971, contact0971, tau0971, center0971, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0971 : CellCertificate where
  tauBall := tau0971
  contactCenter := center0971
  contactBall := contact0971
  work := work0971
  center_sq := center_sq0971
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0971.1
  jac_ok := checks0971.2.1
  accepted := checks0971.2.2

def tau0972 : RatBall :=
  ⟨⟨-1/32, 51/160⟩, 3/320⟩
def center0972 : GaussianRat :=
  ⟨-24200917/1000000000, 228965453/1000000000⟩
def contact0972 : RatBall := localContactBall tau0972 center0972
def work0972 : RoundedTauEval :=
  evalTau precision tau0972 contact0972 logTwoBall

theorem center_sq0972 : (center0972.re : ℝ)^2 +
    (center0972.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0972]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0972 : work0972.theta.ok = true ∧
    work0972.jac.invOK = true ∧ acceptsUnitSq work0972.out = true := by
  norm_num [work0972, contact0972, tau0972, center0972, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0972 : CellCertificate where
  tauBall := tau0972
  contactCenter := center0972
  contactBall := contact0972
  work := work0972
  center_sq := center_sq0972
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0972.1
  jac_ok := checks0972.2.1
  accepted := checks0972.2.2

def tau0973 : RatBall :=
  ⟨⟨-3/160, 49/160⟩, 3/320⟩
def center0973 : GaussianRat :=
  ⟨-14395497/1000000000, 27438463/125000000⟩
def contact0973 : RatBall := localContactBall tau0973 center0973
def work0973 : RoundedTauEval :=
  evalTau precision tau0973 contact0973 logTwoBall

theorem center_sq0973 : (center0973.re : ℝ)^2 +
    (center0973.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0973]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0973 : work0973.theta.ok = true ∧
    work0973.jac.invOK = true ∧ acceptsUnitSq work0973.out = true := by
  norm_num [work0973, contact0973, tau0973, center0973, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0973 : CellCertificate where
  tauBall := tau0973
  contactCenter := center0973
  contactBall := contact0973
  work := work0973
  center_sq := center_sq0973
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0973.1
  jac_ok := checks0973.2.1
  accepted := checks0973.2.2

def tau0974 : RatBall :=
  ⟨⟨-1/160, 49/160⟩, 3/320⟩
def center0974 : GaussianRat :=
  ⟨-1199829/250000000, 109796019/500000000⟩
def contact0974 : RatBall := localContactBall tau0974 center0974
def work0974 : RoundedTauEval :=
  evalTau precision tau0974 contact0974 logTwoBall

theorem center_sq0974 : (center0974.re : ℝ)^2 +
    (center0974.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0974]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0974 : work0974.theta.ok = true ∧
    work0974.jac.invOK = true ∧ acceptsUnitSq work0974.out = true := by
  norm_num [work0974, contact0974, tau0974, center0974, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0974 : CellCertificate where
  tauBall := tau0974
  contactCenter := center0974
  contactBall := contact0974
  work := work0974
  center_sq := center_sq0974
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0974.1
  jac_ok := checks0974.2.1
  accepted := checks0974.2.2

def tau0975 : RatBall :=
  ⟨⟨-3/160, 51/160⟩, 3/320⟩
def center0975 : GaussianRat :=
  ⟨-581027/40000000, 57285979/250000000⟩
def contact0975 : RatBall := localContactBall tau0975 center0975
def work0975 : RoundedTauEval :=
  evalTau precision tau0975 contact0975 logTwoBall

theorem center_sq0975 : (center0975.re : ℝ)^2 +
    (center0975.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0975]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0975 : work0975.theta.ok = true ∧
    work0975.jac.invOK = true ∧ acceptsUnitSq work0975.out = true := by
  norm_num [work0975, contact0975, tau0975, center0975, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0975 : CellCertificate where
  tauBall := tau0975
  contactCenter := center0975
  contactBall := contact0975
  work := work0975
  center_sq := center_sq0975
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0975.1
  jac_ok := checks0975.2.1
  accepted := checks0975.2.2

def cells : List CellCertificate := [cell0968, cell0969, cell0970, cell0971, cell0972, cell0973, cell0974, cell0975]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121
