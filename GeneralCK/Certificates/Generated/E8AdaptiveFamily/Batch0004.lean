import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0032 : RatBall :=
  ⟨⟨-1/40, 1/40⟩, 3/80⟩
def center0032 : GaussianRat :=
  ⟨-17336181/1000000000, 17321167/1000000000⟩
def contact0032 : RatBall := localContactBall tau0032 center0032
def work0032 : RoundedTauEval :=
  evalTau precision tau0032 contact0032 logTwoBall

theorem center_sq0032 : (center0032.re : ℝ)^2 +
    (center0032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0032 : work0032.theta.ok = true ∧
    work0032.jac.invOK = true ∧ acceptsUnitSq work0032.out = true := by
  norm_num [work0032, contact0032, tau0032, center0032, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0032 : CellCertificate where
  tauBall := tau0032
  contactCenter := center0032
  contactBall := contact0032
  work := work0032
  center_sq := center_sq0032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0032.1
  jac_ok := checks0032.2.1
  accepted := checks0032.2.2

def tau0033 : RatBall :=
  ⟨⟨-3/40, 3/40⟩, 3/80⟩
def center0033 : GaussianRat :=
  ⟨-1304683/25000000, 51781961/1000000000⟩
def contact0033 : RatBall := localContactBall tau0033 center0033
def work0033 : RoundedTauEval :=
  evalTau precision tau0033 contact0033 logTwoBall

theorem center_sq0033 : (center0033.re : ℝ)^2 +
    (center0033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0033 : work0033.theta.ok = true ∧
    work0033.jac.invOK = true ∧ acceptsUnitSq work0033.out = true := by
  norm_num [work0033, contact0033, tau0033, center0033, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0033 : CellCertificate where
  tauBall := tau0033
  contactCenter := center0033
  contactBall := contact0033
  work := work0033
  center_sq := center_sq0033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0033.1
  jac_ok := checks0033.2.1
  accepted := checks0033.2.2

def tau0034 : RatBall :=
  ⟨⟨-1/40, 3/40⟩, 3/80⟩
def center0034 : GaussianRat :=
  ⟨-2178341/125000000, 3253349/62500000⟩
def contact0034 : RatBall := localContactBall tau0034 center0034
def work0034 : RoundedTauEval :=
  evalTau precision tau0034 contact0034 logTwoBall

theorem center_sq0034 : (center0034.re : ℝ)^2 +
    (center0034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0034 : work0034.theta.ok = true ∧
    work0034.jac.invOK = true ∧ acceptsUnitSq work0034.out = true := by
  norm_num [work0034, contact0034, tau0034, center0034, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0034 : CellCertificate where
  tauBall := tau0034
  contactCenter := center0034
  contactBall := contact0034
  work := work0034
  center_sq := center_sq0034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0034.1
  jac_ok := checks0034.2.1
  accepted := checks0034.2.2

def tau0035 : RatBall :=
  ⟨⟨-1/8, 1/8⟩, 3/80⟩
def center0035 : GaussianRat :=
  ⟨-87563403/1000000000, 85687457/1000000000⟩
def contact0035 : RatBall := localContactBall tau0035 center0035
def work0035 : RoundedTauEval :=
  evalTau precision tau0035 contact0035 logTwoBall

theorem center_sq0035 : (center0035.re : ℝ)^2 +
    (center0035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0035 : work0035.theta.ok = true ∧
    work0035.jac.invOK = true ∧ acceptsUnitSq work0035.out = true := by
  norm_num [work0035, contact0035, tau0035, center0035, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0035 : CellCertificate where
  tauBall := tau0035
  contactCenter := center0035
  contactBall := contact0035
  work := work0035
  center_sq := center_sq0035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0035.1
  jac_ok := checks0035.2.1
  accepted := checks0035.2.2

def tau0036 : RatBall :=
  ⟨⟨-3/40, 1/8⟩, 3/80⟩
def center0036 : GaussianRat :=
  ⟨-52733271/1000000000, 10824621/125000000⟩
def contact0036 : RatBall := localContactBall tau0036 center0036
def work0036 : RoundedTauEval :=
  evalTau precision tau0036 contact0036 logTwoBall

theorem center_sq0036 : (center0036.re : ℝ)^2 +
    (center0036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0036 : work0036.theta.ok = true ∧
    work0036.jac.invOK = true ∧ acceptsUnitSq work0036.out = true := by
  norm_num [work0036, contact0036, tau0036, center0036, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0036 : CellCertificate where
  tauBall := tau0036
  contactCenter := center0036
  contactBall := contact0036
  work := work0036
  center_sq := center_sq0036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0036.1
  jac_ok := checks0036.2.1
  accepted := checks0036.2.2

def tau0037 : RatBall :=
  ⟨⟨-1/40, 1/8⟩, 3/80⟩
def center0037 : GaussianRat :=
  ⟨-17610637/1000000000, 8705903/100000000⟩
def contact0037 : RatBall := localContactBall tau0037 center0037
def work0037 : RoundedTauEval :=
  evalTau precision tau0037 contact0037 logTwoBall

theorem center_sq0037 : (center0037.re : ℝ)^2 +
    (center0037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0037 : work0037.theta.ok = true ∧
    work0037.jac.invOK = true ∧ acceptsUnitSq work0037.out = true := by
  norm_num [work0037, contact0037, tau0037, center0037, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0037 : CellCertificate where
  tauBall := tau0037
  contactCenter := center0037
  contactBall := contact0037
  work := work0037
  center_sq := center_sq0037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0037.1
  jac_ok := checks0037.2.1
  accepted := checks0037.2.2

def tau0038 : RatBall :=
  ⟨⟨-1/40, 7/40⟩, 3/80⟩
def center0038 : GaussianRat :=
  ⟨-17893761/1000000000, 7658063/62500000⟩
def contact0038 : RatBall := localContactBall tau0038 center0038
def work0038 : RoundedTauEval :=
  evalTau precision tau0038 contact0038 logTwoBall

theorem center_sq0038 : (center0038.re : ℝ)^2 +
    (center0038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0038 : work0038.theta.ok = true ∧
    work0038.jac.invOK = true ∧ acceptsUnitSq work0038.out = true := by
  norm_num [work0038, contact0038, tau0038, center0038, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0038 : CellCertificate where
  tauBall := tau0038
  contactCenter := center0038
  contactBall := contact0038
  work := work0038
  center_sq := center_sq0038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0038.1
  jac_ok := checks0038.2.1
  accepted := checks0038.2.2

def tau0039 : RatBall :=
  ⟨⟨1/40, 1/40⟩, 3/80⟩
def center0039 : GaussianRat :=
  ⟨17336181/1000000000, 17321167/1000000000⟩
def contact0039 : RatBall := localContactBall tau0039 center0039
def work0039 : RoundedTauEval :=
  evalTau precision tau0039 contact0039 logTwoBall

theorem center_sq0039 : (center0039.re : ℝ)^2 +
    (center0039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0039 : work0039.theta.ok = true ∧
    work0039.jac.invOK = true ∧ acceptsUnitSq work0039.out = true := by
  norm_num [work0039, contact0039, tau0039, center0039, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0039 : CellCertificate where
  tauBall := tau0039
  contactCenter := center0039
  contactBall := contact0039
  work := work0039
  center_sq := center_sq0039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0039.1
  jac_ok := checks0039.2.1
  accepted := checks0039.2.2

def cells : List CellCertificate := [cell0032, cell0033, cell0034, cell0035, cell0036, cell0037, cell0038, cell0039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004
