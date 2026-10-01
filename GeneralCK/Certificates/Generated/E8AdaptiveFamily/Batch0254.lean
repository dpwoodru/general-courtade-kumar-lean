import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2032 : RatBall :=
  ⟨⟨-57/320, 97/320⟩, 3/640⟩
def center2032 : GaussianRat :=
  ⟨-67113521/500000000, 52277787/250000000⟩
def contact2032 : RatBall := localContactBall tau2032 center2032
def work2032 : RoundedTauEval :=
  evalTau precision tau2032 contact2032 logTwoBall

theorem center_sq2032 : (center2032.re : ℝ)^2 +
    (center2032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2032 : work2032.theta.ok = true ∧
    work2032.jac.invOK = true ∧ acceptsUnitSq work2032.out = true := by
  norm_num [work2032, contact2032, tau2032, center2032, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2032 : CellCertificate where
  tauBall := tau2032
  contactCenter := center2032
  contactBall := contact2032
  work := work2032
  center_sq := center_sq2032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2032.1
  jac_ok := checks2032.2.1
  accepted := checks2032.2.2

def tau2033 : RatBall :=
  ⟨⟨-59/320, 99/320⟩, 3/640⟩
def center2033 : GaussianRat :=
  ⟨-34836127/250000000, 53276923/250000000⟩
def contact2033 : RatBall := localContactBall tau2033 center2033
def work2033 : RoundedTauEval :=
  evalTau precision tau2033 contact2033 logTwoBall

theorem center_sq2033 : (center2033.re : ℝ)^2 +
    (center2033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2033 : work2033.theta.ok = true ∧
    work2033.jac.invOK = true ∧ acceptsUnitSq work2033.out = true := by
  norm_num [work2033, contact2033, tau2033, center2033, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2033 : CellCertificate where
  tauBall := tau2033
  contactCenter := center2033
  contactBall := contact2033
  work := work2033
  center_sq := center_sq2033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2033.1
  jac_ok := checks2033.2.1
  accepted := checks2033.2.2

def tau2034 : RatBall :=
  ⟨⟨-57/320, 99/320⟩, 3/640⟩
def center2034 : GaussianRat :=
  ⟨-5391177/40000000, 106838001/500000000⟩
def contact2034 : RatBall := localContactBall tau2034 center2034
def work2034 : RoundedTauEval :=
  evalTau precision tau2034 contact2034 logTwoBall

theorem center_sq2034 : (center2034.re : ℝ)^2 +
    (center2034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2034 : work2034.theta.ok = true ∧
    work2034.jac.invOK = true ∧ acceptsUnitSq work2034.out = true := by
  norm_num [work2034, contact2034, tau2034, center2034, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2034 : CellCertificate where
  tauBall := tau2034
  contactCenter := center2034
  contactBall := contact2034
  work := work2034
  center_sq := center_sq2034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2034.1
  jac_ok := checks2034.2.1
  accepted := checks2034.2.2

def tau2035 : RatBall :=
  ⟨⟨-63/320, 101/320⟩, 3/640⟩
def center2035 : GaussianRat :=
  ⟨-74521233/500000000, 108227539/500000000⟩
def contact2035 : RatBall := localContactBall tau2035 center2035
def work2035 : RoundedTauEval :=
  evalTau precision tau2035 contact2035 logTwoBall

theorem center_sq2035 : (center2035.re : ℝ)^2 +
    (center2035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2035 : work2035.theta.ok = true ∧
    work2035.jac.invOK = true ∧ acceptsUnitSq work2035.out = true := by
  norm_num [work2035, contact2035, tau2035, center2035, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2035 : CellCertificate where
  tauBall := tau2035
  contactCenter := center2035
  contactBall := contact2035
  work := work2035
  center_sq := center_sq2035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2035.1
  jac_ok := checks2035.2.1
  accepted := checks2035.2.2

def tau2036 : RatBall :=
  ⟨⟨-61/320, 101/320⟩, 3/640⟩
def center2036 : GaussianRat :=
  ⟨-7224707/50000000, 217072079/1000000000⟩
def contact2036 : RatBall := localContactBall tau2036 center2036
def work2036 : RoundedTauEval :=
  evalTau precision tau2036 contact2036 logTwoBall

theorem center_sq2036 : (center2036.re : ℝ)^2 +
    (center2036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2036 : work2036.theta.ok = true ∧
    work2036.jac.invOK = true ∧ acceptsUnitSq work2036.out = true := by
  norm_num [work2036, contact2036, tau2036, center2036, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2036 : CellCertificate where
  tauBall := tau2036
  contactCenter := center2036
  contactBall := contact2036
  work := work2036
  center_sq := center_sq2036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2036.1
  jac_ok := checks2036.2.1
  accepted := checks2036.2.2

def tau2037 : RatBall :=
  ⟨⟨-63/320, 103/320⟩, 3/640⟩
def center2037 : GaussianRat :=
  ⟨-74838049/500000000, 221002847/1000000000⟩
def contact2037 : RatBall := localContactBall tau2037 center2037
def work2037 : RoundedTauEval :=
  evalTau precision tau2037 contact2037 logTwoBall

theorem center_sq2037 : (center2037.re : ℝ)^2 +
    (center2037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2037 : work2037.theta.ok = true ∧
    work2037.jac.invOK = true ∧ acceptsUnitSq work2037.out = true := by
  norm_num [work2037, contact2037, tau2037, center2037, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2037 : CellCertificate where
  tauBall := tau2037
  contactCenter := center2037
  contactBall := contact2037
  work := work2037
  center_sq := center_sq2037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2037.1
  jac_ok := checks2037.2.1
  accepted := checks2037.2.2

def tau2038 : RatBall :=
  ⟨⟨-61/320, 103/320⟩, 3/640⟩
def center2038 : GaussianRat :=
  ⟨-5804463/40000000, 221637027/1000000000⟩
def contact2038 : RatBall := localContactBall tau2038 center2038
def work2038 : RoundedTauEval :=
  evalTau precision tau2038 contact2038 logTwoBall

theorem center_sq2038 : (center2038.re : ℝ)^2 +
    (center2038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2038 : work2038.theta.ok = true ∧
    work2038.jac.invOK = true ∧ acceptsUnitSq work2038.out = true := by
  norm_num [work2038, contact2038, tau2038, center2038, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2038 : CellCertificate where
  tauBall := tau2038
  contactCenter := center2038
  contactBall := contact2038
  work := work2038
  center_sq := center_sq2038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2038.1
  jac_ok := checks2038.2.1
  accepted := checks2038.2.2

def tau2039 : RatBall :=
  ⟨⟨-59/320, 101/320⟩, 3/640⟩
def center2039 : GaussianRat :=
  ⟨-27985801/200000000, 54418229/250000000⟩
def contact2039 : RatBall := localContactBall tau2039 center2039
def work2039 : RoundedTauEval :=
  evalTau precision tau2039 contact2039 logTwoBall

theorem center_sq2039 : (center2039.re : ℝ)^2 +
    (center2039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2039 : work2039.theta.ok = true ∧
    work2039.jac.invOK = true ∧ acceptsUnitSq work2039.out = true := by
  norm_num [work2039, contact2039, tau2039, center2039, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2039 : CellCertificate where
  tauBall := tau2039
  contactCenter := center2039
  contactBall := contact2039
  work := work2039
  center_sq := center_sq2039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2039.1
  jac_ok := checks2039.2.1
  accepted := checks2039.2.2

def cells : List CellCertificate := [cell2032, cell2033, cell2034, cell2035, cell2036, cell2037, cell2038, cell2039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254
