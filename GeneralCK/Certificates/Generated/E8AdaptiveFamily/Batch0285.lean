import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0285

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2280 : RatBall :=
  ⟨⟨19/320, 23/64⟩, 3/640⟩
def center2280 : GaussianRat :=
  ⟨47415929/1000000000, 260020027/1000000000⟩
def contact2280 : RatBall := localContactBall tau2280 center2280
def work2280 : RoundedTauEval :=
  evalTau precision tau2280 contact2280 logTwoBall

theorem center_sq2280 : (center2280.re : ℝ)^2 +
    (center2280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2280 : work2280.theta.ok = true ∧
    work2280.jac.invOK = true ∧ acceptsUnitSq work2280.out = true := by
  norm_num [work2280, contact2280, tau2280, center2280, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2280 : CellCertificate where
  tauBall := tau2280
  contactCenter := center2280
  contactBall := contact2280
  work := work2280
  center_sq := center_sq2280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2280.1
  jac_ok := checks2280.2.1
  accepted := checks2280.2.2

def tau2281 : RatBall :=
  ⟨⟨21/320, 113/320⟩, 3/640⟩
def center2281 : GaussianRat :=
  ⟨13026633/250000000, 254806033/1000000000⟩
def contact2281 : RatBall := localContactBall tau2281 center2281
def work2281 : RoundedTauEval :=
  evalTau precision tau2281 contact2281 logTwoBall

theorem center_sq2281 : (center2281.re : ℝ)^2 +
    (center2281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2281 : work2281.theta.ok = true ∧
    work2281.jac.invOK = true ∧ acceptsUnitSq work2281.out = true := by
  norm_num [work2281, contact2281, tau2281, center2281, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2281 : CellCertificate where
  tauBall := tau2281
  contactCenter := center2281
  contactBall := contact2281
  work := work2281
  center_sq := center_sq2281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2281.1
  jac_ok := checks2281.2.1
  accepted := checks2281.2.2

def tau2282 : RatBall :=
  ⟨⟨23/320, 113/320⟩, 3/640⟩
def center2282 : GaussianRat :=
  ⟨57038551/1000000000, 63630699/250000000⟩
def contact2282 : RatBall := localContactBall tau2282 center2282
def work2282 : RoundedTauEval :=
  evalTau precision tau2282 contact2282 logTwoBall

theorem center_sq2282 : (center2282.re : ℝ)^2 +
    (center2282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2282 : work2282.theta.ok = true ∧
    work2282.jac.invOK = true ∧ acceptsUnitSq work2282.out = true := by
  norm_num [work2282, contact2282, tau2282, center2282, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2282 : CellCertificate where
  tauBall := tau2282
  contactCenter := center2282
  contactBall := contact2282
  work := work2282
  center_sq := center_sq2282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2282.1
  jac_ok := checks2282.2.1
  accepted := checks2282.2.2

def tau2283 : RatBall :=
  ⟨⟨21/320, 23/64⟩, 3/640⟩
def center2283 : GaussianRat :=
  ⟨6547631/125000000, 64938653/250000000⟩
def contact2283 : RatBall := localContactBall tau2283 center2283
def work2283 : RoundedTauEval :=
  evalTau precision tau2283 contact2283 logTwoBall

theorem center_sq2283 : (center2283.re : ℝ)^2 +
    (center2283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2283 : work2283.theta.ok = true ∧
    work2283.jac.invOK = true ∧ acceptsUnitSq work2283.out = true := by
  norm_num [work2283, contact2283, tau2283, center2283, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2283 : CellCertificate where
  tauBall := tau2283
  contactCenter := center2283
  contactBall := contact2283
  work := work2283
  center_sq := center_sq2283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2283.1
  jac_ok := checks2283.2.1
  accepted := checks2283.2.2

def tau2284 : RatBall :=
  ⟨⟨23/320, 23/64⟩, 3/640⟩
def center2284 : GaussianRat :=
  ⟨5733843/100000000, 129731693/500000000⟩
def contact2284 : RatBall := localContactBall tau2284 center2284
def work2284 : RoundedTauEval :=
  evalTau precision tau2284 contact2284 logTwoBall

theorem center_sq2284 : (center2284.re : ℝ)^2 +
    (center2284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2284]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2284 : work2284.theta.ok = true ∧
    work2284.jac.invOK = true ∧ acceptsUnitSq work2284.out = true := by
  norm_num [work2284, contact2284, tau2284, center2284, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2284 : CellCertificate where
  tauBall := tau2284
  contactCenter := center2284
  contactBall := contact2284
  work := work2284
  center_sq := center_sq2284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2284.1
  jac_ok := checks2284.2.1
  accepted := checks2284.2.2

def tau2285 : RatBall :=
  ⟨⟨17/320, 117/320⟩, 3/640⟩
def center2285 : GaussianRat :=
  ⟨10668331/250000000, 265248069/1000000000⟩
def contact2285 : RatBall := localContactBall tau2285 center2285
def work2285 : RoundedTauEval :=
  evalTau precision tau2285 contact2285 logTwoBall

theorem center_sq2285 : (center2285.re : ℝ)^2 +
    (center2285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2285 : work2285.theta.ok = true ∧
    work2285.jac.invOK = true ∧ acceptsUnitSq work2285.out = true := by
  norm_num [work2285, contact2285, tau2285, center2285, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2285 : CellCertificate where
  tauBall := tau2285
  contactCenter := center2285
  contactBall := contact2285
  work := work2285
  center_sq := center_sq2285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2285.1
  jac_ok := checks2285.2.1
  accepted := checks2285.2.2

def tau2286 : RatBall :=
  ⟨⟨19/320, 117/320⟩, 3/640⟩
def center2286 : GaussianRat :=
  ⟨23835959/500000000, 265001899/1000000000⟩
def contact2286 : RatBall := localContactBall tau2286 center2286
def work2286 : RoundedTauEval :=
  evalTau precision tau2286 contact2286 logTwoBall

theorem center_sq2286 : (center2286.re : ℝ)^2 +
    (center2286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2286 : work2286.theta.ok = true ∧
    work2286.jac.invOK = true ∧ acceptsUnitSq work2286.out = true := by
  norm_num [work2286, contact2286, tau2286, center2286, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2286 : CellCertificate where
  tauBall := tau2286
  contactCenter := center2286
  contactBall := contact2286
  work := work2286
  center_sq := center_sq2286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2286.1
  jac_ok := checks2286.2.1
  accepted := checks2286.2.2

def tau2287 : RatBall :=
  ⟨⟨17/320, 119/320⟩, 3/640⟩
def center2287 : GaussianRat :=
  ⟨42909337/1000000000, 135131799/500000000⟩
def contact2287 : RatBall := localContactBall tau2287 center2287
def work2287 : RoundedTauEval :=
  evalTau precision tau2287 contact2287 logTwoBall

theorem center_sq2287 : (center2287.re : ℝ)^2 +
    (center2287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2287]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2287 : work2287.theta.ok = true ∧
    work2287.jac.invOK = true ∧ acceptsUnitSq work2287.out = true := by
  norm_num [work2287, contact2287, tau2287, center2287, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2287 : CellCertificate where
  tauBall := tau2287
  contactCenter := center2287
  contactBall := contact2287
  work := work2287
  center_sq := center_sq2287
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2287.1
  jac_ok := checks2287.2.1
  accepted := checks2287.2.2

def cells : List CellCertificate := [cell2280, cell2281, cell2282, cell2283, cell2284, cell2285, cell2286, cell2287]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0285
