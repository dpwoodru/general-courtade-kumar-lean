import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0280 : RatBall :=
  ⟨⟨11/80, 13/80⟩, 3/160⟩
def center0280 : GaussianRat :=
  ⟨48637291/500000000, 111393603/1000000000⟩
def contact0280 : RatBall := localContactBall tau0280 center0280
def work0280 : RoundedTauEval :=
  evalTau precision tau0280 contact0280 logTwoBall

theorem center_sq0280 : (center0280.re : ℝ)^2 +
    (center0280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0280 : work0280.theta.ok = true ∧
    work0280.jac.invOK = true ∧ acceptsUnitSq work0280.out = true := by
  norm_num [work0280, contact0280, tau0280, center0280, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0280 : CellCertificate where
  tauBall := tau0280
  contactCenter := center0280
  contactBall := contact0280
  work := work0280
  center_sq := center_sq0280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0280.1
  jac_ok := checks0280.2.1
  accepted := checks0280.2.2

def tau0281 : RatBall :=
  ⟨⟨9/80, 3/16⟩, 3/160⟩
def center0281 : GaussianRat :=
  ⟨80517041/1000000000, 8110609/62500000⟩
def contact0281 : RatBall := localContactBall tau0281 center0281
def work0281 : RoundedTauEval :=
  evalTau precision tau0281 contact0281 logTwoBall

theorem center_sq0281 : (center0281.re : ℝ)^2 +
    (center0281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0281 : work0281.theta.ok = true ∧
    work0281.jac.invOK = true ∧ acceptsUnitSq work0281.out = true := by
  norm_num [work0281, contact0281, tau0281, center0281, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0281 : CellCertificate where
  tauBall := tau0281
  contactCenter := center0281
  contactBall := contact0281
  work := work0281
  center_sq := center_sq0281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0281.1
  jac_ok := checks0281.2.1
  accepted := checks0281.2.2

def tau0282 : RatBall :=
  ⟨⟨11/80, 3/16⟩, 3/160⟩
def center0282 : GaussianRat :=
  ⟨1227011/12500000, 8055803/62500000⟩
def contact0282 : RatBall := localContactBall tau0282 center0282
def work0282 : RoundedTauEval :=
  evalTau precision tau0282 contact0282 logTwoBall

theorem center_sq0282 : (center0282.re : ℝ)^2 +
    (center0282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0282 : work0282.theta.ok = true ∧
    work0282.jac.invOK = true ∧ acceptsUnitSq work0282.out = true := by
  norm_num [work0282, contact0282, tau0282, center0282, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0282 : CellCertificate where
  tauBall := tau0282
  contactCenter := center0282
  contactBall := contact0282
  work := work0282
  center_sq := center_sq0282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0282.1
  jac_ok := checks0282.2.1
  accepted := checks0282.2.2

def tau0283 : RatBall :=
  ⟨⟨13/80, 13/80⟩, 3/160⟩
def center0283 : GaussianRat :=
  ⟨114628827/1000000000, 110510723/1000000000⟩
def contact0283 : RatBall := localContactBall tau0283 center0283
def work0283 : RoundedTauEval :=
  evalTau precision tau0283 contact0283 logTwoBall

theorem center_sq0283 : (center0283.re : ℝ)^2 +
    (center0283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0283 : work0283.theta.ok = true ∧
    work0283.jac.invOK = true ∧ acceptsUnitSq work0283.out = true := by
  norm_num [work0283, contact0283, tau0283, center0283, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0283 : CellCertificate where
  tauBall := tau0283
  contactCenter := center0283
  contactBall := contact0283
  work := work0283
  center_sq := center_sq0283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0283.1
  jac_ok := checks0283.2.1
  accepted := checks0283.2.2

def tau0284 : RatBall :=
  ⟨⟨3/16, 13/80⟩, 3/160⟩
def center0284 : GaussianRat :=
  ⟨131822371/1000000000, 13687313/125000000⟩
def contact0284 : RatBall := localContactBall tau0284 center0284
def work0284 : RoundedTauEval :=
  evalTau precision tau0284 contact0284 logTwoBall

theorem center_sq0284 : (center0284.re : ℝ)^2 +
    (center0284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0284]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0284 : work0284.theta.ok = true ∧
    work0284.jac.invOK = true ∧ acceptsUnitSq work0284.out = true := by
  norm_num [work0284, contact0284, tau0284, center0284, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0284 : CellCertificate where
  tauBall := tau0284
  contactCenter := center0284
  contactBall := contact0284
  work := work0284
  center_sq := center_sq0284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0284.1
  jac_ok := checks0284.2.1
  accepted := checks0284.2.2

def tau0285 : RatBall :=
  ⟨⟨13/80, 3/16⟩, 3/160⟩
def center0285 : GaussianRat :=
  ⟨115659239/1000000000, 127856533/1000000000⟩
def contact0285 : RatBall := localContactBall tau0285 center0285
def work0285 : RoundedTauEval :=
  evalTau precision tau0285 contact0285 logTwoBall

theorem center_sq0285 : (center0285.re : ℝ)^2 +
    (center0285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0285 : work0285.theta.ok = true ∧
    work0285.jac.invOK = true ∧ acceptsUnitSq work0285.out = true := by
  norm_num [work0285, contact0285, tau0285, center0285, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0285 : CellCertificate where
  tauBall := tau0285
  contactCenter := center0285
  contactBall := contact0285
  work := work0285
  center_sq := center_sq0285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0285.1
  jac_ok := checks0285.2.1
  accepted := checks0285.2.2

def tau0286 : RatBall :=
  ⟨⟨3/16, 3/16⟩, 3/160⟩
def center0286 : GaussianRat :=
  ⟨132989007/1000000000, 15833617/125000000⟩
def contact0286 : RatBall := localContactBall tau0286 center0286
def work0286 : RoundedTauEval :=
  evalTau precision tau0286 contact0286 logTwoBall

theorem center_sq0286 : (center0286.re : ℝ)^2 +
    (center0286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0286 : work0286.theta.ok = true ∧
    work0286.jac.invOK = true ∧ acceptsUnitSq work0286.out = true := by
  norm_num [work0286, contact0286, tau0286, center0286, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0286 : CellCertificate where
  tauBall := tau0286
  contactCenter := center0286
  contactBall := contact0286
  work := work0286
  center_sq := center_sq0286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0286.1
  jac_ok := checks0286.2.1
  accepted := checks0286.2.2

def tau0287 : RatBall :=
  ⟨⟨21/80, 1/80⟩, 3/160⟩
def center0287 : GaussianRat :=
  ⟨4445163/25000000, 8084719/1000000000⟩
def contact0287 : RatBall := localContactBall tau0287 center0287
def work0287 : RoundedTauEval :=
  evalTau precision tau0287 contact0287 logTwoBall

theorem center_sq0287 : (center0287.re : ℝ)^2 +
    (center0287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0287]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0287 : work0287.theta.ok = true ∧
    work0287.jac.invOK = true ∧ acceptsUnitSq work0287.out = true := by
  norm_num [work0287, contact0287, tau0287, center0287, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0287 : CellCertificate where
  tauBall := tau0287
  contactCenter := center0287
  contactBall := contact0287
  work := work0287
  center_sq := center_sq0287
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0287.1
  jac_ok := checks0287.2.1
  accepted := checks0287.2.2

def cells : List CellCertificate := [cell0280, cell0281, cell0282, cell0283, cell0284, cell0285, cell0286, cell0287]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035
