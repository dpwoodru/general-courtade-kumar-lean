import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0272 : RatBall :=
  ⟨⟨7/80, 13/80⟩, 3/160⟩
def center0272 : GaussianRat :=
  ⟨31086987/500000000, 112745169/1000000000⟩
def contact0272 : RatBall := localContactBall tau0272 center0272
def work0272 : RoundedTauEval :=
  evalTau precision tau0272 contact0272 logTwoBall

theorem center_sq0272 : (center0272.re : ℝ)^2 +
    (center0272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0272 : work0272.theta.ok = true ∧
    work0272.jac.invOK = true ∧ acceptsUnitSq work0272.out = true := by
  norm_num [work0272, contact0272, tau0272, center0272, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0272 : CellCertificate where
  tauBall := tau0272
  contactCenter := center0272
  contactBall := contact0272
  work := work0272
  center_sq := center_sq0272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0272.1
  jac_ok := checks0272.2.1
  accepted := checks0272.2.2

def tau0273 : RatBall :=
  ⟨⟨1/16, 3/16⟩, 3/160⟩
def center0273 : GaussianRat :=
  ⟨22445977/500000000, 131018253/1000000000⟩
def contact0273 : RatBall := localContactBall tau0273 center0273
def work0273 : RoundedTauEval :=
  evalTau precision tau0273 contact0273 logTwoBall

theorem center_sq0273 : (center0273.re : ℝ)^2 +
    (center0273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0273 : work0273.theta.ok = true ∧
    work0273.jac.invOK = true ∧ acceptsUnitSq work0273.out = true := by
  norm_num [work0273, contact0273, tau0273, center0273, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0273 : CellCertificate where
  tauBall := tau0273
  contactCenter := center0273
  contactBall := contact0273
  work := work0273
  center_sq := center_sq0273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0273.1
  jac_ok := checks0273.2.1
  accepted := checks0273.2.2

def tau0274 : RatBall :=
  ⟨⟨7/80, 3/16⟩, 3/160⟩
def center0274 : GaussianRat :=
  ⟨6275219/100000000, 65240079/500000000⟩
def contact0274 : RatBall := localContactBall tau0274 center0274
def work0274 : RoundedTauEval :=
  evalTau precision tau0274 contact0274 logTwoBall

theorem center_sq0274 : (center0274.re : ℝ)^2 +
    (center0274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0274 : work0274.theta.ok = true ∧
    work0274.jac.invOK = true ∧ acceptsUnitSq work0274.out = true := by
  norm_num [work0274, contact0274, tau0274, center0274, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0274 : CellCertificate where
  tauBall := tau0274
  contactCenter := center0274
  contactBall := contact0274
  work := work0274
  center_sq := center_sq0274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0274.1
  jac_ok := checks0274.2.1
  accepted := checks0274.2.2

def tau0275 : RatBall :=
  ⟨⟨13/80, 9/80⟩, 3/160⟩
def center0275 : GaussianRat :=
  ⟨56522129/500000000, 76186323/1000000000⟩
def contact0275 : RatBall := localContactBall tau0275 center0275
def work0275 : RoundedTauEval :=
  evalTau precision tau0275 contact0275 logTwoBall

theorem center_sq0275 : (center0275.re : ℝ)^2 +
    (center0275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0275 : work0275.theta.ok = true ∧
    work0275.jac.invOK = true ∧ acceptsUnitSq work0275.out = true := by
  norm_num [work0275, contact0275, tau0275, center0275, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0275 : CellCertificate where
  tauBall := tau0275
  contactCenter := center0275
  contactBall := contact0275
  work := work0275
  center_sq := center_sq0275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0275.1
  jac_ok := checks0275.2.1
  accepted := checks0275.2.2

def tau0276 : RatBall :=
  ⟨⟨3/16, 9/80⟩, 3/160⟩
def center0276 : GaussianRat :=
  ⟨26005447/200000000, 37751763/500000000⟩
def contact0276 : RatBall := localContactBall tau0276 center0276
def work0276 : RoundedTauEval :=
  evalTau precision tau0276 contact0276 logTwoBall

theorem center_sq0276 : (center0276.re : ℝ)^2 +
    (center0276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0276 : work0276.theta.ok = true ∧
    work0276.jac.invOK = true ∧ acceptsUnitSq work0276.out = true := by
  norm_num [work0276, contact0276, tau0276, center0276, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0276 : CellCertificate where
  tauBall := tau0276
  contactCenter := center0276
  contactBall := contact0276
  work := work0276
  center_sq := center_sq0276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0276.1
  jac_ok := checks0276.2.1
  accepted := checks0276.2.2

def tau0277 : RatBall :=
  ⟨⟨13/80, 11/80⟩, 3/160⟩
def center0277 : GaussianRat :=
  ⟨22751869/200000000, 46647191/500000000⟩
def contact0277 : RatBall := localContactBall tau0277 center0277
def work0277 : RoundedTauEval :=
  evalTau precision tau0277 contact0277 logTwoBall

theorem center_sq0277 : (center0277.re : ℝ)^2 +
    (center0277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0277 : work0277.theta.ok = true ∧
    work0277.jac.invOK = true ∧ acceptsUnitSq work0277.out = true := by
  norm_num [work0277, contact0277, tau0277, center0277, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0277 : CellCertificate where
  tauBall := tau0277
  contactCenter := center0277
  contactBall := contact0277
  work := work0277
  center_sq := center_sq0277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0277.1
  jac_ok := checks0277.2.1
  accepted := checks0277.2.2

def tau0278 : RatBall :=
  ⟨⟨3/16, 11/80⟩, 3/160⟩
def center0278 : GaussianRat :=
  ⟨130837509/1000000000, 92449971/1000000000⟩
def contact0278 : RatBall := localContactBall tau0278 center0278
def work0278 : RoundedTauEval :=
  evalTau precision tau0278 contact0278 logTwoBall

theorem center_sq0278 : (center0278.re : ℝ)^2 +
    (center0278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0278 : work0278.theta.ok = true ∧
    work0278.jac.invOK = true ∧ acceptsUnitSq work0278.out = true := by
  norm_num [work0278, contact0278, tau0278, center0278, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0278 : CellCertificate where
  tauBall := tau0278
  contactCenter := center0278
  contactBall := contact0278
  work := work0278
  center_sq := center_sq0278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0278.1
  jac_ok := checks0278.2.1
  accepted := checks0278.2.2

def tau0279 : RatBall :=
  ⟨⟨9/80, 13/80⟩, 3/160⟩
def center0279 : GaussianRat :=
  ⟨79781827/1000000000, 56070187/500000000⟩
def contact0279 : RatBall := localContactBall tau0279 center0279
def work0279 : RoundedTauEval :=
  evalTau precision tau0279 contact0279 logTwoBall

theorem center_sq0279 : (center0279.re : ℝ)^2 +
    (center0279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0279 : work0279.theta.ok = true ∧
    work0279.jac.invOK = true ∧ acceptsUnitSq work0279.out = true := by
  norm_num [work0279, contact0279, tau0279, center0279, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0279 : CellCertificate where
  tauBall := tau0279
  contactCenter := center0279
  contactBall := contact0279
  work := work0279
  center_sq := center_sq0279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0279.1
  jac_ok := checks0279.2.1
  accepted := checks0279.2.2

def cells : List CellCertificate := [cell0272, cell0273, cell0274, cell0275, cell0276, cell0277, cell0278, cell0279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034
