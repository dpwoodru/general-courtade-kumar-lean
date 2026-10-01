import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0144 : RatBall :=
  ⟨⟨3/16, -17/80⟩, 3/160⟩
def center0144 : GaussianRat :=
  ⟨16793263/125000000, -143981719/1000000000⟩
def contact0144 : RatBall := localContactBall tau0144 center0144
def work0144 : RoundedTauEval :=
  evalTau precision tau0144 contact0144 logTwoBall

theorem center_sq0144 : (center0144.re : ℝ)^2 +
    (center0144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0144 : work0144.theta.ok = true ∧
    work0144.jac.invOK = true ∧ acceptsUnitSq work0144.out = true := by
  norm_num [work0144, contact0144, tau0144, center0144, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0144 : CellCertificate where
  tauBall := tau0144
  contactCenter := center0144
  contactBall := contact0144
  work := work0144
  center_sq := center_sq0144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0144.1
  jac_ok := checks0144.2.1
  accepted := checks0144.2.2

def tau0145 : RatBall :=
  ⟨⟨1/16, -3/16⟩, 3/160⟩
def center0145 : GaussianRat :=
  ⟨22445977/500000000, -131018253/1000000000⟩
def contact0145 : RatBall := localContactBall tau0145 center0145
def work0145 : RoundedTauEval :=
  evalTau precision tau0145 contact0145 logTwoBall

theorem center_sq0145 : (center0145.re : ℝ)^2 +
    (center0145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0145 : work0145.theta.ok = true ∧
    work0145.jac.invOK = true ∧ acceptsUnitSq work0145.out = true := by
  norm_num [work0145, contact0145, tau0145, center0145, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0145 : CellCertificate where
  tauBall := tau0145
  contactCenter := center0145
  contactBall := contact0145
  work := work0145
  center_sq := center_sq0145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0145.1
  jac_ok := checks0145.2.1
  accepted := checks0145.2.2

def tau0146 : RatBall :=
  ⟨⟨7/80, -3/16⟩, 3/160⟩
def center0146 : GaussianRat :=
  ⟨6275219/100000000, -65240079/500000000⟩
def contact0146 : RatBall := localContactBall tau0146 center0146
def work0146 : RoundedTauEval :=
  evalTau precision tau0146 contact0146 logTwoBall

theorem center_sq0146 : (center0146.re : ℝ)^2 +
    (center0146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0146 : work0146.theta.ok = true ∧
    work0146.jac.invOK = true ∧ acceptsUnitSq work0146.out = true := by
  norm_num [work0146, contact0146, tau0146, center0146, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0146 : CellCertificate where
  tauBall := tau0146
  contactCenter := center0146
  contactBall := contact0146
  work := work0146
  center_sq := center_sq0146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0146.1
  jac_ok := checks0146.2.1
  accepted := checks0146.2.2

def tau0147 : RatBall :=
  ⟨⟨1/16, -13/80⟩, 3/160⟩
def center0147 : GaussianRat :=
  ⟨44475471/1000000000, -14150393/125000000⟩
def contact0147 : RatBall := localContactBall tau0147 center0147
def work0147 : RoundedTauEval :=
  evalTau precision tau0147 contact0147 logTwoBall

theorem center_sq0147 : (center0147.re : ℝ)^2 +
    (center0147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0147 : work0147.theta.ok = true ∧
    work0147.jac.invOK = true ∧ acceptsUnitSq work0147.out = true := by
  norm_num [work0147, contact0147, tau0147, center0147, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0147 : CellCertificate where
  tauBall := tau0147
  contactCenter := center0147
  contactBall := contact0147
  work := work0147
  center_sq := center_sq0147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0147.1
  jac_ok := checks0147.2.1
  accepted := checks0147.2.2

def tau0148 : RatBall :=
  ⟨⟨7/80, -13/80⟩, 3/160⟩
def center0148 : GaussianRat :=
  ⟨31086987/500000000, -112745169/1000000000⟩
def contact0148 : RatBall := localContactBall tau0148 center0148
def work0148 : RoundedTauEval :=
  evalTau precision tau0148 contact0148 logTwoBall

theorem center_sq0148 : (center0148.re : ℝ)^2 +
    (center0148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0148 : work0148.theta.ok = true ∧
    work0148.jac.invOK = true ∧ acceptsUnitSq work0148.out = true := by
  norm_num [work0148, contact0148, tau0148, center0148, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0148 : CellCertificate where
  tauBall := tau0148
  contactCenter := center0148
  contactBall := contact0148
  work := work0148
  center_sq := center_sq0148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0148.1
  jac_ok := checks0148.2.1
  accepted := checks0148.2.2

def tau0149 : RatBall :=
  ⟨⟨9/80, -3/16⟩, 3/160⟩
def center0149 : GaussianRat :=
  ⟨80517041/1000000000, -8110609/62500000⟩
def contact0149 : RatBall := localContactBall tau0149 center0149
def work0149 : RoundedTauEval :=
  evalTau precision tau0149 contact0149 logTwoBall

theorem center_sq0149 : (center0149.re : ℝ)^2 +
    (center0149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0149 : work0149.theta.ok = true ∧
    work0149.jac.invOK = true ∧ acceptsUnitSq work0149.out = true := by
  norm_num [work0149, contact0149, tau0149, center0149, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0149 : CellCertificate where
  tauBall := tau0149
  contactCenter := center0149
  contactBall := contact0149
  work := work0149
  center_sq := center_sq0149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0149.1
  jac_ok := checks0149.2.1
  accepted := checks0149.2.2

def tau0150 : RatBall :=
  ⟨⟨11/80, -3/16⟩, 3/160⟩
def center0150 : GaussianRat :=
  ⟨1227011/12500000, -8055803/62500000⟩
def contact0150 : RatBall := localContactBall tau0150 center0150
def work0150 : RoundedTauEval :=
  evalTau precision tau0150 contact0150 logTwoBall

theorem center_sq0150 : (center0150.re : ℝ)^2 +
    (center0150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0150 : work0150.theta.ok = true ∧
    work0150.jac.invOK = true ∧ acceptsUnitSq work0150.out = true := by
  norm_num [work0150, contact0150, tau0150, center0150, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0150 : CellCertificate where
  tauBall := tau0150
  contactCenter := center0150
  contactBall := contact0150
  work := work0150
  center_sq := center_sq0150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0150.1
  jac_ok := checks0150.2.1
  accepted := checks0150.2.2

def tau0151 : RatBall :=
  ⟨⟨9/80, -13/80⟩, 3/160⟩
def center0151 : GaussianRat :=
  ⟨79781827/1000000000, -56070187/500000000⟩
def contact0151 : RatBall := localContactBall tau0151 center0151
def work0151 : RoundedTauEval :=
  evalTau precision tau0151 contact0151 logTwoBall

theorem center_sq0151 : (center0151.re : ℝ)^2 +
    (center0151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0151 : work0151.theta.ok = true ∧
    work0151.jac.invOK = true ∧ acceptsUnitSq work0151.out = true := by
  norm_num [work0151, contact0151, tau0151, center0151, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0151 : CellCertificate where
  tauBall := tau0151
  contactCenter := center0151
  contactBall := contact0151
  work := work0151
  center_sq := center_sq0151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0151.1
  jac_ok := checks0151.2.1
  accepted := checks0151.2.2

def cells : List CellCertificate := [cell0144, cell0145, cell0146, cell0147, cell0148, cell0149, cell0150, cell0151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018
