import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0240 : RatBall :=
  ⟨⟨-13/80, 13/80⟩, 3/160⟩
def center0240 : GaussianRat :=
  ⟨-114628827/1000000000, 110510723/1000000000⟩
def contact0240 : RatBall := localContactBall tau0240 center0240
def work0240 : RoundedTauEval :=
  evalTau precision tau0240 contact0240 logTwoBall

theorem center_sq0240 : (center0240.re : ℝ)^2 +
    (center0240.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0240]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0240 : work0240.theta.ok = true ∧
    work0240.jac.invOK = true ∧ acceptsUnitSq work0240.out = true := by
  norm_num [work0240, contact0240, tau0240, center0240, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0240 : CellCertificate where
  tauBall := tau0240
  contactCenter := center0240
  contactBall := contact0240
  work := work0240
  center_sq := center_sq0240
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0240.1
  jac_ok := checks0240.2.1
  accepted := checks0240.2.2

def tau0241 : RatBall :=
  ⟨⟨-3/16, 3/16⟩, 3/160⟩
def center0241 : GaussianRat :=
  ⟨-132989007/1000000000, 15833617/125000000⟩
def contact0241 : RatBall := localContactBall tau0241 center0241
def work0241 : RoundedTauEval :=
  evalTau precision tau0241 contact0241 logTwoBall

theorem center_sq0241 : (center0241.re : ℝ)^2 +
    (center0241.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0241]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0241 : work0241.theta.ok = true ∧
    work0241.jac.invOK = true ∧ acceptsUnitSq work0241.out = true := by
  norm_num [work0241, contact0241, tau0241, center0241, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0241 : CellCertificate where
  tauBall := tau0241
  contactCenter := center0241
  contactBall := contact0241
  work := work0241
  center_sq := center_sq0241
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0241.1
  jac_ok := checks0241.2.1
  accepted := checks0241.2.2

def tau0242 : RatBall :=
  ⟨⟨-13/80, 3/16⟩, 3/160⟩
def center0242 : GaussianRat :=
  ⟨-115659239/1000000000, 127856533/1000000000⟩
def contact0242 : RatBall := localContactBall tau0242 center0242
def work0242 : RoundedTauEval :=
  evalTau precision tau0242 contact0242 logTwoBall

theorem center_sq0242 : (center0242.re : ℝ)^2 +
    (center0242.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0242]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0242 : work0242.theta.ok = true ∧
    work0242.jac.invOK = true ∧ acceptsUnitSq work0242.out = true := by
  norm_num [work0242, contact0242, tau0242, center0242, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0242 : CellCertificate where
  tauBall := tau0242
  contactCenter := center0242
  contactBall := contact0242
  work := work0242
  center_sq := center_sq0242
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0242.1
  jac_ok := checks0242.2.1
  accepted := checks0242.2.2

def tau0243 : RatBall :=
  ⟨⟨-11/80, 13/80⟩, 3/160⟩
def center0243 : GaussianRat :=
  ⟨-48637291/500000000, 111393603/1000000000⟩
def contact0243 : RatBall := localContactBall tau0243 center0243
def work0243 : RoundedTauEval :=
  evalTau precision tau0243 contact0243 logTwoBall

theorem center_sq0243 : (center0243.re : ℝ)^2 +
    (center0243.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0243]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0243 : work0243.theta.ok = true ∧
    work0243.jac.invOK = true ∧ acceptsUnitSq work0243.out = true := by
  norm_num [work0243, contact0243, tau0243, center0243, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0243 : CellCertificate where
  tauBall := tau0243
  contactCenter := center0243
  contactBall := contact0243
  work := work0243
  center_sq := center_sq0243
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0243.1
  jac_ok := checks0243.2.1
  accepted := checks0243.2.2

def tau0244 : RatBall :=
  ⟨⟨-9/80, 13/80⟩, 3/160⟩
def center0244 : GaussianRat :=
  ⟨-79781827/1000000000, 56070187/500000000⟩
def contact0244 : RatBall := localContactBall tau0244 center0244
def work0244 : RoundedTauEval :=
  evalTau precision tau0244 contact0244 logTwoBall

theorem center_sq0244 : (center0244.re : ℝ)^2 +
    (center0244.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0244 : work0244.theta.ok = true ∧
    work0244.jac.invOK = true ∧ acceptsUnitSq work0244.out = true := by
  norm_num [work0244, contact0244, tau0244, center0244, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0244 : CellCertificate where
  tauBall := tau0244
  contactCenter := center0244
  contactBall := contact0244
  work := work0244
  center_sq := center_sq0244
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0244.1
  jac_ok := checks0244.2.1
  accepted := checks0244.2.2

def tau0245 : RatBall :=
  ⟨⟨-11/80, 3/16⟩, 3/160⟩
def center0245 : GaussianRat :=
  ⟨-1227011/12500000, 8055803/62500000⟩
def contact0245 : RatBall := localContactBall tau0245 center0245
def work0245 : RoundedTauEval :=
  evalTau precision tau0245 contact0245 logTwoBall

theorem center_sq0245 : (center0245.re : ℝ)^2 +
    (center0245.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0245]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0245 : work0245.theta.ok = true ∧
    work0245.jac.invOK = true ∧ acceptsUnitSq work0245.out = true := by
  norm_num [work0245, contact0245, tau0245, center0245, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0245 : CellCertificate where
  tauBall := tau0245
  contactCenter := center0245
  contactBall := contact0245
  work := work0245
  center_sq := center_sq0245
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0245.1
  jac_ok := checks0245.2.1
  accepted := checks0245.2.2

def tau0246 : RatBall :=
  ⟨⟨-9/80, 3/16⟩, 3/160⟩
def center0246 : GaussianRat :=
  ⟨-80517041/1000000000, 8110609/62500000⟩
def contact0246 : RatBall := localContactBall tau0246 center0246
def work0246 : RoundedTauEval :=
  evalTau precision tau0246 contact0246 logTwoBall

theorem center_sq0246 : (center0246.re : ℝ)^2 +
    (center0246.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0246]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0246 : work0246.theta.ok = true ∧
    work0246.jac.invOK = true ∧ acceptsUnitSq work0246.out = true := by
  norm_num [work0246, contact0246, tau0246, center0246, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0246 : CellCertificate where
  tauBall := tau0246
  contactCenter := center0246
  contactBall := contact0246
  work := work0246
  center_sq := center_sq0246
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0246.1
  jac_ok := checks0246.2.1
  accepted := checks0246.2.2

def tau0247 : RatBall :=
  ⟨⟨-7/80, 13/80⟩, 3/160⟩
def center0247 : GaussianRat :=
  ⟨-31086987/500000000, 112745169/1000000000⟩
def contact0247 : RatBall := localContactBall tau0247 center0247
def work0247 : RoundedTauEval :=
  evalTau precision tau0247 contact0247 logTwoBall

theorem center_sq0247 : (center0247.re : ℝ)^2 +
    (center0247.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0247]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0247 : work0247.theta.ok = true ∧
    work0247.jac.invOK = true ∧ acceptsUnitSq work0247.out = true := by
  norm_num [work0247, contact0247, tau0247, center0247, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0247 : CellCertificate where
  tauBall := tau0247
  contactCenter := center0247
  contactBall := contact0247
  work := work0247
  center_sq := center_sq0247
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0247.1
  jac_ok := checks0247.2.1
  accepted := checks0247.2.2

def cells : List CellCertificate := [cell0240, cell0241, cell0242, cell0243, cell0244, cell0245, cell0246, cell0247]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030
