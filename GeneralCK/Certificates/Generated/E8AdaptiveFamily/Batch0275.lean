import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2200 : RatBall :=
  ⟨⟨-7/320, 23/64⟩, 3/640⟩
def center2200 : GaussianRat :=
  ⟨-350061/20000000, 130530621/500000000⟩
def contact2200 : RatBall := localContactBall tau2200 center2200
def work2200 : RoundedTauEval :=
  evalTau precision tau2200 contact2200 logTwoBall

theorem center_sq2200 : (center2200.re : ℝ)^2 +
    (center2200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2200 : work2200.theta.ok = true ∧
    work2200.jac.invOK = true ∧ acceptsUnitSq work2200.out = true := by
  norm_num [work2200, contact2200, tau2200, center2200, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2200 : CellCertificate where
  tauBall := tau2200
  contactCenter := center2200
  contactBall := contact2200
  work := work2200
  center_sq := center_sq2200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2200.1
  jac_ok := checks2200.2.1
  accepted := checks2200.2.2

def tau2201 : RatBall :=
  ⟨⟨-1/64, 23/64⟩, 3/640⟩
def center2201 : GaussianRat :=
  ⟨-1563007/125000000, 13057087/50000000⟩
def contact2201 : RatBall := localContactBall tau2201 center2201
def work2201 : RoundedTauEval :=
  evalTau precision tau2201 contact2201 logTwoBall

theorem center_sq2201 : (center2201.re : ℝ)^2 +
    (center2201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2201 : work2201.theta.ok = true ∧
    work2201.jac.invOK = true ∧ acceptsUnitSq work2201.out = true := by
  norm_num [work2201, contact2201, tau2201, center2201, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2201 : CellCertificate where
  tauBall := tau2201
  contactCenter := center2201
  contactBall := contact2201
  work := work2201
  center_sq := center_sq2201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2201.1
  jac_ok := checks2201.2.1
  accepted := checks2201.2.2

def tau2202 : RatBall :=
  ⟨⟨-7/320, 117/320⟩, 3/640⟩
def center2202 : GaussianRat :=
  ⟨-3519651/200000000, 8314767/31250000⟩
def contact2202 : RatBall := localContactBall tau2202 center2202
def work2202 : RoundedTauEval :=
  evalTau precision tau2202 contact2202 logTwoBall

theorem center_sq2202 : (center2202.re : ℝ)^2 +
    (center2202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2202 : work2202.theta.ok = true ∧
    work2202.jac.invOK = true ∧ acceptsUnitSq work2202.out = true := by
  norm_num [work2202, contact2202, tau2202, center2202, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2202 : CellCertificate where
  tauBall := tau2202
  contactCenter := center2202
  contactBall := contact2202
  work := work2202
  center_sq := center_sq2202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2202.1
  jac_ok := checks2202.2.1
  accepted := checks2202.2.2

def tau2203 : RatBall :=
  ⟨⟨-1/64, 117/320⟩, 3/640⟩
def center2203 : GaussianRat :=
  ⟨-1257211/100000000, 66538831/250000000⟩
def contact2203 : RatBall := localContactBall tau2203 center2203
def work2203 : RoundedTauEval :=
  evalTau precision tau2203 contact2203 logTwoBall

theorem center_sq2203 : (center2203.re : ℝ)^2 +
    (center2203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2203 : work2203.theta.ok = true ∧
    work2203.jac.invOK = true ∧ acceptsUnitSq work2203.out = true := by
  norm_num [work2203, contact2203, tau2203, center2203, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2203 : CellCertificate where
  tauBall := tau2203
  contactCenter := center2203
  contactBall := contact2203
  work := work2203
  center_sq := center_sq2203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2203.1
  jac_ok := checks2203.2.1
  accepted := checks2203.2.2

def tau2204 : RatBall :=
  ⟨⟨-7/320, 119/320⟩, 3/640⟩
def center2204 : GaussianRat :=
  ⟨-3539231/200000000, 67777837/250000000⟩
def contact2204 : RatBall := localContactBall tau2204 center2204
def work2204 : RoundedTauEval :=
  evalTau precision tau2204 contact2204 logTwoBall

theorem center_sq2204 : (center2204.re : ℝ)^2 +
    (center2204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2204 : work2204.theta.ok = true ∧
    work2204.jac.invOK = true ∧ acceptsUnitSq work2204.out = true := by
  norm_num [work2204, contact2204, tau2204, center2204, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2204 : CellCertificate where
  tauBall := tau2204
  contactCenter := center2204
  contactBall := contact2204
  work := work2204
  center_sq := center_sq2204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2204.1
  jac_ok := checks2204.2.1
  accepted := checks2204.2.2

def tau2205 : RatBall :=
  ⟨⟨-1/64, 119/320⟩, 3/640⟩
def center2205 : GaussianRat :=
  ⟨-1264209/100000000, 27119647/100000000⟩
def contact2205 : RatBall := localContactBall tau2205 center2205
def work2205 : RoundedTauEval :=
  evalTau precision tau2205 contact2205 logTwoBall

theorem center_sq2205 : (center2205.re : ℝ)^2 +
    (center2205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2205 : work2205.theta.ok = true ∧
    work2205.jac.invOK = true ∧ acceptsUnitSq work2205.out = true := by
  norm_num [work2205, contact2205, tau2205, center2205, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2205 : CellCertificate where
  tauBall := tau2205
  contactCenter := center2205
  contactBall := contact2205
  work := work2205
  center_sq := center_sq2205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2205.1
  jac_ok := checks2205.2.1
  accepted := checks2205.2.2

def tau2206 : RatBall :=
  ⟨⟨-3/320, 117/320⟩, 3/640⟩
def center2206 : GaussianRat :=
  ⟨-7544037/1000000000, 16638159/62500000⟩
def contact2206 : RatBall := localContactBall tau2206 center2206
def work2206 : RoundedTauEval :=
  evalTau precision tau2206 contact2206 logTwoBall

theorem center_sq2206 : (center2206.re : ℝ)^2 +
    (center2206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2206 : work2206.theta.ok = true ∧
    work2206.jac.invOK = true ∧ acceptsUnitSq work2206.out = true := by
  norm_num [work2206, contact2206, tau2206, center2206, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2206 : CellCertificate where
  tauBall := tau2206
  contactCenter := center2206
  contactBall := contact2206
  work := work2206
  center_sq := center_sq2206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2206.1
  jac_ok := checks2206.2.1
  accepted := checks2206.2.2

def tau2207 : RatBall :=
  ⟨⟨-1/320, 117/320⟩, 3/640⟩
def center2207 : GaussianRat :=
  ⟨-314351/125000000, 66559541/250000000⟩
def contact2207 : RatBall := localContactBall tau2207 center2207
def work2207 : RoundedTauEval :=
  evalTau precision tau2207 contact2207 logTwoBall

theorem center_sq2207 : (center2207.re : ℝ)^2 +
    (center2207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2207 : work2207.theta.ok = true ∧
    work2207.jac.invOK = true ∧ acceptsUnitSq work2207.out = true := by
  norm_num [work2207, contact2207, tau2207, center2207, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2207 : CellCertificate where
  tauBall := tau2207
  contactCenter := center2207
  contactBall := contact2207
  work := work2207
  center_sq := center_sq2207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2207.1
  jac_ok := checks2207.2.1
  accepted := checks2207.2.2

def cells : List CellCertificate := [cell2200, cell2201, cell2202, cell2203, cell2204, cell2205, cell2206, cell2207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275
