import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2248 : RatBall :=
  ⟨⟨9/320, 113/320⟩, 3/640⟩
def center2248 : GaussianRat :=
  ⟨22380501/1000000000, 127986203/500000000⟩
def contact2248 : RatBall := localContactBall tau2248 center2248
def work2248 : RoundedTauEval :=
  evalTau precision tau2248 contact2248 logTwoBall

theorem center_sq2248 : (center2248.re : ℝ)^2 +
    (center2248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2248 : work2248.theta.ok = true ∧
    work2248.jac.invOK = true ∧ acceptsUnitSq work2248.out = true := by
  norm_num [work2248, contact2248, tau2248, center2248, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2248 : CellCertificate where
  tauBall := tau2248
  contactCenter := center2248
  contactBall := contact2248
  work := work2248
  center_sq := center_sq2248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2248.1
  jac_ok := checks2248.2.1
  accepted := checks2248.2.2

def tau2249 : RatBall :=
  ⟨⟨11/320, 113/320⟩, 3/640⟩
def center2249 : GaussianRat :=
  ⟨5469449/200000000, 51168439/200000000⟩
def contact2249 : RatBall := localContactBall tau2249 center2249
def work2249 : RoundedTauEval :=
  evalTau precision tau2249 contact2249 logTwoBall

theorem center_sq2249 : (center2249.re : ℝ)^2 +
    (center2249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2249 : work2249.theta.ok = true ∧
    work2249.jac.invOK = true ∧ acceptsUnitSq work2249.out = true := by
  norm_num [work2249, contact2249, tau2249, center2249, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2249 : CellCertificate where
  tauBall := tau2249
  contactCenter := center2249
  contactBall := contact2249
  work := work2249
  center_sq := center_sq2249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2249.1
  jac_ok := checks2249.2.1
  accepted := checks2249.2.2

def tau2250 : RatBall :=
  ⟨⟨9/320, 23/64⟩, 3/640⟩
def center2250 : GaussianRat :=
  ⟨22499417/1000000000, 260954001/1000000000⟩
def contact2250 : RatBall := localContactBall tau2250 center2250
def work2250 : RoundedTauEval :=
  evalTau precision tau2250 contact2250 logTwoBall

theorem center_sq2250 : (center2250.re : ℝ)^2 +
    (center2250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2250 : work2250.theta.ok = true ∧
    work2250.jac.invOK = true ∧ acceptsUnitSq work2250.out = true := by
  norm_num [work2250, contact2250, tau2250, center2250, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2250 : CellCertificate where
  tauBall := tau2250
  contactCenter := center2250
  contactBall := contact2250
  work := work2250
  center_sq := center_sq2250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2250.1
  jac_ok := checks2250.2.1
  accepted := checks2250.2.2

def tau2251 : RatBall :=
  ⟨⟨11/320, 23/64⟩, 3/640⟩
def center2251 : GaussianRat :=
  ⟨27492413/1000000000, 2037657/7812500⟩
def contact2251 : RatBall := localContactBall tau2251 center2251
def work2251 : RoundedTauEval :=
  evalTau precision tau2251 contact2251 logTwoBall

theorem center_sq2251 : (center2251.re : ℝ)^2 +
    (center2251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2251 : work2251.theta.ok = true ∧
    work2251.jac.invOK = true ∧ acceptsUnitSq work2251.out = true := by
  norm_num [work2251, contact2251, tau2251, center2251, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2251 : CellCertificate where
  tauBall := tau2251
  contactCenter := center2251
  contactBall := contact2251
  work := work2251
  center_sq := center_sq2251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2251.1
  jac_ok := checks2251.2.1
  accepted := checks2251.2.2

def tau2252 : RatBall :=
  ⟨⟨13/320, 113/320⟩, 3/640⟩
def center2252 : GaussianRat :=
  ⟨32309979/1000000000, 127843073/500000000⟩
def contact2252 : RatBall := localContactBall tau2252 center2252
def work2252 : RoundedTauEval :=
  evalTau precision tau2252 contact2252 logTwoBall

theorem center_sq2252 : (center2252.re : ℝ)^2 +
    (center2252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2252 : work2252.theta.ok = true ∧
    work2252.jac.invOK = true ∧ acceptsUnitSq work2252.out = true := by
  norm_num [work2252, contact2252, tau2252, center2252, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2252 : CellCertificate where
  tauBall := tau2252
  contactCenter := center2252
  contactBall := contact2252
  work := work2252
  center_sq := center_sq2252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2252.1
  jac_ok := checks2252.2.1
  accepted := checks2252.2.2

def tau2253 : RatBall :=
  ⟨⟨3/64, 113/320⟩, 3/640⟩
def center2253 : GaussianRat :=
  ⟨18633993/500000000, 15969023/62500000⟩
def contact2253 : RatBall := localContactBall tau2253 center2253
def work2253 : RoundedTauEval :=
  evalTau precision tau2253 contact2253 logTwoBall

theorem center_sq2253 : (center2253.re : ℝ)^2 +
    (center2253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2253 : work2253.theta.ok = true ∧
    work2253.jac.invOK = true ∧ acceptsUnitSq work2253.out = true := by
  norm_num [work2253, contact2253, tau2253, center2253, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2253 : CellCertificate where
  tauBall := tau2253
  contactCenter := center2253
  contactBall := contact2253
  work := work2253
  center_sq := center_sq2253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2253.1
  jac_ok := checks2253.2.1
  accepted := checks2253.2.2

def tau2254 : RatBall :=
  ⟨⟨13/320, 23/64⟩, 3/640⟩
def center2254 : GaussianRat :=
  ⟨32481297/1000000000, 260659621/1000000000⟩
def contact2254 : RatBall := localContactBall tau2254 center2254
def work2254 : RoundedTauEval :=
  evalTau precision tau2254 contact2254 logTwoBall

theorem center_sq2254 : (center2254.re : ℝ)^2 +
    (center2254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2254 : work2254.theta.ok = true ∧
    work2254.jac.invOK = true ∧ acceptsUnitSq work2254.out = true := by
  norm_num [work2254, contact2254, tau2254, center2254, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2254 : CellCertificate where
  tauBall := tau2254
  contactCenter := center2254
  contactBall := contact2254
  work := work2254
  center_sq := center_sq2254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2254.1
  jac_ok := checks2254.2.1
  accepted := checks2254.2.2

def tau2255 : RatBall :=
  ⟨⟨3/64, 23/64⟩, 3/640⟩
def center2255 : GaussianRat :=
  ⟨37465331/1000000000, 260472693/1000000000⟩
def contact2255 : RatBall := localContactBall tau2255 center2255
def work2255 : RoundedTauEval :=
  evalTau precision tau2255 contact2255 logTwoBall

theorem center_sq2255 : (center2255.re : ℝ)^2 +
    (center2255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2255 : work2255.theta.ok = true ∧
    work2255.jac.invOK = true ∧ acceptsUnitSq work2255.out = true := by
  norm_num [work2255, contact2255, tau2255, center2255, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2255 : CellCertificate where
  tauBall := tau2255
  contactCenter := center2255
  contactBall := contact2255
  work := work2255
  center_sq := center_sq2255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2255.1
  jac_ok := checks2255.2.1
  accepted := checks2255.2.2

def cells : List CellCertificate := [cell2248, cell2249, cell2250, cell2251, cell2252, cell2253, cell2254, cell2255]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281
