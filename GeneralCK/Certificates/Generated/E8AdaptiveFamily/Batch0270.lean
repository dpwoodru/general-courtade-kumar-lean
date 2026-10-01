import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2160 : RatBall :=
  ⟨⟨-5/64, 117/320⟩, 3/640⟩
def center2160 : GaussianRat :=
  ⟨-3131077/50000000, 66025963/250000000⟩
def contact2160 : RatBall := localContactBall tau2160 center2160
def work2160 : RoundedTauEval :=
  evalTau precision tau2160 contact2160 logTwoBall

theorem center_sq2160 : (center2160.re : ℝ)^2 +
    (center2160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2160 : work2160.theta.ok = true ∧
    work2160.jac.invOK = true ∧ acceptsUnitSq work2160.out = true := by
  norm_num [work2160, contact2160, tau2160, center2160, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2160 : CellCertificate where
  tauBall := tau2160
  contactCenter := center2160
  contactBall := contact2160
  work := work2160
  center_sq := center_sq2160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2160.1
  jac_ok := checks2160.2.1
  accepted := checks2160.2.2

def tau2161 : RatBall :=
  ⟨⟨-27/320, 119/320⟩, 3/640⟩
def center2161 : GaussianRat :=
  ⟨-33978407/500000000, 67181393/250000000⟩
def contact2161 : RatBall := localContactBall tau2161 center2161
def work2161 : RoundedTauEval :=
  evalTau precision tau2161 contact2161 logTwoBall

theorem center_sq2161 : (center2161.re : ℝ)^2 +
    (center2161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2161 : work2161.theta.ok = true ∧
    work2161.jac.invOK = true ∧ acceptsUnitSq work2161.out = true := by
  norm_num [work2161, contact2161, tau2161, center2161, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2161 : CellCertificate where
  tauBall := tau2161
  contactCenter := center2161
  contactBall := contact2161
  work := work2161
  center_sq := center_sq2161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2161.1
  jac_ok := checks2161.2.1
  accepted := checks2161.2.2

def tau2162 : RatBall :=
  ⟨⟨-5/64, 119/320⟩, 3/640⟩
def center2162 : GaussianRat :=
  ⟨-1574127/25000000, 53817447/200000000⟩
def contact2162 : RatBall := localContactBall tau2162 center2162
def work2162 : RoundedTauEval :=
  evalTau precision tau2162 contact2162 logTwoBall

theorem center_sq2162 : (center2162.re : ℝ)^2 +
    (center2162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2162 : work2162.theta.ok = true ∧
    work2162.jac.invOK = true ∧ acceptsUnitSq work2162.out = true := by
  norm_num [work2162, contact2162, tau2162, center2162, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2162 : CellCertificate where
  tauBall := tau2162
  contactCenter := center2162
  contactBall := contact2162
  work := work2162
  center_sq := center_sq2162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2162.1
  jac_ok := checks2162.2.1
  accepted := checks2162.2.2

def tau2163 : RatBall :=
  ⟨⟨-23/320, 113/320⟩, 3/640⟩
def center2163 : GaussianRat :=
  ⟨-57038551/1000000000, 63630699/250000000⟩
def contact2163 : RatBall := localContactBall tau2163 center2163
def work2163 : RoundedTauEval :=
  evalTau precision tau2163 contact2163 logTwoBall

theorem center_sq2163 : (center2163.re : ℝ)^2 +
    (center2163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2163 : work2163.theta.ok = true ∧
    work2163.jac.invOK = true ∧ acceptsUnitSq work2163.out = true := by
  norm_num [work2163, contact2163, tau2163, center2163, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2163 : CellCertificate where
  tauBall := tau2163
  contactCenter := center2163
  contactBall := contact2163
  work := work2163
  center_sq := center_sq2163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2163.1
  jac_ok := checks2163.2.1
  accepted := checks2163.2.2

def tau2164 : RatBall :=
  ⟨⟨-21/320, 113/320⟩, 3/640⟩
def center2164 : GaussianRat :=
  ⟨-13026633/250000000, 254806033/1000000000⟩
def contact2164 : RatBall := localContactBall tau2164 center2164
def work2164 : RoundedTauEval :=
  evalTau precision tau2164 contact2164 logTwoBall

theorem center_sq2164 : (center2164.re : ℝ)^2 +
    (center2164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2164 : work2164.theta.ok = true ∧
    work2164.jac.invOK = true ∧ acceptsUnitSq work2164.out = true := by
  norm_num [work2164, contact2164, tau2164, center2164, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2164 : CellCertificate where
  tauBall := tau2164
  contactCenter := center2164
  contactBall := contact2164
  work := work2164
  center_sq := center_sq2164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2164.1
  jac_ok := checks2164.2.1
  accepted := checks2164.2.2

def tau2165 : RatBall :=
  ⟨⟨-23/320, 23/64⟩, 3/640⟩
def center2165 : GaussianRat :=
  ⟨-5733843/100000000, 129731693/500000000⟩
def contact2165 : RatBall := localContactBall tau2165 center2165
def work2165 : RoundedTauEval :=
  evalTau precision tau2165 contact2165 logTwoBall

theorem center_sq2165 : (center2165.re : ℝ)^2 +
    (center2165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2165 : work2165.theta.ok = true ∧
    work2165.jac.invOK = true ∧ acceptsUnitSq work2165.out = true := by
  norm_num [work2165, contact2165, tau2165, center2165, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2165 : CellCertificate where
  tauBall := tau2165
  contactCenter := center2165
  contactBall := contact2165
  work := work2165
  center_sq := center_sq2165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2165.1
  jac_ok := checks2165.2.1
  accepted := checks2165.2.2

def tau2166 : RatBall :=
  ⟨⟨-21/320, 23/64⟩, 3/640⟩
def center2166 : GaussianRat :=
  ⟨-6547631/125000000, 64938653/250000000⟩
def contact2166 : RatBall := localContactBall tau2166 center2166
def work2166 : RoundedTauEval :=
  evalTau precision tau2166 contact2166 logTwoBall

theorem center_sq2166 : (center2166.re : ℝ)^2 +
    (center2166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2166 : work2166.theta.ok = true ∧
    work2166.jac.invOK = true ∧ acceptsUnitSq work2166.out = true := by
  norm_num [work2166, contact2166, tau2166, center2166, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2166 : CellCertificate where
  tauBall := tau2166
  contactCenter := center2166
  contactBall := contact2166
  work := work2166
  center_sq := center_sq2166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2166.1
  jac_ok := checks2166.2.1
  accepted := checks2166.2.2

def tau2167 : RatBall :=
  ⟨⟨-19/320, 113/320⟩, 3/640⟩
def center2167 : GaussianRat :=
  ⟨-47166967/1000000000, 255064157/1000000000⟩
def contact2167 : RatBall := localContactBall tau2167 center2167
def work2167 : RoundedTauEval :=
  evalTau precision tau2167 contact2167 logTwoBall

theorem center_sq2167 : (center2167.re : ℝ)^2 +
    (center2167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2167 : work2167.theta.ok = true ∧
    work2167.jac.invOK = true ∧ acceptsUnitSq work2167.out = true := by
  norm_num [work2167, contact2167, tau2167, center2167, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2167 : CellCertificate where
  tauBall := tau2167
  contactCenter := center2167
  contactBall := contact2167
  work := work2167
  center_sq := center_sq2167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2167.1
  jac_ok := checks2167.2.1
  accepted := checks2167.2.2

def cells : List CellCertificate := [cell2160, cell2161, cell2162, cell2163, cell2164, cell2165, cell2166, cell2167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270
