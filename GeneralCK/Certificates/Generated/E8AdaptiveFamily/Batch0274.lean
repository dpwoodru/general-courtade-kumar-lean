import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2192 : RatBall :=
  ⟨⟨-3/64, 119/320⟩, 3/640⟩
def center2192 : GaussianRat :=
  ⟨-18938457/500000000, 5409781/20000000⟩
def contact2192 : RatBall := localContactBall tau2192 center2192
def work2192 : RoundedTauEval :=
  evalTau precision tau2192 contact2192 logTwoBall

theorem center_sq2192 : (center2192.re : ℝ)^2 +
    (center2192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2192 : work2192.theta.ok = true ∧
    work2192.jac.invOK = true ∧ acceptsUnitSq work2192.out = true := by
  norm_num [work2192, contact2192, tau2192, center2192, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2192 : CellCertificate where
  tauBall := tau2192
  contactCenter := center2192
  contactBall := contact2192
  work := work2192
  center_sq := center_sq2192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2192.1
  jac_ok := checks2192.2.1
  accepted := checks2192.2.2

def tau2193 : RatBall :=
  ⟨⟨-13/320, 119/320⟩, 3/640⟩
def center2193 : GaussianRat :=
  ⟨-32838611/1000000000, 135343343/500000000⟩
def contact2193 : RatBall := localContactBall tau2193 center2193
def work2193 : RoundedTauEval :=
  evalTau precision tau2193 contact2193 logTwoBall

theorem center_sq2193 : (center2193.re : ℝ)^2 +
    (center2193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2193 : work2193.theta.ok = true ∧
    work2193.jac.invOK = true ∧ acceptsUnitSq work2193.out = true := by
  norm_num [work2193, contact2193, tau2193, center2193, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2193 : CellCertificate where
  tauBall := tau2193
  contactCenter := center2193
  contactBall := contact2193
  work := work2193
  center_sq := center_sq2193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2193.1
  jac_ok := checks2193.2.1
  accepted := checks2193.2.2

def tau2194 : RatBall :=
  ⟨⟨-11/320, 117/320⟩, 3/640⟩
def center2194 : GaussianRat :=
  ⟨-863803/31250000, 33228071/125000000⟩
def contact2194 : RatBall := localContactBall tau2194 center2194
def work2194 : RoundedTauEval :=
  evalTau precision tau2194 contact2194 logTwoBall

theorem center_sq2194 : (center2194.re : ℝ)^2 +
    (center2194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2194 : work2194.theta.ok = true ∧
    work2194.jac.invOK = true ∧ acceptsUnitSq work2194.out = true := by
  norm_num [work2194, contact2194, tau2194, center2194, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2194 : CellCertificate where
  tauBall := tau2194
  contactCenter := center2194
  contactBall := contact2194
  work := work2194
  center_sq := center_sq2194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2194.1
  jac_ok := checks2194.2.1
  accepted := checks2194.2.2

def tau2195 : RatBall :=
  ⟨⟨-9/320, 117/320⟩, 3/640⟩
def center2195 : GaussianRat :=
  ⟨-4524341/200000000, 53192453/200000000⟩
def contact2195 : RatBall := localContactBall tau2195 center2195
def work2195 : RoundedTauEval :=
  evalTau precision tau2195 contact2195 logTwoBall

theorem center_sq2195 : (center2195.re : ℝ)^2 +
    (center2195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2195 : work2195.theta.ok = true ∧
    work2195.jac.invOK = true ∧ acceptsUnitSq work2195.out = true := by
  norm_num [work2195, contact2195, tau2195, center2195, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2195 : CellCertificate where
  tauBall := tau2195
  contactCenter := center2195
  contactBall := contact2195
  work := work2195
  center_sq := center_sq2195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2195.1
  jac_ok := checks2195.2.1
  accepted := checks2195.2.2

def tau2196 : RatBall :=
  ⟨⟨-11/320, 119/320⟩, 3/640⟩
def center2196 : GaussianRat :=
  ⟨-27795199/1000000000, 135428181/500000000⟩
def contact2196 : RatBall := localContactBall tau2196 center2196
def work2196 : RoundedTauEval :=
  evalTau precision tau2196 contact2196 logTwoBall

theorem center_sq2196 : (center2196.re : ℝ)^2 +
    (center2196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2196 : work2196.theta.ok = true ∧
    work2196.jac.invOK = true ∧ acceptsUnitSq work2196.out = true := by
  norm_num [work2196, contact2196, tau2196, center2196, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2196 : CellCertificate where
  tauBall := tau2196
  contactCenter := center2196
  contactBall := contact2196
  work := work2196
  center_sq := center_sq2196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2196.1
  jac_ok := checks2196.2.1
  accepted := checks2196.2.2

def tau2197 : RatBall :=
  ⟨⟨-9/320, 119/320⟩, 3/640⟩
def center2197 : GaussianRat :=
  ⟨-22747453/1000000000, 270997951/1000000000⟩
def contact2197 : RatBall := localContactBall tau2197 center2197
def work2197 : RoundedTauEval :=
  evalTau precision tau2197 contact2197 logTwoBall

theorem center_sq2197 : (center2197.re : ℝ)^2 +
    (center2197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2197]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2197 : work2197.theta.ok = true ∧
    work2197.jac.invOK = true ∧ acceptsUnitSq work2197.out = true := by
  norm_num [work2197, contact2197, tau2197, center2197, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2197 : CellCertificate where
  tauBall := tau2197
  contactCenter := center2197
  contactBall := contact2197
  work := work2197
  center_sq := center_sq2197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2197.1
  jac_ok := checks2197.2.1
  accepted := checks2197.2.2

def tau2198 : RatBall :=
  ⟨⟨-7/320, 113/320⟩, 3/640⟩
def center2198 : GaussianRat :=
  ⟨-17410471/1000000000, 51215337/200000000⟩
def contact2198 : RatBall := localContactBall tau2198 center2198
def work2198 : RoundedTauEval :=
  evalTau precision tau2198 contact2198 logTwoBall

theorem center_sq2198 : (center2198.re : ℝ)^2 +
    (center2198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2198 : work2198.theta.ok = true ∧
    work2198.jac.invOK = true ∧ acceptsUnitSq work2198.out = true := by
  norm_num [work2198, contact2198, tau2198, center2198, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2198 : CellCertificate where
  tauBall := tau2198
  contactCenter := center2198
  contactBall := contact2198
  work := work2198
  center_sq := center_sq2198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2198.1
  jac_ok := checks2198.2.1
  accepted := checks2198.2.2

def tau2199 : RatBall :=
  ⟨⟨-1/64, 113/320⟩, 3/640⟩
def center2199 : GaussianRat :=
  ⟨-12437881/1000000000, 3201937/12500000⟩
def contact2199 : RatBall := localContactBall tau2199 center2199
def work2199 : RoundedTauEval :=
  evalTau precision tau2199 contact2199 logTwoBall

theorem center_sq2199 : (center2199.re : ℝ)^2 +
    (center2199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2199 : work2199.theta.ok = true ∧
    work2199.jac.invOK = true ∧ acceptsUnitSq work2199.out = true := by
  norm_num [work2199, contact2199, tau2199, center2199, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2199 : CellCertificate where
  tauBall := tau2199
  contactCenter := center2199
  contactBall := contact2199
  work := work2199
  center_sq := center_sq2199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2199.1
  jac_ok := checks2199.2.1
  accepted := checks2199.2.2

def cells : List CellCertificate := [cell2192, cell2193, cell2194, cell2195, cell2196, cell2197, cell2198, cell2199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274
