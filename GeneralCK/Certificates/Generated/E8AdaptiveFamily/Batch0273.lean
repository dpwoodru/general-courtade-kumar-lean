import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2184 : RatBall :=
  ⟨⟨-3/64, 23/64⟩, 3/640⟩
def center2184 : GaussianRat :=
  ⟨-37465331/1000000000, 260472693/1000000000⟩
def contact2184 : RatBall := localContactBall tau2184 center2184
def work2184 : RoundedTauEval :=
  evalTau precision tau2184 contact2184 logTwoBall

theorem center_sq2184 : (center2184.re : ℝ)^2 +
    (center2184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2184 : work2184.theta.ok = true ∧
    work2184.jac.invOK = true ∧ acceptsUnitSq work2184.out = true := by
  norm_num [work2184, contact2184, tau2184, center2184, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2184 : CellCertificate where
  tauBall := tau2184
  contactCenter := center2184
  contactBall := contact2184
  work := work2184
  center_sq := center_sq2184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2184.1
  jac_ok := checks2184.2.1
  accepted := checks2184.2.2

def tau2185 : RatBall :=
  ⟨⟨-13/320, 23/64⟩, 3/640⟩
def center2185 : GaussianRat :=
  ⟨-32481297/1000000000, 260659621/1000000000⟩
def contact2185 : RatBall := localContactBall tau2185 center2185
def work2185 : RoundedTauEval :=
  evalTau precision tau2185 contact2185 logTwoBall

theorem center_sq2185 : (center2185.re : ℝ)^2 +
    (center2185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2185 : work2185.theta.ok = true ∧
    work2185.jac.invOK = true ∧ acceptsUnitSq work2185.out = true := by
  norm_num [work2185, contact2185, tau2185, center2185, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2185 : CellCertificate where
  tauBall := tau2185
  contactCenter := center2185
  contactBall := contact2185
  work := work2185
  center_sq := center_sq2185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2185.1
  jac_ok := checks2185.2.1
  accepted := checks2185.2.2

def tau2186 : RatBall :=
  ⟨⟨-11/320, 113/320⟩, 3/640⟩
def center2186 : GaussianRat :=
  ⟨-5469449/200000000, 51168439/200000000⟩
def contact2186 : RatBall := localContactBall tau2186 center2186
def work2186 : RoundedTauEval :=
  evalTau precision tau2186 contact2186 logTwoBall

theorem center_sq2186 : (center2186.re : ℝ)^2 +
    (center2186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2186 : work2186.theta.ok = true ∧
    work2186.jac.invOK = true ∧ acceptsUnitSq work2186.out = true := by
  norm_num [work2186, contact2186, tau2186, center2186, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2186 : CellCertificate where
  tauBall := tau2186
  contactCenter := center2186
  contactBall := contact2186
  work := work2186
  center_sq := center_sq2186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2186.1
  jac_ok := checks2186.2.1
  accepted := checks2186.2.2

def tau2187 : RatBall :=
  ⟨⟨-9/320, 113/320⟩, 3/640⟩
def center2187 : GaussianRat :=
  ⟨-22380501/1000000000, 127986203/500000000⟩
def contact2187 : RatBall := localContactBall tau2187 center2187
def work2187 : RoundedTauEval :=
  evalTau precision tau2187 contact2187 logTwoBall

theorem center_sq2187 : (center2187.re : ℝ)^2 +
    (center2187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2187 : work2187.theta.ok = true ∧
    work2187.jac.invOK = true ∧ acceptsUnitSq work2187.out = true := by
  norm_num [work2187, contact2187, tau2187, center2187, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2187 : CellCertificate where
  tauBall := tau2187
  contactCenter := center2187
  contactBall := contact2187
  work := work2187
  center_sq := center_sq2187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2187.1
  jac_ok := checks2187.2.1
  accepted := checks2187.2.2

def tau2188 : RatBall :=
  ⟨⟨-11/320, 23/64⟩, 3/640⟩
def center2188 : GaussianRat :=
  ⟨-27492413/1000000000, 2037657/7812500⟩
def contact2188 : RatBall := localContactBall tau2188 center2188
def work2188 : RoundedTauEval :=
  evalTau precision tau2188 contact2188 logTwoBall

theorem center_sq2188 : (center2188.re : ℝ)^2 +
    (center2188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2188 : work2188.theta.ok = true ∧
    work2188.jac.invOK = true ∧ acceptsUnitSq work2188.out = true := by
  norm_num [work2188, contact2188, tau2188, center2188, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2188 : CellCertificate where
  tauBall := tau2188
  contactCenter := center2188
  contactBall := contact2188
  work := work2188
  center_sq := center_sq2188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2188.1
  jac_ok := checks2188.2.1
  accepted := checks2188.2.2

def tau2189 : RatBall :=
  ⟨⟨-9/320, 23/64⟩, 3/640⟩
def center2189 : GaussianRat :=
  ⟨-22499417/1000000000, 260954001/1000000000⟩
def contact2189 : RatBall := localContactBall tau2189 center2189
def work2189 : RoundedTauEval :=
  evalTau precision tau2189 contact2189 logTwoBall

theorem center_sq2189 : (center2189.re : ℝ)^2 +
    (center2189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2189 : work2189.theta.ok = true ∧
    work2189.jac.invOK = true ∧ acceptsUnitSq work2189.out = true := by
  norm_num [work2189, contact2189, tau2189, center2189, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2189 : CellCertificate where
  tauBall := tau2189
  contactCenter := center2189
  contactBall := contact2189
  work := work2189
  center_sq := center_sq2189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2189.1
  jac_ok := checks2189.2.1
  accepted := checks2189.2.2

def tau2190 : RatBall :=
  ⟨⟨-3/64, 117/320⟩, 3/640⟩
def center2190 : GaussianRat :=
  ⟨-18834129/500000000, 13273367/50000000⟩
def contact2190 : RatBall := localContactBall tau2190 center2190
def work2190 : RoundedTauEval :=
  evalTau precision tau2190 contact2190 logTwoBall

theorem center_sq2190 : (center2190.re : ℝ)^2 +
    (center2190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2190 : work2190.theta.ok = true ∧
    work2190.jac.invOK = true ∧ acceptsUnitSq work2190.out = true := by
  norm_num [work2190, contact2190, tau2190, center2190, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2190 : CellCertificate where
  tauBall := tau2190
  contactCenter := center2190
  contactBall := contact2190
  work := work2190
  center_sq := center_sq2190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2190.1
  jac_ok := checks2190.2.1
  accepted := checks2190.2.2

def tau2191 : RatBall :=
  ⟨⟨-13/320, 117/320⟩, 3/640⟩
def center2191 : GaussianRat :=
  ⟨-6531493/200000000, 265659553/1000000000⟩
def contact2191 : RatBall := localContactBall tau2191 center2191
def work2191 : RoundedTauEval :=
  evalTau precision tau2191 contact2191 logTwoBall

theorem center_sq2191 : (center2191.re : ℝ)^2 +
    (center2191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2191 : work2191.theta.ok = true ∧
    work2191.jac.invOK = true ∧ acceptsUnitSq work2191.out = true := by
  norm_num [work2191, contact2191, tau2191, center2191, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2191 : CellCertificate where
  tauBall := tau2191
  contactCenter := center2191
  contactBall := contact2191
  work := work2191
  center_sq := center_sq2191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2191.1
  jac_ok := checks2191.2.1
  accepted := checks2191.2.2

def cells : List CellCertificate := [cell2184, cell2185, cell2186, cell2187, cell2188, cell2189, cell2190, cell2191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273
