import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2176 : RatBall :=
  ⟨⟨-17/320, 117/320⟩, 3/640⟩
def center2176 : GaussianRat :=
  ⟨-10668331/250000000, 265248069/1000000000⟩
def contact2176 : RatBall := localContactBall tau2176 center2176
def work2176 : RoundedTauEval :=
  evalTau precision tau2176 contact2176 logTwoBall

theorem center_sq2176 : (center2176.re : ℝ)^2 +
    (center2176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2176 : work2176.theta.ok = true ∧
    work2176.jac.invOK = true ∧ acceptsUnitSq work2176.out = true := by
  norm_num [work2176, contact2176, tau2176, center2176, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2176 : CellCertificate where
  tauBall := tau2176
  contactCenter := center2176
  contactBall := contact2176
  work := work2176
  center_sq := center_sq2176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2176.1
  jac_ok := checks2176.2.1
  accepted := checks2176.2.2

def tau2177 : RatBall :=
  ⟨⟨-19/320, 119/320⟩, 3/640⟩
def center2177 : GaussianRat :=
  ⟨-47935117/1000000000, 2109457/7812500⟩
def contact2177 : RatBall := localContactBall tau2177 center2177
def work2177 : RoundedTauEval :=
  evalTau precision tau2177 contact2177 logTwoBall

theorem center_sq2177 : (center2177.re : ℝ)^2 +
    (center2177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2177 : work2177.theta.ok = true ∧
    work2177.jac.invOK = true ∧ acceptsUnitSq work2177.out = true := by
  norm_num [work2177, contact2177, tau2177, center2177, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2177 : CellCertificate where
  tauBall := tau2177
  contactCenter := center2177
  contactBall := contact2177
  work := work2177
  center_sq := center_sq2177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2177.1
  jac_ok := checks2177.2.1
  accepted := checks2177.2.2

def tau2178 : RatBall :=
  ⟨⟨-17/320, 119/320⟩, 3/640⟩
def center2178 : GaussianRat :=
  ⟨-42909337/1000000000, 135131799/500000000⟩
def contact2178 : RatBall := localContactBall tau2178 center2178
def work2178 : RoundedTauEval :=
  evalTau precision tau2178 contact2178 logTwoBall

theorem center_sq2178 : (center2178.re : ℝ)^2 +
    (center2178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2178 : work2178.theta.ok = true ∧
    work2178.jac.invOK = true ∧ acceptsUnitSq work2178.out = true := by
  norm_num [work2178, contact2178, tau2178, center2178, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2178 : CellCertificate where
  tauBall := tau2178
  contactCenter := center2178
  contactBall := contact2178
  work := work2178
  center_sq := center_sq2178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2178.1
  jac_ok := checks2178.2.1
  accepted := checks2178.2.2

def tau2179 : RatBall :=
  ⟨⟨-21/320, 121/320⟩, 3/640⟩
def center2179 : GaussianRat :=
  ⟨-53251841/1000000000, 54951623/200000000⟩
def contact2179 : RatBall := localContactBall tau2179 center2179
def work2179 : RoundedTauEval :=
  evalTau precision tau2179 contact2179 logTwoBall

theorem center_sq2179 : (center2179.re : ℝ)^2 +
    (center2179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2179 : work2179.theta.ok = true ∧
    work2179.jac.invOK = true ∧ acceptsUnitSq work2179.out = true := by
  norm_num [work2179, contact2179, tau2179, center2179, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2179 : CellCertificate where
  tauBall := tau2179
  contactCenter := center2179
  contactBall := contact2179
  work := work2179
  center_sq := center_sq2179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2179.1
  jac_ok := checks2179.2.1
  accepted := checks2179.2.2

def tau2180 : RatBall :=
  ⟨⟨-19/320, 121/320⟩, 3/640⟩
def center2180 : GaussianRat :=
  ⟨-48205717/1000000000, 275046561/1000000000⟩
def contact2180 : RatBall := localContactBall tau2180 center2180
def work2180 : RoundedTauEval :=
  evalTau precision tau2180 contact2180 logTwoBall

theorem center_sq2180 : (center2180.re : ℝ)^2 +
    (center2180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2180 : work2180.theta.ok = true ∧
    work2180.jac.invOK = true ∧ acceptsUnitSq work2180.out = true := by
  norm_num [work2180, contact2180, tau2180, center2180, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2180 : CellCertificate where
  tauBall := tau2180
  contactCenter := center2180
  contactBall := contact2180
  work := work2180
  center_sq := center_sq2180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2180.1
  jac_ok := checks2180.2.1
  accepted := checks2180.2.2

def tau2181 : RatBall :=
  ⟨⟨-17/320, 121/320⟩, 3/640⟩
def center2181 : GaussianRat :=
  ⟨-8630399/200000000, 275306779/1000000000⟩
def contact2181 : RatBall := localContactBall tau2181 center2181
def work2181 : RoundedTauEval :=
  evalTau precision tau2181 contact2181 logTwoBall

theorem center_sq2181 : (center2181.re : ℝ)^2 +
    (center2181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2181 : work2181.theta.ok = true ∧
    work2181.jac.invOK = true ∧ acceptsUnitSq work2181.out = true := by
  norm_num [work2181, contact2181, tau2181, center2181, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2181 : CellCertificate where
  tauBall := tau2181
  contactCenter := center2181
  contactBall := contact2181
  work := work2181
  center_sq := center_sq2181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2181.1
  jac_ok := checks2181.2.1
  accepted := checks2181.2.2

def tau2182 : RatBall :=
  ⟨⟨-3/64, 113/320⟩, 3/640⟩
def center2182 : GaussianRat :=
  ⟨-18633993/500000000, 15969023/62500000⟩
def contact2182 : RatBall := localContactBall tau2182 center2182
def work2182 : RoundedTauEval :=
  evalTau precision tau2182 contact2182 logTwoBall

theorem center_sq2182 : (center2182.re : ℝ)^2 +
    (center2182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2182 : work2182.theta.ok = true ∧
    work2182.jac.invOK = true ∧ acceptsUnitSq work2182.out = true := by
  norm_num [work2182, contact2182, tau2182, center2182, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2182 : CellCertificate where
  tauBall := tau2182
  contactCenter := center2182
  contactBall := contact2182
  work := work2182
  center_sq := center_sq2182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2182.1
  jac_ok := checks2182.2.1
  accepted := checks2182.2.2

def tau2183 : RatBall :=
  ⟨⟨-13/320, 113/320⟩, 3/640⟩
def center2183 : GaussianRat :=
  ⟨-32309979/1000000000, 127843073/500000000⟩
def contact2183 : RatBall := localContactBall tau2183 center2183
def work2183 : RoundedTauEval :=
  evalTau precision tau2183 contact2183 logTwoBall

theorem center_sq2183 : (center2183.re : ℝ)^2 +
    (center2183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2183 : work2183.theta.ok = true ∧
    work2183.jac.invOK = true ∧ acceptsUnitSq work2183.out = true := by
  norm_num [work2183, contact2183, tau2183, center2183, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2183 : CellCertificate where
  tauBall := tau2183
  contactCenter := center2183
  contactBall := contact2183
  work := work2183
  center_sq := center_sq2183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2183.1
  jac_ok := checks2183.2.1
  accepted := checks2183.2.2

def cells : List CellCertificate := [cell2176, cell2177, cell2178, cell2179, cell2180, cell2181, cell2182, cell2183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272
