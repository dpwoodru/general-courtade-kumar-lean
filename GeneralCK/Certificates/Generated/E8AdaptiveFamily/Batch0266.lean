import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2128 : RatBall :=
  ⟨⟨-33/320, 113/320⟩, 3/640⟩
def center2128 : GaussianRat :=
  ⟨-16312353/200000000, 252737367/1000000000⟩
def contact2128 : RatBall := localContactBall tau2128 center2128
def work2128 : RoundedTauEval :=
  evalTau precision tau2128 contact2128 logTwoBall

theorem center_sq2128 : (center2128.re : ℝ)^2 +
    (center2128.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2128]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2128 : work2128.theta.ok = true ∧
    work2128.jac.invOK = true ∧ acceptsUnitSq work2128.out = true := by
  norm_num [work2128, contact2128, tau2128, center2128, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2128 : CellCertificate where
  tauBall := tau2128
  contactCenter := center2128
  contactBall := contact2128
  work := work2128
  center_sq := center_sq2128
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2128.1
  jac_ok := checks2128.2.1
  accepted := checks2128.2.2

def tau2129 : RatBall :=
  ⟨⟨-7/64, 23/64⟩, 3/640⟩
def center2129 : GaussianRat :=
  ⟨-43440767/500000000, 257186633/1000000000⟩
def contact2129 : RatBall := localContactBall tau2129 center2129
def work2129 : RoundedTauEval :=
  evalTau precision tau2129 contact2129 logTwoBall

theorem center_sq2129 : (center2129.re : ℝ)^2 +
    (center2129.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2129]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2129 : work2129.theta.ok = true ∧
    work2129.jac.invOK = true ∧ acceptsUnitSq work2129.out = true := by
  norm_num [work2129, contact2129, tau2129, center2129, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2129 : CellCertificate where
  tauBall := tau2129
  contactCenter := center2129
  contactBall := contact2129
  work := work2129
  center_sq := center_sq2129
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2129.1
  jac_ok := checks2129.2.1
  accepted := checks2129.2.2

def tau2130 : RatBall :=
  ⟨⟨-33/320, 23/64⟩, 3/640⟩
def center2130 : GaussianRat :=
  ⟨-40992501/500000000, 257627847/1000000000⟩
def contact2130 : RatBall := localContactBall tau2130 center2130
def work2130 : RoundedTauEval :=
  evalTau precision tau2130 contact2130 logTwoBall

theorem center_sq2130 : (center2130.re : ℝ)^2 +
    (center2130.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2130]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2130 : work2130.theta.ok = true ∧
    work2130.jac.invOK = true ∧ acceptsUnitSq work2130.out = true := by
  norm_num [work2130, contact2130, tau2130, center2130, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2130 : CellCertificate where
  tauBall := tau2130
  contactCenter := center2130
  contactBall := contact2130
  work := work2130
  center_sq := center_sq2130
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2130.1
  jac_ok := checks2130.2.1
  accepted := checks2130.2.2

def tau2131 : RatBall :=
  ⟨⟨-39/320, 117/320⟩, 3/640⟩
def center2131 : GaussianRat :=
  ⟨-97144261/1000000000, 261108469/1000000000⟩
def contact2131 : RatBall := localContactBall tau2131 center2131
def work2131 : RoundedTauEval :=
  evalTau precision tau2131 contact2131 logTwoBall

theorem center_sq2131 : (center2131.re : ℝ)^2 +
    (center2131.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2131]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2131 : work2131.theta.ok = true ∧
    work2131.jac.invOK = true ∧ acceptsUnitSq work2131.out = true := by
  norm_num [work2131, contact2131, tau2131, center2131, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2131 : CellCertificate where
  tauBall := tau2131
  contactCenter := center2131
  contactBall := contact2131
  work := work2131
  center_sq := center_sq2131
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2131.1
  jac_ok := checks2131.2.1
  accepted := checks2131.2.2

def tau2132 : RatBall :=
  ⟨⟨-37/320, 117/320⟩, 3/640⟩
def center2132 : GaussianRat :=
  ⟨-46124689/500000000, 261610997/1000000000⟩
def contact2132 : RatBall := localContactBall tau2132 center2132
def work2132 : RoundedTauEval :=
  evalTau precision tau2132 contact2132 logTwoBall

theorem center_sq2132 : (center2132.re : ℝ)^2 +
    (center2132.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2132]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2132 : work2132.theta.ok = true ∧
    work2132.jac.invOK = true ∧ acceptsUnitSq work2132.out = true := by
  norm_num [work2132, contact2132, tau2132, center2132, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2132 : CellCertificate where
  tauBall := tau2132
  contactCenter := center2132
  contactBall := contact2132
  work := work2132
  center_sq := center_sq2132
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2132.1
  jac_ok := checks2132.2.1
  accepted := checks2132.2.2

def tau2133 : RatBall :=
  ⟨⟨-7/64, 117/320⟩, 3/640⟩
def center2133 : GaussianRat :=
  ⟨-43670547/500000000, 65522293/250000000⟩
def contact2133 : RatBall := localContactBall tau2133 center2133
def work2133 : RoundedTauEval :=
  evalTau precision tau2133 contact2133 logTwoBall

theorem center_sq2133 : (center2133.re : ℝ)^2 +
    (center2133.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2133]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2133 : work2133.theta.ok = true ∧
    work2133.jac.invOK = true ∧ acceptsUnitSq work2133.out = true := by
  norm_num [work2133, contact2133, tau2133, center2133, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2133 : CellCertificate where
  tauBall := tau2133
  contactCenter := center2133
  contactBall := contact2133
  work := work2133
  center_sq := center_sq2133
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2133.1
  jac_ok := checks2133.2.1
  accepted := checks2133.2.2

def tau2134 : RatBall :=
  ⟨⟨-33/320, 117/320⟩, 3/640⟩
def center2134 : GaussianRat :=
  ⟨-1648401/20000000, 65635667/250000000⟩
def contact2134 : RatBall := localContactBall tau2134 center2134
def work2134 : RoundedTauEval :=
  evalTau precision tau2134 contact2134 logTwoBall

theorem center_sq2134 : (center2134.re : ℝ)^2 +
    (center2134.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2134]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2134 : work2134.theta.ok = true ∧
    work2134.jac.invOK = true ∧ acceptsUnitSq work2134.out = true := by
  norm_num [work2134, contact2134, tau2134, center2134, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2134 : CellCertificate where
  tauBall := tau2134
  contactCenter := center2134
  contactBall := contact2134
  work := work2134
  center_sq := center_sq2134
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2134.1
  jac_ok := checks2134.2.1
  accepted := checks2134.2.2

def tau2135 : RatBall :=
  ⟨⟨-31/320, 109/320⟩, 3/640⟩
def center2135 : GaussianRat :=
  ⟨-75911827/1000000000, 121705269/500000000⟩
def contact2135 : RatBall := localContactBall tau2135 center2135
def work2135 : RoundedTauEval :=
  evalTau precision tau2135 contact2135 logTwoBall

theorem center_sq2135 : (center2135.re : ℝ)^2 +
    (center2135.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2135]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2135 : work2135.theta.ok = true ∧
    work2135.jac.invOK = true ∧ acceptsUnitSq work2135.out = true := by
  norm_num [work2135, contact2135, tau2135, center2135, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2135 : CellCertificate where
  tauBall := tau2135
  contactCenter := center2135
  contactBall := contact2135
  work := work2135
  center_sq := center_sq2135
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2135.1
  jac_ok := checks2135.2.1
  accepted := checks2135.2.2

def cells : List CellCertificate := [cell2128, cell2129, cell2130, cell2131, cell2132, cell2133, cell2134, cell2135]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266
