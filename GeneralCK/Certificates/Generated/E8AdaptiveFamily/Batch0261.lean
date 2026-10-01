import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2088 : RatBall :=
  ⟨⟨-9/64, 107/320⟩, 3/640⟩
def center2088 : GaussianRat :=
  ⟨-109007417/1000000000, 235517221/1000000000⟩
def contact2088 : RatBall := localContactBall tau2088 center2088
def work2088 : RoundedTauEval :=
  evalTau precision tau2088 contact2088 logTwoBall

theorem center_sq2088 : (center2088.re : ℝ)^2 +
    (center2088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2088 : work2088.theta.ok = true ∧
    work2088.jac.invOK = true ∧ acceptsUnitSq work2088.out = true := by
  norm_num [work2088, contact2088, tau2088, center2088, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2088 : CellCertificate where
  tauBall := tau2088
  contactCenter := center2088
  contactBall := contact2088
  work := work2088
  center_sq := center_sq2088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2088.1
  jac_ok := checks2088.2.1
  accepted := checks2088.2.2

def tau2089 : RatBall :=
  ⟨⟨-43/320, 21/64⟩, 3/640⟩
def center2089 : GaussianRat :=
  ⟨-103781603/1000000000, 28909781/125000000⟩
def contact2089 : RatBall := localContactBall tau2089 center2089
def work2089 : RoundedTauEval :=
  evalTau precision tau2089 contact2089 logTwoBall

theorem center_sq2089 : (center2089.re : ℝ)^2 +
    (center2089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2089 : work2089.theta.ok = true ∧
    work2089.jac.invOK = true ∧ acceptsUnitSq work2089.out = true := by
  norm_num [work2089, contact2089, tau2089, center2089, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2089 : CellCertificate where
  tauBall := tau2089
  contactCenter := center2089
  contactBall := contact2089
  work := work2089
  center_sq := center_sq2089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2089.1
  jac_ok := checks2089.2.1
  accepted := checks2089.2.2

def tau2090 : RatBall :=
  ⟨⟨-41/320, 21/64⟩, 3/640⟩
def center2090 : GaussianRat :=
  ⟨-12380739/125000000, 115872433/500000000⟩
def contact2090 : RatBall := localContactBall tau2090 center2090
def work2090 : RoundedTauEval :=
  evalTau precision tau2090 contact2090 logTwoBall

theorem center_sq2090 : (center2090.re : ℝ)^2 +
    (center2090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2090 : work2090.theta.ok = true ∧
    work2090.jac.invOK = true ∧ acceptsUnitSq work2090.out = true := by
  norm_num [work2090, contact2090, tau2090, center2090, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2090 : CellCertificate where
  tauBall := tau2090
  contactCenter := center2090
  contactBall := contact2090
  work := work2090
  center_sq := center_sq2090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2090.1
  jac_ok := checks2090.2.1
  accepted := checks2090.2.2

def tau2091 : RatBall :=
  ⟨⟨-43/320, 107/320⟩, 3/640⟩
def center2091 : GaussianRat :=
  ⟨-104264923/1000000000, 236017459/1000000000⟩
def contact2091 : RatBall := localContactBall tau2091 center2091
def work2091 : RoundedTauEval :=
  evalTau precision tau2091 contact2091 logTwoBall

theorem center_sq2091 : (center2091.re : ℝ)^2 +
    (center2091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2091 : work2091.theta.ok = true ∧
    work2091.jac.invOK = true ∧ acceptsUnitSq work2091.out = true := by
  norm_num [work2091, contact2091, tau2091, center2091, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2091 : CellCertificate where
  tauBall := tau2091
  contactCenter := center2091
  contactBall := contact2091
  work := work2091
  center_sq := center_sq2091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2091.1
  jac_ok := checks2091.2.1
  accepted := checks2091.2.2

def tau2092 : RatBall :=
  ⟨⟨-41/320, 107/320⟩, 3/640⟩
def center2092 : GaussianRat :=
  ⟨-99508871/1000000000, 236497219/1000000000⟩
def contact2092 : RatBall := localContactBall tau2092 center2092
def work2092 : RoundedTauEval :=
  evalTau precision tau2092 contact2092 logTwoBall

theorem center_sq2092 : (center2092.re : ℝ)^2 +
    (center2092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2092 : work2092.theta.ok = true ∧
    work2092.jac.invOK = true ∧ acceptsUnitSq work2092.out = true := by
  norm_num [work2092, contact2092, tau2092, center2092, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2092 : CellCertificate where
  tauBall := tau2092
  contactCenter := center2092
  contactBall := contact2092
  work := work2092
  center_sq := center_sq2092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2092.1
  jac_ok := checks2092.2.1
  accepted := checks2092.2.2

def tau2093 : RatBall :=
  ⟨⟨-47/320, 109/320⟩, 3/640⟩
def center2093 : GaussianRat :=
  ⟨-3571049/31250000, 239728011/1000000000⟩
def contact2093 : RatBall := localContactBall tau2093 center2093
def work2093 : RoundedTauEval :=
  evalTau precision tau2093 contact2093 logTwoBall

theorem center_sq2093 : (center2093.re : ℝ)^2 +
    (center2093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2093]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2093 : work2093.theta.ok = true ∧
    work2093.jac.invOK = true ∧ acceptsUnitSq work2093.out = true := by
  norm_num [work2093, contact2093, tau2093, center2093, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2093 : CellCertificate where
  tauBall := tau2093
  contactCenter := center2093
  contactBall := contact2093
  work := work2093
  center_sq := center_sq2093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2093.1
  jac_ok := checks2093.2.1
  accepted := checks2093.2.2

def tau2094 : RatBall :=
  ⟨⟨-9/64, 109/320⟩, 3/640⟩
def center2094 : GaussianRat :=
  ⟨-109524891/1000000000, 240262931/1000000000⟩
def contact2094 : RatBall := localContactBall tau2094 center2094
def work2094 : RoundedTauEval :=
  evalTau precision tau2094 contact2094 logTwoBall

theorem center_sq2094 : (center2094.re : ℝ)^2 +
    (center2094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2094]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2094 : work2094.theta.ok = true ∧
    work2094.jac.invOK = true ∧ acceptsUnitSq work2094.out = true := by
  norm_num [work2094, contact2094, tau2094, center2094, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2094 : CellCertificate where
  tauBall := tau2094
  contactCenter := center2094
  contactBall := contact2094
  work := work2094
  center_sq := center_sq2094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2094.1
  jac_ok := checks2094.2.1
  accepted := checks2094.2.2

def tau2095 : RatBall :=
  ⟨⟨-47/320, 111/320⟩, 3/640⟩
def center2095 : GaussianRat :=
  ⟨-57413127/500000000, 244479579/1000000000⟩
def contact2095 : RatBall := localContactBall tau2095 center2095
def work2095 : RoundedTauEval :=
  evalTau precision tau2095 contact2095 logTwoBall

theorem center_sq2095 : (center2095.re : ℝ)^2 +
    (center2095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2095 : work2095.theta.ok = true ∧
    work2095.jac.invOK = true ∧ acceptsUnitSq work2095.out = true := by
  norm_num [work2095, contact2095, tau2095, center2095, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2095 : CellCertificate where
  tauBall := tau2095
  contactCenter := center2095
  contactBall := contact2095
  work := work2095
  center_sq := center_sq2095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2095.1
  jac_ok := checks2095.2.1
  accepted := checks2095.2.2

def cells : List CellCertificate := [cell2088, cell2089, cell2090, cell2091, cell2092, cell2093, cell2094, cell2095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261
