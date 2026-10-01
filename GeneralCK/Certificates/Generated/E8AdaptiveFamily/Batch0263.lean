import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2104 : RatBall :=
  ⟨⟨-37/320, 107/320⟩, 3/640⟩
def center2104 : GaussianRat :=
  ⟨-22489569/250000000, 47478823/200000000⟩
def contact2104 : RatBall := localContactBall tau2104 center2104
def work2104 : RoundedTauEval :=
  evalTau precision tau2104 contact2104 logTwoBall

theorem center_sq2104 : (center2104.re : ℝ)^2 +
    (center2104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2104 : work2104.theta.ok = true ∧
    work2104.jac.invOK = true ∧ acceptsUnitSq work2104.out = true := by
  norm_num [work2104, contact2104, tau2104, center2104, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2104 : CellCertificate where
  tauBall := tau2104
  contactCenter := center2104
  contactBall := contact2104
  work := work2104
  center_sq := center_sq2104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2104.1
  jac_ok := checks2104.2.1
  accepted := checks2104.2.2

def tau2105 : RatBall :=
  ⟨⟨-39/320, 109/320⟩, 3/640⟩
def center2105 : GaussianRat :=
  ⟨-47597289/500000000, 241742219/1000000000⟩
def contact2105 : RatBall := localContactBall tau2105 center2105
def work2105 : RoundedTauEval :=
  evalTau precision tau2105 contact2105 logTwoBall

theorem center_sq2105 : (center2105.re : ℝ)^2 +
    (center2105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2105 : work2105.theta.ok = true ∧
    work2105.jac.invOK = true ∧ acceptsUnitSq work2105.out = true := by
  norm_num [work2105, contact2105, tau2105, center2105, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2105 : CellCertificate where
  tauBall := tau2105
  contactCenter := center2105
  contactBall := contact2105
  work := work2105
  center_sq := center_sq2105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2105.1
  jac_ok := checks2105.2.1
  accepted := checks2105.2.2

def tau2106 : RatBall :=
  ⟨⟨-37/320, 109/320⟩, 3/640⟩
def center2106 : GaussianRat :=
  ⟨-45195779/500000000, 121096227/500000000⟩
def contact2106 : RatBall := localContactBall tau2106 center2106
def work2106 : RoundedTauEval :=
  evalTau precision tau2106 contact2106 logTwoBall

theorem center_sq2106 : (center2106.re : ℝ)^2 +
    (center2106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2106 : work2106.theta.ok = true ∧
    work2106.jac.invOK = true ∧ acceptsUnitSq work2106.out = true := by
  norm_num [work2106, contact2106, tau2106, center2106, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2106 : CellCertificate where
  tauBall := tau2106
  contactCenter := center2106
  contactBall := contact2106
  work := work2106
  center_sq := center_sq2106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2106.1
  jac_ok := checks2106.2.1
  accepted := checks2106.2.2

def tau2107 : RatBall :=
  ⟨⟨-39/320, 111/320⟩, 3/640⟩
def center2107 : GaussianRat :=
  ⟨-11957763/125000000, 15409367/62500000⟩
def contact2107 : RatBall := localContactBall tau2107 center2107
def work2107 : RoundedTauEval :=
  evalTau precision tau2107 contact2107 logTwoBall

theorem center_sq2107 : (center2107.re : ℝ)^2 +
    (center2107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2107 : work2107.theta.ok = true ∧
    work2107.jac.invOK = true ∧ acceptsUnitSq work2107.out = true := by
  norm_num [work2107, contact2107, tau2107, center2107, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2107 : CellCertificate where
  tauBall := tau2107
  contactCenter := center2107
  contactBall := contact2107
  work := work2107
  center_sq := center_sq2107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2107.1
  jac_ok := checks2107.2.1
  accepted := checks2107.2.2

def tau2108 : RatBall :=
  ⟨⟨-37/320, 111/320⟩, 3/640⟩
def center2108 : GaussianRat :=
  ⟨-45418507/500000000, 247012717/1000000000⟩
def contact2108 : RatBall := localContactBall tau2108 center2108
def work2108 : RoundedTauEval :=
  evalTau precision tau2108 contact2108 logTwoBall

theorem center_sq2108 : (center2108.re : ℝ)^2 +
    (center2108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2108 : work2108.theta.ok = true ∧
    work2108.jac.invOK = true ∧ acceptsUnitSq work2108.out = true := by
  norm_num [work2108, contact2108, tau2108, center2108, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2108 : CellCertificate where
  tauBall := tau2108
  contactCenter := center2108
  contactBall := contact2108
  work := work2108
  center_sq := center_sq2108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2108.1
  jac_ok := checks2108.2.1
  accepted := checks2108.2.2

def tau2109 : RatBall :=
  ⟨⟨-7/64, 109/320⟩, 3/640⟩
def center2109 : GaussianRat :=
  ⟨-17115273/200000000, 242620769/1000000000⟩
def contact2109 : RatBall := localContactBall tau2109 center2109
def work2109 : RoundedTauEval :=
  evalTau precision tau2109 contact2109 logTwoBall

theorem center_sq2109 : (center2109.re : ℝ)^2 +
    (center2109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2109 : work2109.theta.ok = true ∧
    work2109.jac.invOK = true ∧ acceptsUnitSq work2109.out = true := by
  norm_num [work2109, contact2109, tau2109, center2109, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2109 : CellCertificate where
  tauBall := tau2109
  contactCenter := center2109
  contactBall := contact2109
  work := work2109
  center_sq := center_sq2109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2109.1
  jac_ok := checks2109.2.1
  accepted := checks2109.2.2

def tau2110 : RatBall :=
  ⟨⟨-33/320, 109/320⟩, 3/640⟩
def center2110 : GaussianRat :=
  ⟨-20187397/250000000, 48605377/200000000⟩
def contact2110 : RatBall := localContactBall tau2110 center2110
def work2110 : RoundedTauEval :=
  evalTau precision tau2110 contact2110 logTwoBall

theorem center_sq2110 : (center2110.re : ℝ)^2 +
    (center2110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2110 : work2110.theta.ok = true ∧
    work2110.jac.invOK = true ∧ acceptsUnitSq work2110.out = true := by
  norm_num [work2110, contact2110, tau2110, center2110, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2110 : CellCertificate where
  tauBall := tau2110
  contactCenter := center2110
  contactBall := contact2110
  work := work2110
  center_sq := center_sq2110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2110.1
  jac_ok := checks2110.2.1
  accepted := checks2110.2.2

def tau2111 : RatBall :=
  ⟨⟨-7/64, 111/320⟩, 3/640⟩
def center2111 : GaussianRat :=
  ⟨-85999463/1000000000, 247453051/1000000000⟩
def contact2111 : RatBall := localContactBall tau2111 center2111
def work2111 : RoundedTauEval :=
  evalTau precision tau2111 contact2111 logTwoBall

theorem center_sq2111 : (center2111.re : ℝ)^2 +
    (center2111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2111 : work2111.theta.ok = true ∧
    work2111.jac.invOK = true ∧ acceptsUnitSq work2111.out = true := by
  norm_num [work2111, contact2111, tau2111, center2111, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2111 : CellCertificate where
  tauBall := tau2111
  contactCenter := center2111
  contactBall := contact2111
  work := work2111
  center_sq := center_sq2111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2111.1
  jac_ok := checks2111.2.1
  accepted := checks2111.2.2

def cells : List CellCertificate := [cell2104, cell2105, cell2106, cell2107, cell2108, cell2109, cell2110, cell2111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263
