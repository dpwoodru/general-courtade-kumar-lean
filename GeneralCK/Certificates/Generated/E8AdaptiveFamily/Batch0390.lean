import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3120 : RatBall :=
  ⟨⟨19/128, -237/640⟩, 3/1280⟩
def center3120 : GaussianRat :=
  ⟨29562099/250000000, -262332709/1000000000⟩
def contact3120 : RatBall := localContactBall tau3120 center3120
def work3120 : RoundedTauEval :=
  evalTau precision tau3120 contact3120 logTwoBall

theorem center_sq3120 : (center3120.re : ℝ)^2 +
    (center3120.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3120]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3120 : work3120.theta.ok = true ∧
    work3120.jac.invOK = true ∧ acceptsUnitSq work3120.out = true := by
  norm_num [work3120, contact3120, tau3120, center3120, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3120 : CellCertificate where
  tauBall := tau3120
  contactCenter := center3120
  contactBall := contact3120
  work := work3120
  center_sq := center_sq3120
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3120.1
  jac_ok := checks3120.2.1
  accepted := checks3120.2.2

def tau3121 : RatBall :=
  ⟨⟨89/640, -47/128⟩, 3/1280⟩
def center3121 : GaussianRat :=
  ⟨110676327/1000000000, -2037627/7812500⟩
def contact3121 : RatBall := localContactBall tau3121 center3121
def work3121 : RoundedTauEval :=
  evalTau precision tau3121 contact3121 logTwoBall

theorem center_sq3121 : (center3121.re : ℝ)^2 +
    (center3121.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3121]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3121 : work3121.theta.ok = true ∧
    work3121.jac.invOK = true ∧ acceptsUnitSq work3121.out = true := by
  norm_num [work3121, contact3121, tau3121, center3121, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3121 : CellCertificate where
  tauBall := tau3121
  contactCenter := center3121
  contactBall := contact3121
  work := work3121
  center_sq := center_sq3121
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3121.1
  jac_ok := checks3121.2.1
  accepted := checks3121.2.2

def tau3122 : RatBall :=
  ⟨⟨91/640, -47/128⟩, 3/1280⟩
def center3122 : GaussianRat :=
  ⟨14137597/125000000, -260521763/1000000000⟩
def contact3122 : RatBall := localContactBall tau3122 center3122
def work3122 : RoundedTauEval :=
  evalTau precision tau3122 contact3122 logTwoBall

theorem center_sq3122 : (center3122.re : ℝ)^2 +
    (center3122.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3122]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3122 : work3122.theta.ok = true ∧
    work3122.jac.invOK = true ∧ acceptsUnitSq work3122.out = true := by
  norm_num [work3122, contact3122, tau3122, center3122, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3122 : CellCertificate where
  tauBall := tau3122
  contactCenter := center3122
  contactBall := contact3122
  work := work3122
  center_sq := center_sq3122
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3122.1
  jac_ok := checks3122.2.1
  accepted := checks3122.2.2

def tau3123 : RatBall :=
  ⟨⟨89/640, -233/640⟩, 3/1280⟩
def center3123 : GaussianRat :=
  ⟨22077337/200000000, -258392707/1000000000⟩
def contact3123 : RatBall := localContactBall tau3123 center3123
def work3123 : RoundedTauEval :=
  evalTau precision tau3123 contact3123 logTwoBall

theorem center_sq3123 : (center3123.re : ℝ)^2 +
    (center3123.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3123]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3123 : work3123.theta.ok = true ∧
    work3123.jac.invOK = true ∧ acceptsUnitSq work3123.out = true := by
  norm_num [work3123, contact3123, tau3123, center3123, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3123 : CellCertificate where
  tauBall := tau3123
  contactCenter := center3123
  contactBall := contact3123
  work := work3123
  center_sq := center_sq3123
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3123.1
  jac_ok := checks3123.2.1
  accepted := checks3123.2.2

def tau3124 : RatBall :=
  ⟨⟨91/640, -233/640⟩, 3/1280⟩
def center3124 : GaussianRat :=
  ⟨112805403/1000000000, -25810217/100000000⟩
def contact3124 : RatBall := localContactBall tau3124 center3124
def work3124 : RoundedTauEval :=
  evalTau precision tau3124 contact3124 logTwoBall

theorem center_sq3124 : (center3124.re : ℝ)^2 +
    (center3124.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3124]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3124 : work3124.theta.ok = true ∧
    work3124.jac.invOK = true ∧ acceptsUnitSq work3124.out = true := by
  norm_num [work3124, contact3124, tau3124, center3124, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3124 : CellCertificate where
  tauBall := tau3124
  contactCenter := center3124
  contactBall := contact3124
  work := work3124
  center_sq := center_sq3124
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3124.1
  jac_ok := checks3124.2.1
  accepted := checks3124.2.2

def tau3125 : RatBall :=
  ⟨⟨93/640, -47/128⟩, 3/1280⟩
def center3125 : GaussianRat :=
  ⟨115521207/1000000000, -32527691/125000000⟩
def contact3125 : RatBall := localContactBall tau3125 center3125
def work3125 : RoundedTauEval :=
  evalTau precision tau3125 contact3125 logTwoBall

theorem center_sq3125 : (center3125.re : ℝ)^2 +
    (center3125.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3125]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3125 : work3125.theta.ok = true ∧
    work3125.jac.invOK = true ∧ acceptsUnitSq work3125.out = true := by
  norm_num [work3125, contact3125, tau3125, center3125, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3125 : CellCertificate where
  tauBall := tau3125
  contactCenter := center3125
  contactBall := contact3125
  work := work3125
  center_sq := center_sq3125
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3125.1
  jac_ok := checks3125.2.1
  accepted := checks3125.2.2

def tau3126 : RatBall :=
  ⟨⟨19/128, -47/128⟩, 3/1280⟩
def center3126 : GaussianRat :=
  ⟨117937551/1000000000, -649789/2500000⟩
def contact3126 : RatBall := localContactBall tau3126 center3126
def work3126 : RoundedTauEval :=
  evalTau precision tau3126 contact3126 logTwoBall

theorem center_sq3126 : (center3126.re : ℝ)^2 +
    (center3126.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3126]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3126 : work3126.theta.ok = true ∧
    work3126.jac.invOK = true ∧ acceptsUnitSq work3126.out = true := by
  norm_num [work3126, contact3126, tau3126, center3126, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3126 : CellCertificate where
  tauBall := tau3126
  contactCenter := center3126
  contactBall := contact3126
  work := work3126
  center_sq := center_sq3126
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3126.1
  jac_ok := checks3126.2.1
  accepted := checks3126.2.2

def tau3127 : RatBall :=
  ⟨⟨93/640, -233/640⟩, 3/1280⟩
def center3127 : GaussianRat :=
  ⟨115220153/1000000000, -257805963/1000000000⟩
def contact3127 : RatBall := localContactBall tau3127 center3127
def work3127 : RoundedTauEval :=
  evalTau precision tau3127 contact3127 logTwoBall

theorem center_sq3127 : (center3127.re : ℝ)^2 +
    (center3127.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3127 : work3127.theta.ok = true ∧
    work3127.jac.invOK = true ∧ acceptsUnitSq work3127.out = true := by
  norm_num [work3127, contact3127, tau3127, center3127, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3127 : CellCertificate where
  tauBall := tau3127
  contactCenter := center3127
  contactBall := contact3127
  work := work3127
  center_sq := center_sq3127
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3127.1
  jac_ok := checks3127.2.1
  accepted := checks3127.2.2

def cells : List CellCertificate := [cell3120, cell3121, cell3122, cell3123, cell3124, cell3125, cell3126, cell3127]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390
