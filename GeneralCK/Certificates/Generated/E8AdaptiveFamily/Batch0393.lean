import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0393

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3144 : RatBall :=
  ⟨⟨107/640, -233/640⟩, 3/1280⟩
def center3144 : GaussianRat :=
  ⟨132006469/1000000000, -255577867/1000000000⟩
def contact3144 : RatBall := localContactBall tau3144 center3144
def work3144 : RoundedTauEval :=
  evalTau precision tau3144 contact3144 logTwoBall

theorem center_sq3144 : (center3144.re : ℝ)^2 +
    (center3144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3144 : work3144.theta.ok = true ∧
    work3144.jac.invOK = true ∧ acceptsUnitSq work3144.out = true := by
  norm_num [work3144, contact3144, tau3144, center3144, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3144 : CellCertificate where
  tauBall := tau3144
  contactCenter := center3144
  contactBall := contact3144
  work := work3144
  center_sq := center_sq3144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3144.1
  jac_ok := checks3144.2.1
  accepted := checks3144.2.2

def tau3145 : RatBall :=
  ⟨⟨109/640, -233/640⟩, 3/1280⟩
def center3145 : GaussianRat :=
  ⟨134387007/1000000000, -127619041/500000000⟩
def contact3145 : RatBall := localContactBall tau3145 center3145
def work3145 : RoundedTauEval :=
  evalTau precision tau3145 contact3145 logTwoBall

theorem center_sq3145 : (center3145.re : ℝ)^2 +
    (center3145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3145 : work3145.theta.ok = true ∧
    work3145.jac.invOK = true ∧ acceptsUnitSq work3145.out = true := by
  norm_num [work3145, contact3145, tau3145, center3145, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3145 : CellCertificate where
  tauBall := tau3145
  contactCenter := center3145
  contactBall := contact3145
  work := work3145
  center_sq := center_sq3145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3145.1
  jac_ok := checks3145.2.1
  accepted := checks3145.2.2

def tau3146 : RatBall :=
  ⟨⟨97/640, -231/640⟩, 3/1280⟩
def center3146 : GaussianRat :=
  ⟨59864687/500000000, -254794957/1000000000⟩
def contact3146 : RatBall := localContactBall tau3146 center3146
def work3146 : RoundedTauEval :=
  evalTau precision tau3146 contact3146 logTwoBall

theorem center_sq3146 : (center3146.re : ℝ)^2 +
    (center3146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3146 : work3146.theta.ok = true ∧
    work3146.jac.invOK = true ∧ acceptsUnitSq work3146.out = true := by
  norm_num [work3146, contact3146, tau3146, center3146, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3146 : CellCertificate where
  tauBall := tau3146
  contactCenter := center3146
  contactBall := contact3146
  work := work3146
  center_sq := center_sq3146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3146.1
  jac_ok := checks3146.2.1
  accepted := checks3146.2.2

def tau3147 : RatBall :=
  ⟨⟨99/640, -231/640⟩, 3/1280⟩
def center3147 : GaussianRat :=
  ⟨122126333/1000000000, -127243109/500000000⟩
def contact3147 : RatBall := localContactBall tau3147 center3147
def work3147 : RoundedTauEval :=
  evalTau precision tau3147 contact3147 logTwoBall

theorem center_sq3147 : (center3147.re : ℝ)^2 +
    (center3147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3147 : work3147.theta.ok = true ∧
    work3147.jac.invOK = true ∧ acceptsUnitSq work3147.out = true := by
  norm_num [work3147, contact3147, tau3147, center3147, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3147 : CellCertificate where
  tauBall := tau3147
  contactCenter := center3147
  contactBall := contact3147
  work := work3147
  center_sq := center_sq3147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3147.1
  jac_ok := checks3147.2.1
  accepted := checks3147.2.2

def tau3148 : RatBall :=
  ⟨⟨97/640, -229/640⟩, 3/1280⟩
def center3148 : GaussianRat :=
  ⟨119425411/1000000000, -252398639/1000000000⟩
def contact3148 : RatBall := localContactBall tau3148 center3148
def work3148 : RoundedTauEval :=
  evalTau precision tau3148 contact3148 logTwoBall

theorem center_sq3148 : (center3148.re : ℝ)^2 +
    (center3148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3148 : work3148.theta.ok = true ∧
    work3148.jac.invOK = true ∧ acceptsUnitSq work3148.out = true := by
  norm_num [work3148, contact3148, tau3148, center3148, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3148 : CellCertificate where
  tauBall := tau3148
  contactCenter := center3148
  contactBall := contact3148
  work := work3148
  center_sq := center_sq3148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3148.1
  jac_ok := checks3148.2.1
  accepted := checks3148.2.2

def tau3149 : RatBall :=
  ⟨⟨99/640, -229/640⟩, 3/1280⟩
def center3149 : GaussianRat :=
  ⟨30454243/250000000, -126047019/500000000⟩
def contact3149 : RatBall := localContactBall tau3149 center3149
def work3149 : RoundedTauEval :=
  evalTau precision tau3149 contact3149 logTwoBall

theorem center_sq3149 : (center3149.re : ℝ)^2 +
    (center3149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3149 : work3149.theta.ok = true ∧
    work3149.jac.invOK = true ∧ acceptsUnitSq work3149.out = true := by
  norm_num [work3149, contact3149, tau3149, center3149, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3149 : CellCertificate where
  tauBall := tau3149
  contactCenter := center3149
  contactBall := contact3149
  work := work3149
  center_sq := center_sq3149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3149.1
  jac_ok := checks3149.2.1
  accepted := checks3149.2.2

def tau3150 : RatBall :=
  ⟨⟨101/640, -231/640⟩, 3/1280⟩
def center3150 : GaussianRat :=
  ⟨15564887/125000000, -254172071/1000000000⟩
def contact3150 : RatBall := localContactBall tau3150 center3150
def work3150 : RoundedTauEval :=
  evalTau precision tau3150 contact3150 logTwoBall

theorem center_sq3150 : (center3150.re : ℝ)^2 +
    (center3150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3150 : work3150.theta.ok = true ∧
    work3150.jac.invOK = true ∧ acceptsUnitSq work3150.out = true := by
  norm_num [work3150, contact3150, tau3150, center3150, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3150 : CellCertificate where
  tauBall := tau3150
  contactCenter := center3150
  contactBall := contact3150
  work := work3150
  center_sq := center_sq3150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3150.1
  jac_ok := checks3150.2.1
  accepted := checks3150.2.2

def tau3151 : RatBall :=
  ⟨⟨103/640, -231/640⟩, 3/1280⟩
def center3151 : GaussianRat :=
  ⟨63453799/500000000, -253852567/1000000000⟩
def contact3151 : RatBall := localContactBall tau3151 center3151
def work3151 : RoundedTauEval :=
  evalTau precision tau3151 contact3151 logTwoBall

theorem center_sq3151 : (center3151.re : ℝ)^2 +
    (center3151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3151 : work3151.theta.ok = true ∧
    work3151.jac.invOK = true ∧ acceptsUnitSq work3151.out = true := by
  norm_num [work3151, contact3151, tau3151, center3151, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3151 : CellCertificate where
  tauBall := tau3151
  contactCenter := center3151
  contactBall := contact3151
  work := work3151
  center_sq := center_sq3151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3151.1
  jac_ok := checks3151.2.1
  accepted := checks3151.2.2

def cells : List CellCertificate := [cell3144, cell3145, cell3146, cell3147, cell3148, cell3149, cell3150, cell3151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0393
