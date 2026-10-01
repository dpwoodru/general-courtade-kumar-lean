import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3184 : RatBall :=
  ⟨⟨123/640, -221/640⟩, 3/1280⟩
def center3184 : GaussianRat :=
  ⟨29748323/200000000, -119366383/500000000⟩
def contact3184 : RatBall := localContactBall tau3184 center3184
def work3184 : RoundedTauEval :=
  evalTau precision tau3184 contact3184 logTwoBall

theorem center_sq3184 : (center3184.re : ℝ)^2 +
    (center3184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3184 : work3184.theta.ok = true ∧
    work3184.jac.invOK = true ∧ acceptsUnitSq work3184.out = true := by
  norm_num [work3184, contact3184, tau3184, center3184, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3184 : CellCertificate where
  tauBall := tau3184
  contactCenter := center3184
  contactBall := contact3184
  work := work3184
  center_sq := center_sq3184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3184.1
  jac_ok := checks3184.2.1
  accepted := checks3184.2.2

def tau3185 : RatBall :=
  ⟨⟨25/128, -223/640⟩, 3/1280⟩
def center3185 : GaussianRat :=
  ⟨151411581/1000000000, -120348091/500000000⟩
def contact3185 : RatBall := localContactBall tau3185 center3185
def work3185 : RoundedTauEval :=
  evalTau precision tau3185 contact3185 logTwoBall

theorem center_sq3185 : (center3185.re : ℝ)^2 +
    (center3185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3185 : work3185.theta.ok = true ∧
    work3185.jac.invOK = true ∧ acceptsUnitSq work3185.out = true := by
  norm_num [work3185, contact3185, tau3185, center3185, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3185 : CellCertificate where
  tauBall := tau3185
  contactCenter := center3185
  contactBall := contact3185
  work := work3185
  center_sq := center_sq3185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3185.1
  jac_ok := checks3185.2.1
  accepted := checks3185.2.2

def tau3186 : RatBall :=
  ⟨⟨127/640, -223/640⟩, 3/1280⟩
def center3186 : GaussianRat :=
  ⟨153725769/1000000000, -120168019/500000000⟩
def contact3186 : RatBall := localContactBall tau3186 center3186
def work3186 : RoundedTauEval :=
  evalTau precision tau3186 contact3186 logTwoBall

theorem center_sq3186 : (center3186.re : ℝ)^2 +
    (center3186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3186 : work3186.theta.ok = true ∧
    work3186.jac.invOK = true ∧ acceptsUnitSq work3186.out = true := by
  norm_num [work3186, contact3186, tau3186, center3186, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3186 : CellCertificate where
  tauBall := tau3186
  contactCenter := center3186
  contactBall := contact3186
  work := work3186
  center_sq := center_sq3186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3186.1
  jac_ok := checks3186.2.1
  accepted := checks3186.2.2

def tau3187 : RatBall :=
  ⟨⟨25/128, -221/640⟩, 3/1280⟩
def center3187 : GaussianRat :=
  ⟨151056059/1000000000, -238381849/1000000000⟩
def contact3187 : RatBall := localContactBall tau3187 center3187
def work3187 : RoundedTauEval :=
  evalTau precision tau3187 contact3187 logTwoBall

theorem center_sq3187 : (center3187.re : ℝ)^2 +
    (center3187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3187 : work3187.theta.ok = true ∧
    work3187.jac.invOK = true ∧ acceptsUnitSq work3187.out = true := by
  norm_num [work3187, contact3187, tau3187, center3187, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3187 : CellCertificate where
  tauBall := tau3187
  contactCenter := center3187
  contactBall := contact3187
  work := work3187
  center_sq := center_sq3187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3187.1
  jac_ok := checks3187.2.1
  accepted := checks3187.2.2

def tau3188 : RatBall :=
  ⟨⟨127/640, -221/640⟩, 3/1280⟩
def center3188 : GaussianRat :=
  ⟨38341447/250000000, -29753309/125000000⟩
def contact3188 : RatBall := localContactBall tau3188 center3188
def work3188 : RoundedTauEval :=
  evalTau precision tau3188 contact3188 logTwoBall

theorem center_sq3188 : (center3188.re : ℝ)^2 +
    (center3188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3188 : work3188.theta.ok = true ∧
    work3188.jac.invOK = true ∧ acceptsUnitSq work3188.out = true := by
  norm_num [work3188, contact3188, tau3188, center3188, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3188 : CellCertificate where
  tauBall := tau3188
  contactCenter := center3188
  contactBall := contact3188
  work := work3188
  center_sq := center_sq3188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3188.1
  jac_ok := checks3188.2.1
  accepted := checks3188.2.2

def tau3189 : RatBall :=
  ⟨⟨129/640, -221/640⟩, 3/1280⟩
def center3189 : GaussianRat :=
  ⟨155670749/1000000000, -118833343/500000000⟩
def contact3189 : RatBall := localContactBall tau3189 center3189
def work3189 : RoundedTauEval :=
  evalTau precision tau3189 contact3189 logTwoBall

theorem center_sq3189 : (center3189.re : ℝ)^2 +
    (center3189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3189 : work3189.theta.ok = true ∧
    work3189.jac.invOK = true ∧ acceptsUnitSq work3189.out = true := by
  norm_num [work3189, contact3189, tau3189, center3189, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3189 : CellCertificate where
  tauBall := tau3189
  contactCenter := center3189
  contactBall := contact3189
  work := work3189
  center_sq := center_sq3189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3189.1
  jac_ok := checks3189.2.1
  accepted := checks3189.2.2

def tau3190 : RatBall :=
  ⟨⟨131/640, -221/640⟩, 3/1280⟩
def center3190 : GaussianRat :=
  ⟨157970893/1000000000, -237302543/1000000000⟩
def contact3190 : RatBall := localContactBall tau3190 center3190
def work3190 : RoundedTauEval :=
  evalTau precision tau3190 contact3190 logTwoBall

theorem center_sq3190 : (center3190.re : ℝ)^2 +
    (center3190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3190 : work3190.theta.ok = true ∧
    work3190.jac.invOK = true ∧ acceptsUnitSq work3190.out = true := by
  norm_num [work3190, contact3190, tau3190, center3190, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3190 : CellCertificate where
  tauBall := tau3190
  contactCenter := center3190
  contactBall := contact3190
  work := work3190
  center_sq := center_sq3190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3190.1
  jac_ok := checks3190.2.1
  accepted := checks3190.2.2

def tau3191 : RatBall :=
  ⟨⟨129/640, -219/640⟩, 3/1280⟩
def center3191 : GaussianRat :=
  ⟨155311177/1000000000, -29420787/125000000⟩
def contact3191 : RatBall := localContactBall tau3191 center3191
def work3191 : RoundedTauEval :=
  evalTau precision tau3191 contact3191 logTwoBall

theorem center_sq3191 : (center3191.re : ℝ)^2 +
    (center3191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3191 : work3191.theta.ok = true ∧
    work3191.jac.invOK = true ∧ acceptsUnitSq work3191.out = true := by
  norm_num [work3191, contact3191, tau3191, center3191, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3191 : CellCertificate where
  tauBall := tau3191
  contactCenter := center3191
  contactBall := contact3191
  work := work3191
  center_sq := center_sq3191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3191.1
  jac_ok := checks3191.2.1
  accepted := checks3191.2.2

def cells : List CellCertificate := [cell3184, cell3185, cell3186, cell3187, cell3188, cell3189, cell3190, cell3191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398
