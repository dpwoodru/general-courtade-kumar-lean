import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0451

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3608 : RatBall :=
  ⟨⟨9/128, 241/640⟩, 3/1280⟩
def center3608 : GaussianRat :=
  ⟨11390081/200000000, 136632679/500000000⟩
def contact3608 : RatBall := localContactBall tau3608 center3608
def work3608 : RoundedTauEval :=
  evalTau precision tau3608 contact3608 logTwoBall

theorem center_sq3608 : (center3608.re : ℝ)^2 +
    (center3608.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3608]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3608 : work3608.theta.ok = true ∧
    work3608.jac.invOK = true ∧ acceptsUnitSq work3608.out = true := by
  norm_num [work3608, contact3608, tau3608, center3608, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3608 : CellCertificate where
  tauBall := tau3608
  contactCenter := center3608
  contactBall := contact3608
  work := work3608
  center_sq := center_sq3608
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3608.1
  jac_ok := checks3608.2.1
  accepted := checks3608.2.2

def tau3609 : RatBall :=
  ⟨⟨47/640, 241/640⟩, 3/1280⟩
def center3609 : GaussianRat :=
  ⟨59463601/1000000000, 273101301/1000000000⟩
def contact3609 : RatBall := localContactBall tau3609 center3609
def work3609 : RoundedTauEval :=
  evalTau precision tau3609 contact3609 logTwoBall

theorem center_sq3609 : (center3609.re : ℝ)^2 +
    (center3609.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3609]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3609 : work3609.theta.ok = true ∧
    work3609.jac.invOK = true ∧ acceptsUnitSq work3609.out = true := by
  norm_num [work3609, contact3609, tau3609, center3609, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3609 : CellCertificate where
  tauBall := tau3609
  contactCenter := center3609
  contactBall := contact3609
  work := work3609
  center_sq := center_sq3609
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3609.1
  jac_ok := checks3609.2.1
  accepted := checks3609.2.2

def tau3610 : RatBall :=
  ⟨⟨9/128, 243/640⟩, 3/1280⟩
def center3610 : GaussianRat :=
  ⟨456897/8000000, 17236447/62500000⟩
def contact3610 : RatBall := localContactBall tau3610 center3610
def work3610 : RoundedTauEval :=
  evalTau precision tau3610 contact3610 logTwoBall

theorem center_sq3610 : (center3610.re : ℝ)^2 +
    (center3610.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3610]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3610 : work3610.theta.ok = true ∧
    work3610.jac.invOK = true ∧ acceptsUnitSq work3610.out = true := by
  norm_num [work3610, contact3610, tau3610, center3610, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3610 : CellCertificate where
  tauBall := tau3610
  contactCenter := center3610
  contactBall := contact3610
  work := work3610
  center_sq := center_sq3610
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3610.1
  jac_ok := checks3610.2.1
  accepted := checks3610.2.2

def tau3611 : RatBall :=
  ⟨⟨47/640, 243/640⟩, 3/1280⟩
def center3611 : GaussianRat :=
  ⟨59632267/1000000000, 137808407/500000000⟩
def contact3611 : RatBall := localContactBall tau3611 center3611
def work3611 : RoundedTauEval :=
  evalTau precision tau3611 contact3611 logTwoBall

theorem center_sq3611 : (center3611.re : ℝ)^2 +
    (center3611.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3611]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3611 : work3611.theta.ok = true ∧
    work3611.jac.invOK = true ∧ acceptsUnitSq work3611.out = true := by
  norm_num [work3611, contact3611, tau3611, center3611, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3611 : CellCertificate where
  tauBall := tau3611
  contactCenter := center3611
  contactBall := contact3611
  work := work3611
  center_sq := center_sq3611
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3611.1
  jac_ok := checks3611.2.1
  accepted := checks3611.2.2

def tau3612 : RatBall :=
  ⟨⟨41/640, 49/128⟩, 3/1280⟩
def center3612 : GaussianRat :=
  ⟨13053747/250000000, 34827989/125000000⟩
def contact3612 : RatBall := localContactBall tau3612 center3612
def work3612 : RoundedTauEval :=
  evalTau precision tau3612 contact3612 logTwoBall

theorem center_sq3612 : (center3612.re : ℝ)^2 +
    (center3612.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3612]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3612 : work3612.theta.ok = true ∧
    work3612.jac.invOK = true ∧ acceptsUnitSq work3612.out = true := by
  norm_num [work3612, contact3612, tau3612, center3612, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3612 : CellCertificate where
  tauBall := tau3612
  contactCenter := center3612
  contactBall := contact3612
  work := work3612
  center_sq := center_sq3612
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3612.1
  jac_ok := checks3612.2.1
  accepted := checks3612.2.2

def tau3613 : RatBall :=
  ⟨⟨43/640, 49/128⟩, 3/1280⟩
def center3613 : GaussianRat :=
  ⟨6843329/125000000, 556939/2000000⟩
def contact3613 : RatBall := localContactBall tau3613 center3613
def work3613 : RoundedTauEval :=
  evalTau precision tau3613 contact3613 logTwoBall

theorem center_sq3613 : (center3613.re : ℝ)^2 +
    (center3613.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3613]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3613 : work3613.theta.ok = true ∧
    work3613.jac.invOK = true ∧ acceptsUnitSq work3613.out = true := by
  norm_num [work3613, contact3613, tau3613, center3613, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3613 : CellCertificate where
  tauBall := tau3613
  contactCenter := center3613
  contactBall := contact3613
  work := work3613
  center_sq := center_sq3613
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3613.1
  jac_ok := checks3613.2.1
  accepted := checks3613.2.2

def tau3614 : RatBall :=
  ⟨⟨41/640, 247/640⟩, 3/1280⟩
def center3614 : GaussianRat :=
  ⟨52366871/1000000000, 70290053/250000000⟩
def contact3614 : RatBall := localContactBall tau3614 center3614
def work3614 : RoundedTauEval :=
  evalTau precision tau3614 contact3614 logTwoBall

theorem center_sq3614 : (center3614.re : ℝ)^2 +
    (center3614.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3614]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3614 : work3614.theta.ok = true ∧
    work3614.jac.invOK = true ∧ acceptsUnitSq work3614.out = true := by
  norm_num [work3614, contact3614, tau3614, center3614, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3614 : CellCertificate where
  tauBall := tau3614
  contactCenter := center3614
  contactBall := contact3614
  work := work3614
  center_sq := center_sq3614
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3614.1
  jac_ok := checks3614.2.1
  accepted := checks3614.2.2

def tau3615 : RatBall :=
  ⟨⟨43/640, 247/640⟩, 3/1280⟩
def center3615 : GaussianRat :=
  ⟨3431607/62500000, 70250913/250000000⟩
def contact3615 : RatBall := localContactBall tau3615 center3615
def work3615 : RoundedTauEval :=
  evalTau precision tau3615 contact3615 logTwoBall

theorem center_sq3615 : (center3615.re : ℝ)^2 +
    (center3615.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3615]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3615 : work3615.theta.ok = true ∧
    work3615.jac.invOK = true ∧ acceptsUnitSq work3615.out = true := by
  norm_num [work3615, contact3615, tau3615, center3615, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3615 : CellCertificate where
  tauBall := tau3615
  contactCenter := center3615
  contactBall := contact3615
  work := work3615
  center_sq := center_sq3615
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3615.1
  jac_ok := checks3615.2.1
  accepted := checks3615.2.2

def cells : List CellCertificate := [cell3608, cell3609, cell3610, cell3611, cell3612, cell3613, cell3614, cell3615]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0451
