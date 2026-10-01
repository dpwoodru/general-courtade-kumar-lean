import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0461

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3688 : RatBall :=
  ⟨⟨123/640, 221/640⟩, 3/1280⟩
def center3688 : GaussianRat :=
  ⟨29748323/200000000, 119366383/500000000⟩
def contact3688 : RatBall := localContactBall tau3688 center3688
def work3688 : RoundedTauEval :=
  evalTau precision tau3688 contact3688 logTwoBall

theorem center_sq3688 : (center3688.re : ℝ)^2 +
    (center3688.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3688]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3688 : work3688.theta.ok = true ∧
    work3688.jac.invOK = true ∧ acceptsUnitSq work3688.out = true := by
  norm_num [work3688, contact3688, tau3688, center3688, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3688 : CellCertificate where
  tauBall := tau3688
  contactCenter := center3688
  contactBall := contact3688
  work := work3688
  center_sq := center_sq3688
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3688.1
  jac_ok := checks3688.2.1
  accepted := checks3688.2.2

def tau3689 : RatBall :=
  ⟨⟨121/640, 223/640⟩, 3/1280⟩
def center3689 : GaussianRat :=
  ⟨146768957/1000000000, 60350721/250000000⟩
def contact3689 : RatBall := localContactBall tau3689 center3689
def work3689 : RoundedTauEval :=
  evalTau precision tau3689 contact3689 logTwoBall

theorem center_sq3689 : (center3689.re : ℝ)^2 +
    (center3689.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3689]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3689 : work3689.theta.ok = true ∧
    work3689.jac.invOK = true ∧ acceptsUnitSq work3689.out = true := by
  norm_num [work3689, contact3689, tau3689, center3689, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3689 : CellCertificate where
  tauBall := tau3689
  contactCenter := center3689
  contactBall := contact3689
  work := work3689
  center_sq := center_sq3689
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3689.1
  jac_ok := checks3689.2.1
  accepted := checks3689.2.2

def tau3690 : RatBall :=
  ⟨⟨123/640, 223/640⟩, 3/1280⟩
def center3690 : GaussianRat :=
  ⟨74546313/500000000, 120525907/500000000⟩
def contact3690 : RatBall := localContactBall tau3690 center3690
def work3690 : RoundedTauEval :=
  evalTau precision tau3690 contact3690 logTwoBall

theorem center_sq3690 : (center3690.re : ℝ)^2 +
    (center3690.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3690]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3690 : work3690.theta.ok = true ∧
    work3690.jac.invOK = true ∧ acceptsUnitSq work3690.out = true := by
  norm_num [work3690, contact3690, tau3690, center3690, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3690 : CellCertificate where
  tauBall := tau3690
  contactCenter := center3690
  contactBall := contact3690
  work := work3690
  center_sq := center_sq3690
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3690.1
  jac_ok := checks3690.2.1
  accepted := checks3690.2.2

def tau3691 : RatBall :=
  ⟨⟨25/128, 221/640⟩, 3/1280⟩
def center3691 : GaussianRat :=
  ⟨151056059/1000000000, 238381849/1000000000⟩
def contact3691 : RatBall := localContactBall tau3691 center3691
def work3691 : RoundedTauEval :=
  evalTau precision tau3691 contact3691 logTwoBall

theorem center_sq3691 : (center3691.re : ℝ)^2 +
    (center3691.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3691]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3691 : work3691.theta.ok = true ∧
    work3691.jac.invOK = true ∧ acceptsUnitSq work3691.out = true := by
  norm_num [work3691, contact3691, tau3691, center3691, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3691 : CellCertificate where
  tauBall := tau3691
  contactCenter := center3691
  contactBall := contact3691
  work := work3691
  center_sq := center_sq3691
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3691.1
  jac_ok := checks3691.2.1
  accepted := checks3691.2.2

def tau3692 : RatBall :=
  ⟨⟨127/640, 221/640⟩, 3/1280⟩
def center3692 : GaussianRat :=
  ⟨38341447/250000000, 29753309/125000000⟩
def contact3692 : RatBall := localContactBall tau3692 center3692
def work3692 : RoundedTauEval :=
  evalTau precision tau3692 contact3692 logTwoBall

theorem center_sq3692 : (center3692.re : ℝ)^2 +
    (center3692.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3692]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3692 : work3692.theta.ok = true ∧
    work3692.jac.invOK = true ∧ acceptsUnitSq work3692.out = true := by
  norm_num [work3692, contact3692, tau3692, center3692, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3692 : CellCertificate where
  tauBall := tau3692
  contactCenter := center3692
  contactBall := contact3692
  work := work3692
  center_sq := center_sq3692
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3692.1
  jac_ok := checks3692.2.1
  accepted := checks3692.2.2

def tau3693 : RatBall :=
  ⟨⟨25/128, 223/640⟩, 3/1280⟩
def center3693 : GaussianRat :=
  ⟨151411581/1000000000, 120348091/500000000⟩
def contact3693 : RatBall := localContactBall tau3693 center3693
def work3693 : RoundedTauEval :=
  evalTau precision tau3693 contact3693 logTwoBall

theorem center_sq3693 : (center3693.re : ℝ)^2 +
    (center3693.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3693]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3693 : work3693.theta.ok = true ∧
    work3693.jac.invOK = true ∧ acceptsUnitSq work3693.out = true := by
  norm_num [work3693, contact3693, tau3693, center3693, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3693 : CellCertificate where
  tauBall := tau3693
  contactCenter := center3693
  contactBall := contact3693
  work := work3693
  center_sq := center_sq3693
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3693.1
  jac_ok := checks3693.2.1
  accepted := checks3693.2.2

def tau3694 : RatBall :=
  ⟨⟨127/640, 223/640⟩, 3/1280⟩
def center3694 : GaussianRat :=
  ⟨153725769/1000000000, 120168019/500000000⟩
def contact3694 : RatBall := localContactBall tau3694 center3694
def work3694 : RoundedTauEval :=
  evalTau precision tau3694 contact3694 logTwoBall

theorem center_sq3694 : (center3694.re : ℝ)^2 +
    (center3694.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3694]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3694 : work3694.theta.ok = true ∧
    work3694.jac.invOK = true ∧ acceptsUnitSq work3694.out = true := by
  norm_num [work3694, contact3694, tau3694, center3694, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3694 : CellCertificate where
  tauBall := tau3694
  contactCenter := center3694
  contactBall := contact3694
  work := work3694
  center_sq := center_sq3694
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3694.1
  jac_ok := checks3694.2.1
  accepted := checks3694.2.2

def tau3695 : RatBall :=
  ⟨⟨13/128, 237/640⟩, 3/1280⟩
def center3695 : GaussianRat :=
  ⟨40758673/500000000, 133178453/500000000⟩
def contact3695 : RatBall := localContactBall tau3695 center3695
def work3695 : RoundedTauEval :=
  evalTau precision tau3695 contact3695 logTwoBall

theorem center_sq3695 : (center3695.re : ℝ)^2 +
    (center3695.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3695]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3695 : work3695.theta.ok = true ∧
    work3695.jac.invOK = true ∧ acceptsUnitSq work3695.out = true := by
  norm_num [work3695, contact3695, tau3695, center3695, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3695 : CellCertificate where
  tauBall := tau3695
  contactCenter := center3695
  contactBall := contact3695
  work := work3695
  center_sq := center_sq3695
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3695.1
  jac_ok := checks3695.2.1
  accepted := checks3695.2.2

def cells : List CellCertificate := [cell3688, cell3689, cell3690, cell3691, cell3692, cell3693, cell3694, cell3695]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0461
