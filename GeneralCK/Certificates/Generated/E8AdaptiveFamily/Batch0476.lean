import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3808 : RatBall :=
  ⟨⟨103/640, 47/128⟩, 3/1280⟩
def center3808 : GaussianRat :=
  ⟨31890163/250000000, 51727193/200000000⟩
def contact3808 : RatBall := localContactBall tau3808 center3808
def work3808 : RoundedTauEval :=
  evalTau precision tau3808 contact3808 logTwoBall

theorem center_sq3808 : (center3808.re : ℝ)^2 +
    (center3808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3808 : work3808.theta.ok = true ∧
    work3808.jac.invOK = true ∧ acceptsUnitSq work3808.out = true := by
  norm_num [work3808, contact3808, tau3808, center3808, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3808 : CellCertificate where
  tauBall := tau3808
  contactCenter := center3808
  contactBall := contact3808
  work := work3808
  center_sq := center_sq3808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3808.1
  jac_ok := checks3808.2.1
  accepted := checks3808.2.2

def tau3809 : RatBall :=
  ⟨⟨97/640, 237/640⟩, 3/1280⟩
def center3809 : GaussianRat :=
  ⟨60333117/500000000, 6550423/25000000⟩
def contact3809 : RatBall := localContactBall tau3809 center3809
def work3809 : RoundedTauEval :=
  evalTau precision tau3809 contact3809 logTwoBall

theorem center_sq3809 : (center3809.re : ℝ)^2 +
    (center3809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3809 : work3809.theta.ok = true ∧
    work3809.jac.invOK = true ∧ acceptsUnitSq work3809.out = true := by
  norm_num [work3809, contact3809, tau3809, center3809, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3809 : CellCertificate where
  tauBall := tau3809
  contactCenter := center3809
  contactBall := contact3809
  work := work3809
  center_sq := center_sq3809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3809.1
  jac_ok := checks3809.2.1
  accepted := checks3809.2.2

def tau3810 : RatBall :=
  ⟨⟨99/640, 237/640⟩, 3/1280⟩
def center3810 : GaussianRat :=
  ⟨123079793/1000000000, 65423867/250000000⟩
def contact3810 : RatBall := localContactBall tau3810 center3810
def work3810 : RoundedTauEval :=
  evalTau precision tau3810 contact3810 logTwoBall

theorem center_sq3810 : (center3810.re : ℝ)^2 +
    (center3810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3810 : work3810.theta.ok = true ∧
    work3810.jac.invOK = true ∧ acceptsUnitSq work3810.out = true := by
  norm_num [work3810, contact3810, tau3810, center3810, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3810 : CellCertificate where
  tauBall := tau3810
  contactCenter := center3810
  contactBall := contact3810
  work := work3810
  center_sq := center_sq3810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3810.1
  jac_ok := checks3810.2.1
  accepted := checks3810.2.2

def tau3811 : RatBall :=
  ⟨⟨21/128, 233/640⟩, 3/1280⟩
def center3811 : GaussianRat :=
  ⟨8101339/62500000, 3998631/15625000⟩
def contact3811 : RatBall := localContactBall tau3811 center3811
def work3811 : RoundedTauEval :=
  evalTau precision tau3811 contact3811 logTwoBall

theorem center_sq3811 : (center3811.re : ℝ)^2 +
    (center3811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3811 : work3811.theta.ok = true ∧
    work3811.jac.invOK = true ∧ acceptsUnitSq work3811.out = true := by
  norm_num [work3811, contact3811, tau3811, center3811, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3811 : CellCertificate where
  tauBall := tau3811
  contactCenter := center3811
  contactBall := contact3811
  work := work3811
  center_sq := center_sq3811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3811.1
  jac_ok := checks3811.2.1
  accepted := checks3811.2.2

def tau3812 : RatBall :=
  ⟨⟨107/640, 233/640⟩, 3/1280⟩
def center3812 : GaussianRat :=
  ⟨132006469/1000000000, 255577867/1000000000⟩
def contact3812 : RatBall := localContactBall tau3812 center3812
def work3812 : RoundedTauEval :=
  evalTau precision tau3812 contact3812 logTwoBall

theorem center_sq3812 : (center3812.re : ℝ)^2 +
    (center3812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3812 : work3812.theta.ok = true ∧
    work3812.jac.invOK = true ∧ acceptsUnitSq work3812.out = true := by
  norm_num [work3812, contact3812, tau3812, center3812, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3812 : CellCertificate where
  tauBall := tau3812
  contactCenter := center3812
  contactBall := contact3812
  work := work3812
  center_sq := center_sq3812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3812.1
  jac_ok := checks3812.2.1
  accepted := checks3812.2.2

def tau3813 : RatBall :=
  ⟨⟨109/640, 233/640⟩, 3/1280⟩
def center3813 : GaussianRat :=
  ⟨134387007/1000000000, 127619041/500000000⟩
def contact3813 : RatBall := localContactBall tau3813 center3813
def work3813 : RoundedTauEval :=
  evalTau precision tau3813 contact3813 logTwoBall

theorem center_sq3813 : (center3813.re : ℝ)^2 +
    (center3813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3813 : work3813.theta.ok = true ∧
    work3813.jac.invOK = true ∧ acceptsUnitSq work3813.out = true := by
  norm_num [work3813, contact3813, tau3813, center3813, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3813 : CellCertificate where
  tauBall := tau3813
  contactCenter := center3813
  contactBall := contact3813
  work := work3813
  center_sq := center_sq3813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3813.1
  jac_ok := checks3813.2.1
  accepted := checks3813.2.2

def tau3814 : RatBall :=
  ⟨⟨113/640, 45/128⟩, 3/1280⟩
def center3814 : GaussianRat :=
  ⟨137760383/1000000000, 245107147/1000000000⟩
def contact3814 : RatBall := localContactBall tau3814 center3814
def work3814 : RoundedTauEval :=
  evalTau precision tau3814 contact3814 logTwoBall

theorem center_sq3814 : (center3814.re : ℝ)^2 +
    (center3814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3814]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3814 : work3814.theta.ok = true ∧
    work3814.jac.invOK = true ∧ acceptsUnitSq work3814.out = true := by
  norm_num [work3814, contact3814, tau3814, center3814, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3814 : CellCertificate where
  tauBall := tau3814
  contactCenter := center3814
  contactBall := contact3814
  work := work3814
  center_sq := center_sq3814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3814.1
  jac_ok := checks3814.2.1
  accepted := checks3814.2.2

def tau3815 : RatBall :=
  ⟨⟨23/128, 45/128⟩, 3/1280⟩
def center3815 : GaussianRat :=
  ⟨5604287/40000000, 122385171/500000000⟩
def contact3815 : RatBall := localContactBall tau3815 center3815
def work3815 : RoundedTauEval :=
  evalTau precision tau3815 contact3815 logTwoBall

theorem center_sq3815 : (center3815.re : ℝ)^2 +
    (center3815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3815 : work3815.theta.ok = true ∧
    work3815.jac.invOK = true ∧ acceptsUnitSq work3815.out = true := by
  norm_num [work3815, contact3815, tau3815, center3815, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3815 : CellCertificate where
  tauBall := tau3815
  contactCenter := center3815
  contactBall := contact3815
  work := work3815
  center_sq := center_sq3815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3815.1
  jac_ok := checks3815.2.1
  accepted := checks3815.2.2

def cells : List CellCertificate := [cell3808, cell3809, cell3810, cell3811, cell3812, cell3813, cell3814, cell3815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476
