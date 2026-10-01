import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0107

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0856 : RatBall :=
  ⟨⟨-9/32, 33/160⟩, 3/320⟩
def center0856 : GaussianRat :=
  ⟨-197489591/1000000000, 66677907/500000000⟩
def contact0856 : RatBall := localContactBall tau0856 center0856
def work0856 : RoundedTauEval :=
  evalTau precision tau0856 contact0856 logTwoBall

theorem center_sq0856 : (center0856.re : ℝ)^2 +
    (center0856.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0856]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0856 : work0856.theta.ok = true ∧
    work0856.jac.invOK = true ∧ acceptsUnitSq work0856.out = true := by
  norm_num [work0856, contact0856, tau0856, center0856, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0856 : CellCertificate where
  tauBall := tau0856
  contactCenter := center0856
  contactBall := contact0856
  work := work0856
  center_sq := center_sq0856
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0856.1
  jac_ok := checks0856.2.1
  accepted := checks0856.2.2

def tau0857 : RatBall :=
  ⟨⟨-47/160, 7/32⟩, 3/320⟩
def center0857 : GaussianRat :=
  ⟨-206714057/1000000000, 70283583/500000000⟩
def contact0857 : RatBall := localContactBall tau0857 center0857
def work0857 : RoundedTauEval :=
  evalTau precision tau0857 contact0857 logTwoBall

theorem center_sq0857 : (center0857.re : ℝ)^2 +
    (center0857.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0857]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0857 : work0857.theta.ok = true ∧
    work0857.jac.invOK = true ∧ acceptsUnitSq work0857.out = true := by
  norm_num [work0857, contact0857, tau0857, center0857, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0857 : CellCertificate where
  tauBall := tau0857
  contactCenter := center0857
  contactBall := contact0857
  work := work0857
  center_sq := center_sq0857
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0857.1
  jac_ok := checks0857.2.1
  accepted := checks0857.2.2

def tau0858 : RatBall :=
  ⟨⟨-9/32, 7/32⟩, 3/320⟩
def center0858 : GaussianRat :=
  ⟨-49620407/250000000, 141607653/1000000000⟩
def contact0858 : RatBall := localContactBall tau0858 center0858
def work0858 : RoundedTauEval :=
  evalTau precision tau0858 contact0858 logTwoBall

theorem center_sq0858 : (center0858.re : ℝ)^2 +
    (center0858.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0858]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0858 : work0858.theta.ok = true ∧
    work0858.jac.invOK = true ∧ acceptsUnitSq work0858.out = true := by
  norm_num [work0858, contact0858, tau0858, center0858, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0858 : CellCertificate where
  tauBall := tau0858
  contactCenter := center0858
  contactBall := contact0858
  work := work0858
  center_sq := center_sq0858
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0858.1
  jac_ok := checks0858.2.1
  accepted := checks0858.2.2

def tau0859 : RatBall :=
  ⟨⟨-43/160, 33/160⟩, 3/320⟩
def center0859 : GaussianRat :=
  ⟨-189219451/1000000000, 67150009/500000000⟩
def contact0859 : RatBall := localContactBall tau0859 center0859
def work0859 : RoundedTauEval :=
  evalTau precision tau0859 contact0859 logTwoBall

theorem center_sq0859 : (center0859.re : ℝ)^2 +
    (center0859.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0859]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0859 : work0859.theta.ok = true ∧
    work0859.jac.invOK = true ∧ acceptsUnitSq work0859.out = true := by
  norm_num [work0859, contact0859, tau0859, center0859, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0859 : CellCertificate where
  tauBall := tau0859
  contactCenter := center0859
  contactBall := contact0859
  work := work0859
  center_sq := center_sq0859
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0859.1
  jac_ok := checks0859.2.1
  accepted := checks0859.2.2

def tau0860 : RatBall :=
  ⟨⟨-41/160, 33/160⟩, 3/320⟩
def center0860 : GaussianRat :=
  ⟨-180884951/1000000000, 135214257/1000000000⟩
def contact0860 : RatBall := localContactBall tau0860 center0860
def work0860 : RoundedTauEval :=
  evalTau precision tau0860 contact0860 logTwoBall

theorem center_sq0860 : (center0860.re : ℝ)^2 +
    (center0860.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0860]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0860 : work0860.theta.ok = true ∧
    work0860.jac.invOK = true ∧ acceptsUnitSq work0860.out = true := by
  norm_num [work0860, contact0860, tau0860, center0860, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0860 : CellCertificate where
  tauBall := tau0860
  contactCenter := center0860
  contactBall := contact0860
  work := work0860
  center_sq := center_sq0860
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0860.1
  jac_ok := checks0860.2.1
  accepted := checks0860.2.2

def tau0861 : RatBall :=
  ⟨⟨-43/160, 7/32⟩, 3/320⟩
def center0861 : GaussianRat :=
  ⟨-9509069/50000000, 71308977/500000000⟩
def contact0861 : RatBall := localContactBall tau0861 center0861
def work0861 : RoundedTauEval :=
  evalTau precision tau0861 contact0861 logTwoBall

theorem center_sq0861 : (center0861.re : ℝ)^2 +
    (center0861.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0861]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0861 : work0861.theta.ok = true ∧
    work0861.jac.invOK = true ∧ acceptsUnitSq work0861.out = true := by
  norm_num [work0861, contact0861, tau0861, center0861, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0861 : CellCertificate where
  tauBall := tau0861
  contactCenter := center0861
  contactBall := contact0861
  work := work0861
  center_sq := center_sq0861
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0861.1
  jac_ok := checks0861.2.1
  accepted := checks0861.2.2

def tau0862 : RatBall :=
  ⟨⟨-41/160, 7/32⟩, 3/320⟩
def center0862 : GaussianRat :=
  ⟨-90907579/500000000, 143596387/1000000000⟩
def contact0862 : RatBall := localContactBall tau0862 center0862
def work0862 : RoundedTauEval :=
  evalTau precision tau0862 contact0862 logTwoBall

theorem center_sq0862 : (center0862.re : ℝ)^2 +
    (center0862.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0862]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0862 : work0862.theta.ok = true ∧
    work0862.jac.invOK = true ∧ acceptsUnitSq work0862.out = true := by
  norm_num [work0862, contact0862, tau0862, center0862, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0862 : CellCertificate where
  tauBall := tau0862
  contactCenter := center0862
  contactBall := contact0862
  work := work0862
  center_sq := center_sq0862
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0862.1
  jac_ok := checks0862.2.1
  accepted := checks0862.2.2

def tau0863 : RatBall :=
  ⟨⟨-47/160, 37/160⟩, 3/320⟩
def center0863 : GaussianRat :=
  ⟨-103902067/500000000, 37194907/250000000⟩
def contact0863 : RatBall := localContactBall tau0863 center0863
def work0863 : RoundedTauEval :=
  evalTau precision tau0863 contact0863 logTwoBall

theorem center_sq0863 : (center0863.re : ℝ)^2 +
    (center0863.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0863]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0863 : work0863.theta.ok = true ∧
    work0863.jac.invOK = true ∧ acceptsUnitSq work0863.out = true := by
  norm_num [work0863, contact0863, tau0863, center0863, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0863 : CellCertificate where
  tauBall := tau0863
  contactCenter := center0863
  contactBall := contact0863
  work := work0863
  center_sq := center_sq0863
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0863.1
  jac_ok := checks0863.2.1
  accepted := checks0863.2.2

def cells : List CellCertificate := [cell0856, cell0857, cell0858, cell0859, cell0860, cell0861, cell0862, cell0863]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0107
