import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0736 : RatBall :=
  ⟨⟨53/160, -23/160⟩, 3/320⟩
def center0736 : GaussianRat :=
  ⟨225467593/1000000000, -89762261/1000000000⟩
def contact0736 : RatBall := localContactBall tau0736 center0736
def work0736 : RoundedTauEval :=
  evalTau precision tau0736 contact0736 logTwoBall

theorem center_sq0736 : (center0736.re : ℝ)^2 +
    (center0736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0736 : work0736.theta.ok = true ∧
    work0736.jac.invOK = true ∧ acceptsUnitSq work0736.out = true := by
  norm_num [work0736, contact0736, tau0736, center0736, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0736 : CellCertificate where
  tauBall := tau0736
  contactCenter := center0736
  contactBall := contact0736
  work := work0736
  center_sq := center_sq0736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0736.1
  jac_ok := checks0736.2.1
  accepted := checks0736.2.2

def tau0737 : RatBall :=
  ⟨⟨11/32, -23/160⟩, 3/320⟩
def center0737 : GaussianRat :=
  ⟨58324897/250000000, -11129939/125000000⟩
def contact0737 : RatBall := localContactBall tau0737 center0737
def work0737 : RoundedTauEval :=
  evalTau precision tau0737 contact0737 logTwoBall

theorem center_sq0737 : (center0737.re : ℝ)^2 +
    (center0737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0737 : work0737.theta.ok = true ∧
    work0737.jac.invOK = true ∧ acceptsUnitSq work0737.out = true := by
  norm_num [work0737, contact0737, tau0737, center0737, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0737 : CellCertificate where
  tauBall := tau0737
  contactCenter := center0737
  contactBall := contact0737
  work := work0737
  center_sq := center_sq0737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0737.1
  jac_ok := checks0737.2.1
  accepted := checks0737.2.2

def tau0738 : RatBall :=
  ⟨⟨53/160, -21/160⟩, 3/320⟩
def center0738 : GaussianRat :=
  ⟨224785281/1000000000, -4095231/50000000⟩
def contact0738 : RatBall := localContactBall tau0738 center0738
def work0738 : RoundedTauEval :=
  evalTau precision tau0738 contact0738 logTwoBall

theorem center_sq0738 : (center0738.re : ℝ)^2 +
    (center0738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0738 : work0738.theta.ok = true ∧
    work0738.jac.invOK = true ∧ acceptsUnitSq work0738.out = true := by
  norm_num [work0738, contact0738, tau0738, center0738, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0738 : CellCertificate where
  tauBall := tau0738
  contactCenter := center0738
  contactBall := contact0738
  work := work0738
  center_sq := center_sq0738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0738.1
  jac_ok := checks0738.2.1
  accepted := checks0738.2.2

def tau0739 : RatBall :=
  ⟨⟨11/32, -21/160⟩, 3/320⟩
def center0739 : GaussianRat :=
  ⟨232602861/1000000000, -81248009/1000000000⟩
def contact0739 : RatBall := localContactBall tau0739 center0739
def work0739 : RoundedTauEval :=
  evalTau precision tau0739 contact0739 logTwoBall

theorem center_sq0739 : (center0739.re : ℝ)^2 +
    (center0739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0739 : work0739.theta.ok = true ∧
    work0739.jac.invOK = true ∧ acceptsUnitSq work0739.out = true := by
  norm_num [work0739, contact0739, tau0739, center0739, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0739 : CellCertificate where
  tauBall := tau0739
  contactCenter := center0739
  contactBall := contact0739
  work := work0739
  center_sq := center_sq0739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0739.1
  jac_ok := checks0739.2.1
  accepted := checks0739.2.2

def tau0740 : RatBall :=
  ⟨⟨53/160, -19/160⟩, 3/320⟩
def center0740 : GaussianRat :=
  ⟨56041997/250000000, -74061203/1000000000⟩
def contact0740 : RatBall := localContactBall tau0740 center0740
def work0740 : RoundedTauEval :=
  evalTau precision tau0740 contact0740 logTwoBall

theorem center_sq0740 : (center0740.re : ℝ)^2 +
    (center0740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0740 : work0740.theta.ok = true ∧
    work0740.jac.invOK = true ∧ acceptsUnitSq work0740.out = true := by
  norm_num [work0740, contact0740, tau0740, center0740, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0740 : CellCertificate where
  tauBall := tau0740
  contactCenter := center0740
  contactBall := contact0740
  work := work0740
  center_sq := center_sq0740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0740.1
  jac_ok := checks0740.2.1
  accepted := checks0740.2.2

def tau0741 : RatBall :=
  ⟨⟨11/32, -19/160⟩, 3/320⟩
def center0741 : GaussianRat :=
  ⟨231972447/1000000000, -73469819/1000000000⟩
def contact0741 : RatBall := localContactBall tau0741 center0741
def work0741 : RoundedTauEval :=
  evalTau precision tau0741 contact0741 logTwoBall

theorem center_sq0741 : (center0741.re : ℝ)^2 +
    (center0741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0741 : work0741.theta.ok = true ∧
    work0741.jac.invOK = true ∧ acceptsUnitSq work0741.out = true := by
  norm_num [work0741, contact0741, tau0741, center0741, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0741 : CellCertificate where
  tauBall := tau0741
  contactCenter := center0741
  contactBall := contact0741
  work := work0741
  center_sq := center_sq0741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0741.1
  jac_ok := checks0741.2.1
  accepted := checks0741.2.2

def tau0742 : RatBall :=
  ⟨⟨53/160, -17/160⟩, 3/320⟩
def center0742 : GaussianRat :=
  ⟨44722969/200000000, -66230667/1000000000⟩
def contact0742 : RatBall := localContactBall tau0742 center0742
def work0742 : RoundedTauEval :=
  evalTau precision tau0742 contact0742 logTwoBall

theorem center_sq0742 : (center0742.re : ℝ)^2 +
    (center0742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0742 : work0742.theta.ok = true ∧
    work0742.jac.invOK = true ∧ acceptsUnitSq work0742.out = true := by
  norm_num [work0742, contact0742, tau0742, center0742, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0742 : CellCertificate where
  tauBall := tau0742
  contactCenter := center0742
  contactBall := contact0742
  work := work0742
  center_sq := center_sq0742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0742.1
  jac_ok := checks0742.2.1
  accepted := checks0742.2.2

def tau0743 : RatBall :=
  ⟨⟨11/32, -17/160⟩, 3/320⟩
def center0743 : GaussianRat :=
  ⟨57851871/250000000, -6570369/100000000⟩
def contact0743 : RatBall := localContactBall tau0743 center0743
def work0743 : RoundedTauEval :=
  evalTau precision tau0743 contact0743 logTwoBall

theorem center_sq0743 : (center0743.re : ℝ)^2 +
    (center0743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0743 : work0743.theta.ok = true ∧
    work0743.jac.invOK = true ∧ acceptsUnitSq work0743.out = true := by
  norm_num [work0743, contact0743, tau0743, center0743, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0743 : CellCertificate where
  tauBall := tau0743
  contactCenter := center0743
  contactBall := contact0743
  work := work0743
  center_sq := center_sq0743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0743.1
  jac_ok := checks0743.2.1
  accepted := checks0743.2.2

def cells : List CellCertificate := [cell0736, cell0737, cell0738, cell0739, cell0740, cell0741, cell0742, cell0743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092
