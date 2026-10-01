import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2792 : RatBall :=
  ⟨⟨-43/640, -247/640⟩, 3/1280⟩
def center2792 : GaussianRat :=
  ⟨-3431607/62500000, -70250913/250000000⟩
def contact2792 : RatBall := localContactBall tau2792 center2792
def work2792 : RoundedTauEval :=
  evalTau precision tau2792 contact2792 logTwoBall

theorem center_sq2792 : (center2792.re : ℝ)^2 +
    (center2792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2792 : work2792.theta.ok = true ∧
    work2792.jac.invOK = true ∧ acceptsUnitSq work2792.out = true := by
  norm_num [work2792, contact2792, tau2792, center2792, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2792 : CellCertificate where
  tauBall := tau2792
  contactCenter := center2792
  contactBall := contact2792
  work := work2792
  center_sq := center_sq2792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2792.1
  jac_ok := checks2792.2.1
  accepted := checks2792.2.2

def tau2793 : RatBall :=
  ⟨⟨-41/640, -247/640⟩, 3/1280⟩
def center2793 : GaussianRat :=
  ⟨-52366871/1000000000, -70290053/250000000⟩
def contact2793 : RatBall := localContactBall tau2793 center2793
def work2793 : RoundedTauEval :=
  evalTau precision tau2793 contact2793 logTwoBall

theorem center_sq2793 : (center2793.re : ℝ)^2 +
    (center2793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2793 : work2793.theta.ok = true ∧
    work2793.jac.invOK = true ∧ acceptsUnitSq work2793.out = true := by
  norm_num [work2793, contact2793, tau2793, center2793, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2793 : CellCertificate where
  tauBall := tau2793
  contactCenter := center2793
  contactBall := contact2793
  work := work2793
  center_sq := center_sq2793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2793.1
  jac_ok := checks2793.2.1
  accepted := checks2793.2.2

def tau2794 : RatBall :=
  ⟨⟨-43/640, -49/128⟩, 3/1280⟩
def center2794 : GaussianRat :=
  ⟨-6843329/125000000, -556939/2000000⟩
def contact2794 : RatBall := localContactBall tau2794 center2794
def work2794 : RoundedTauEval :=
  evalTau precision tau2794 contact2794 logTwoBall

theorem center_sq2794 : (center2794.re : ℝ)^2 +
    (center2794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2794 : work2794.theta.ok = true ∧
    work2794.jac.invOK = true ∧ acceptsUnitSq work2794.out = true := by
  norm_num [work2794, contact2794, tau2794, center2794, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2794 : CellCertificate where
  tauBall := tau2794
  contactCenter := center2794
  contactBall := contact2794
  work := work2794
  center_sq := center_sq2794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2794.1
  jac_ok := checks2794.2.1
  accepted := checks2794.2.2

def tau2795 : RatBall :=
  ⟨⟨-41/640, -49/128⟩, 3/1280⟩
def center2795 : GaussianRat :=
  ⟨-13053747/250000000, -34827989/125000000⟩
def contact2795 : RatBall := localContactBall tau2795 center2795
def work2795 : RoundedTauEval :=
  evalTau precision tau2795 contact2795 logTwoBall

theorem center_sq2795 : (center2795.re : ℝ)^2 +
    (center2795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2795 : work2795.theta.ok = true ∧
    work2795.jac.invOK = true ∧ acceptsUnitSq work2795.out = true := by
  norm_num [work2795, contact2795, tau2795, center2795, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2795 : CellCertificate where
  tauBall := tau2795
  contactCenter := center2795
  contactBall := contact2795
  work := work2795
  center_sq := center_sq2795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2795.1
  jac_ok := checks2795.2.1
  accepted := checks2795.2.2

def tau2796 : RatBall :=
  ⟨⟨-47/640, -243/640⟩, 3/1280⟩
def center2796 : GaussianRat :=
  ⟨-59632267/1000000000, -137808407/500000000⟩
def contact2796 : RatBall := localContactBall tau2796 center2796
def work2796 : RoundedTauEval :=
  evalTau precision tau2796 contact2796 logTwoBall

theorem center_sq2796 : (center2796.re : ℝ)^2 +
    (center2796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2796 : work2796.theta.ok = true ∧
    work2796.jac.invOK = true ∧ acceptsUnitSq work2796.out = true := by
  norm_num [work2796, contact2796, tau2796, center2796, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2796 : CellCertificate where
  tauBall := tau2796
  contactCenter := center2796
  contactBall := contact2796
  work := work2796
  center_sq := center_sq2796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2796.1
  jac_ok := checks2796.2.1
  accepted := checks2796.2.2

def tau2797 : RatBall :=
  ⟨⟨-9/128, -243/640⟩, 3/1280⟩
def center2797 : GaussianRat :=
  ⟨-456897/8000000, -17236447/62500000⟩
def contact2797 : RatBall := localContactBall tau2797 center2797
def work2797 : RoundedTauEval :=
  evalTau precision tau2797 contact2797 logTwoBall

theorem center_sq2797 : (center2797.re : ℝ)^2 +
    (center2797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2797 : work2797.theta.ok = true ∧
    work2797.jac.invOK = true ∧ acceptsUnitSq work2797.out = true := by
  norm_num [work2797, contact2797, tau2797, center2797, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2797 : CellCertificate where
  tauBall := tau2797
  contactCenter := center2797
  contactBall := contact2797
  work := work2797
  center_sq := center_sq2797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2797.1
  jac_ok := checks2797.2.1
  accepted := checks2797.2.2

def tau2798 : RatBall :=
  ⟨⟨-47/640, -241/640⟩, 3/1280⟩
def center2798 : GaussianRat :=
  ⟨-59463601/1000000000, -273101301/1000000000⟩
def contact2798 : RatBall := localContactBall tau2798 center2798
def work2798 : RoundedTauEval :=
  evalTau precision tau2798 contact2798 logTwoBall

theorem center_sq2798 : (center2798.re : ℝ)^2 +
    (center2798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2798 : work2798.theta.ok = true ∧
    work2798.jac.invOK = true ∧ acceptsUnitSq work2798.out = true := by
  norm_num [work2798, contact2798, tau2798, center2798, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2798 : CellCertificate where
  tauBall := tau2798
  contactCenter := center2798
  contactBall := contact2798
  work := work2798
  center_sq := center_sq2798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2798.1
  jac_ok := checks2798.2.1
  accepted := checks2798.2.2

def tau2799 : RatBall :=
  ⟨⟨-9/128, -241/640⟩, 3/1280⟩
def center2799 : GaussianRat :=
  ⟨-11390081/200000000, -136632679/500000000⟩
def contact2799 : RatBall := localContactBall tau2799 center2799
def work2799 : RoundedTauEval :=
  evalTau precision tau2799 contact2799 logTwoBall

theorem center_sq2799 : (center2799.re : ℝ)^2 +
    (center2799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2799 : work2799.theta.ok = true ∧
    work2799.jac.invOK = true ∧ acceptsUnitSq work2799.out = true := by
  norm_num [work2799, contact2799, tau2799, center2799, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2799 : CellCertificate where
  tauBall := tau2799
  contactCenter := center2799
  contactBall := contact2799
  work := work2799
  center_sq := center_sq2799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2799.1
  jac_ok := checks2799.2.1
  accepted := checks2799.2.2

def cells : List CellCertificate := [cell2792, cell2793, cell2794, cell2795, cell2796, cell2797, cell2798, cell2799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349
