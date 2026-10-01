import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2760 : RatBall :=
  ⟨⟨-53/640, -241/640⟩, 3/1280⟩
def center2760 : GaussianRat :=
  ⟨-13397789/200000000, -54513591/200000000⟩
def contact2760 : RatBall := localContactBall tau2760 center2760
def work2760 : RoundedTauEval :=
  evalTau precision tau2760 contact2760 logTwoBall

theorem center_sq2760 : (center2760.re : ℝ)^2 +
    (center2760.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2760]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2760 : work2760.theta.ok = true ∧
    work2760.jac.invOK = true ∧ acceptsUnitSq work2760.out = true := by
  norm_num [work2760, contact2760, tau2760, center2760, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2760 : CellCertificate where
  tauBall := tau2760
  contactCenter := center2760
  contactBall := contact2760
  work := work2760
  center_sq := center_sq2760
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2760.1
  jac_ok := checks2760.2.1
  accepted := checks2760.2.2

def tau2761 : RatBall :=
  ⟨⟨-51/640, -243/640⟩, 3/1280⟩
def center2761 : GaussianRat :=
  ⟨-32332713/500000000, -275263239/1000000000⟩
def contact2761 : RatBall := localContactBall tau2761 center2761
def work2761 : RoundedTauEval :=
  evalTau precision tau2761 contact2761 logTwoBall

theorem center_sq2761 : (center2761.re : ℝ)^2 +
    (center2761.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2761]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2761 : work2761.theta.ok = true ∧
    work2761.jac.invOK = true ∧ acceptsUnitSq work2761.out = true := by
  norm_num [work2761, contact2761, tau2761, center2761, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2761 : CellCertificate where
  tauBall := tau2761
  contactCenter := center2761
  contactBall := contact2761
  work := work2761
  center_sq := center_sq2761
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2761.1
  jac_ok := checks2761.2.1
  accepted := checks2761.2.2

def tau2762 : RatBall :=
  ⟨⟨-49/640, -243/640⟩, 3/1280⟩
def center2762 : GaussianRat :=
  ⟨-12430013/200000000, -275443499/1000000000⟩
def contact2762 : RatBall := localContactBall tau2762 center2762
def work2762 : RoundedTauEval :=
  evalTau precision tau2762 contact2762 logTwoBall

theorem center_sq2762 : (center2762.re : ℝ)^2 +
    (center2762.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2762]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2762 : work2762.theta.ok = true ∧
    work2762.jac.invOK = true ∧ acceptsUnitSq work2762.out = true := by
  norm_num [work2762, contact2762, tau2762, center2762, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2762 : CellCertificate where
  tauBall := tau2762
  contactCenter := center2762
  contactBall := contact2762
  work := work2762
  center_sq := center_sq2762
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2762.1
  jac_ok := checks2762.2.1
  accepted := checks2762.2.2

def tau2763 : RatBall :=
  ⟨⟨-51/640, -241/640⟩, 3/1280⟩
def center2763 : GaussianRat :=
  ⟨-16120741/250000000, -34094071/125000000⟩
def contact2763 : RatBall := localContactBall tau2763 center2763
def work2763 : RoundedTauEval :=
  evalTau precision tau2763 contact2763 logTwoBall

theorem center_sq2763 : (center2763.re : ℝ)^2 +
    (center2763.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2763]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2763 : work2763.theta.ok = true ∧
    work2763.jac.invOK = true ∧ acceptsUnitSq work2763.out = true := by
  norm_num [work2763, contact2763, tau2763, center2763, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2763 : CellCertificate where
  tauBall := tau2763
  contactCenter := center2763
  contactBall := contact2763
  work := work2763
  center_sq := center_sq2763
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2763.1
  jac_ok := checks2763.2.1
  accepted := checks2763.2.2

def tau2764 : RatBall :=
  ⟨⟨-49/640, -241/640⟩, 3/1280⟩
def center2764 : GaussianRat :=
  ⟨-12394897/200000000, -272930361/1000000000⟩
def contact2764 : RatBall := localContactBall tau2764 center2764
def work2764 : RoundedTauEval :=
  evalTau precision tau2764 contact2764 logTwoBall

theorem center_sq2764 : (center2764.re : ℝ)^2 +
    (center2764.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2764]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2764 : work2764.theta.ok = true ∧
    work2764.jac.invOK = true ∧ acceptsUnitSq work2764.out = true := by
  norm_num [work2764, contact2764, tau2764, center2764, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2764 : CellCertificate where
  tauBall := tau2764
  contactCenter := center2764
  contactBall := contact2764
  work := work2764
  center_sq := center_sq2764
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2764.1
  jac_ok := checks2764.2.1
  accepted := checks2764.2.2

def tau2765 : RatBall :=
  ⟨⟨-9/128, -253/640⟩, 3/1280⟩
def center2765 : GaussianRat :=
  ⟨-5795507/100000000, -288479173/1000000000⟩
def contact2765 : RatBall := localContactBall tau2765 center2765
def work2765 : RoundedTauEval :=
  evalTau precision tau2765 contact2765 logTwoBall

theorem center_sq2765 : (center2765.re : ℝ)^2 +
    (center2765.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2765]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2765 : work2765.theta.ok = true ∧
    work2765.jac.invOK = true ∧ acceptsUnitSq work2765.out = true := by
  norm_num [work2765, contact2765, tau2765, center2765, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2765 : CellCertificate where
  tauBall := tau2765
  contactCenter := center2765
  contactBall := contact2765
  work := work2765
  center_sq := center_sq2765
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2765.1
  jac_ok := checks2765.2.1
  accepted := checks2765.2.2

def tau2766 : RatBall :=
  ⟨⟨-43/640, -253/640⟩, 3/1280⟩
def center2766 : GaussianRat :=
  ⟨-55396349/1000000000, -28864989/100000000⟩
def contact2766 : RatBall := localContactBall tau2766 center2766
def work2766 : RoundedTauEval :=
  evalTau precision tau2766 contact2766 logTwoBall

theorem center_sq2766 : (center2766.re : ℝ)^2 +
    (center2766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2766 : work2766.theta.ok = true ∧
    work2766.jac.invOK = true ∧ acceptsUnitSq work2766.out = true := by
  norm_num [work2766, contact2766, tau2766, center2766, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2766 : CellCertificate where
  tauBall := tau2766
  contactCenter := center2766
  contactBall := contact2766
  work := work2766
  center_sq := center_sq2766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2766.1
  jac_ok := checks2766.2.1
  accepted := checks2766.2.2

def tau2767 : RatBall :=
  ⟨⟨-41/640, -253/640⟩, 3/1280⟩
def center2767 : GaussianRat :=
  ⟨-52835321/1000000000, -11552523/40000000⟩
def contact2767 : RatBall := localContactBall tau2767 center2767
def work2767 : RoundedTauEval :=
  evalTau precision tau2767 contact2767 logTwoBall

theorem center_sq2767 : (center2767.re : ℝ)^2 +
    (center2767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2767 : work2767.theta.ok = true ∧
    work2767.jac.invOK = true ∧ acceptsUnitSq work2767.out = true := by
  norm_num [work2767, contact2767, tau2767, center2767, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2767 : CellCertificate where
  tauBall := tau2767
  contactCenter := center2767
  contactBall := contact2767
  work := work2767
  center_sq := center_sq2767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2767.1
  jac_ok := checks2767.2.1
  accepted := checks2767.2.2

def cells : List CellCertificate := [cell2760, cell2761, cell2762, cell2763, cell2764, cell2765, cell2766, cell2767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345
