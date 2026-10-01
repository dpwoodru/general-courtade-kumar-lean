import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0102

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0816 : RatBall :=
  ⟨⟨-57/160, 29/160⟩, 3/320⟩
def center0816 : GaussianRat :=
  ⟨-243609941/1000000000, 22312087/200000000⟩
def contact0816 : RatBall := localContactBall tau0816 center0816
def work0816 : RoundedTauEval :=
  evalTau precision tau0816 contact0816 logTwoBall

theorem center_sq0816 : (center0816.re : ℝ)^2 +
    (center0816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0816 : work0816.theta.ok = true ∧
    work0816.jac.invOK = true ∧ acceptsUnitSq work0816.out = true := by
  norm_num [work0816, contact0816, tau0816, center0816, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0816 : CellCertificate where
  tauBall := tau0816
  contactCenter := center0816
  contactBall := contact0816
  work := work0816
  center_sq := center_sq0816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0816.1
  jac_ok := checks0816.2.1
  accepted := checks0816.2.2

def tau0817 : RatBall :=
  ⟨⟨-11/32, 5/32⟩, 3/320⟩
def center0817 : GaussianRat :=
  ⟨-234063587/1000000000, 96845571/1000000000⟩
def contact0817 : RatBall := localContactBall tau0817 center0817
def work0817 : RoundedTauEval :=
  evalTau precision tau0817 contact0817 logTwoBall

theorem center_sq0817 : (center0817.re : ℝ)^2 +
    (center0817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0817 : work0817.theta.ok = true ∧
    work0817.jac.invOK = true ∧ acceptsUnitSq work0817.out = true := by
  norm_num [work0817, contact0817, tau0817, center0817, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0817 : CellCertificate where
  tauBall := tau0817
  contactCenter := center0817
  contactBall := contact0817
  work := work0817
  center_sq := center_sq0817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0817.1
  jac_ok := checks0817.2.1
  accepted := checks0817.2.2

def tau0818 : RatBall :=
  ⟨⟨-53/160, 5/32⟩, 3/320⟩
def center0818 : GaussianRat :=
  ⟨-226215887/1000000000, 24408867/250000000⟩
def contact0818 : RatBall := localContactBall tau0818 center0818
def work0818 : RoundedTauEval :=
  evalTau precision tau0818 contact0818 logTwoBall

theorem center_sq0818 : (center0818.re : ℝ)^2 +
    (center0818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0818 : work0818.theta.ok = true ∧
    work0818.jac.invOK = true ∧ acceptsUnitSq work0818.out = true := by
  norm_num [work0818, contact0818, tau0818, center0818, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0818 : CellCertificate where
  tauBall := tau0818
  contactCenter := center0818
  contactBall := contact0818
  work := work0818
  center_sq := center_sq0818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0818.1
  jac_ok := checks0818.2.1
  accepted := checks0818.2.2

def tau0819 : RatBall :=
  ⟨⟨-11/32, 27/160⟩, 3/320⟩
def center0819 : GaussianRat :=
  ⟨-234895911/1000000000, 52333711/500000000⟩
def contact0819 : RatBall := localContactBall tau0819 center0819
def work0819 : RoundedTauEval :=
  evalTau precision tau0819 contact0819 logTwoBall

theorem center_sq0819 : (center0819.re : ℝ)^2 +
    (center0819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0819 : work0819.theta.ok = true ∧
    work0819.jac.invOK = true ∧ acceptsUnitSq work0819.out = true := by
  norm_num [work0819, contact0819, tau0819, center0819, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0819 : CellCertificate where
  tauBall := tau0819
  contactCenter := center0819
  contactBall := contact0819
  work := work0819
  center_sq := center_sq0819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0819.1
  jac_ok := checks0819.2.1
  accepted := checks0819.2.2

def tau0820 : RatBall :=
  ⟨⟨-53/160, 27/160⟩, 3/320⟩
def center0820 : GaussianRat :=
  ⟨-113515613/500000000, 13190697/125000000⟩
def contact0820 : RatBall := localContactBall tau0820 center0820
def work0820 : RoundedTauEval :=
  evalTau precision tau0820 contact0820 logTwoBall

theorem center_sq0820 : (center0820.re : ℝ)^2 +
    (center0820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0820 : work0820.theta.ok = true ∧
    work0820.jac.invOK = true ∧ acceptsUnitSq work0820.out = true := by
  norm_num [work0820, contact0820, tau0820, center0820, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0820 : CellCertificate where
  tauBall := tau0820
  contactCenter := center0820
  contactBall := contact0820
  work := work0820
  center_sq := center_sq0820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0820.1
  jac_ok := checks0820.2.1
  accepted := checks0820.2.2

def tau0821 : RatBall :=
  ⟨⟨-51/160, 5/32⟩, 3/320⟩
def center0821 : GaussianRat :=
  ⟨-5457529/25000000, 49204231/500000000⟩
def contact0821 : RatBall := localContactBall tau0821 center0821
def work0821 : RoundedTauEval :=
  evalTau precision tau0821 contact0821 logTwoBall

theorem center_sq0821 : (center0821.re : ℝ)^2 +
    (center0821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0821 : work0821.theta.ok = true ∧
    work0821.jac.invOK = true ∧ acceptsUnitSq work0821.out = true := by
  norm_num [work0821, contact0821, tau0821, center0821, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0821 : CellCertificate where
  tauBall := tau0821
  contactCenter := center0821
  contactBall := contact0821
  work := work0821
  center_sq := center_sq0821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0821.1
  jac_ok := checks0821.2.1
  accepted := checks0821.2.2

def tau0822 : RatBall :=
  ⟨⟨-49/160, 5/32⟩, 3/320⟩
def center0822 : GaussianRat :=
  ⟨-52580197/250000000, 1239543/12500000⟩
def contact0822 : RatBall := localContactBall tau0822 center0822
def work0822 : RoundedTauEval :=
  evalTau precision tau0822 contact0822 logTwoBall

theorem center_sq0822 : (center0822.re : ℝ)^2 +
    (center0822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0822 : work0822.theta.ok = true ∧
    work0822.jac.invOK = true ∧ acceptsUnitSq work0822.out = true := by
  norm_num [work0822, contact0822, tau0822, center0822, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0822 : CellCertificate where
  tauBall := tau0822
  contactCenter := center0822
  contactBall := contact0822
  work := work0822
  center_sq := center_sq0822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0822.1
  jac_ok := checks0822.2.1
  accepted := checks0822.2.2

def tau0823 : RatBall :=
  ⟨⟨-51/160, 27/160⟩, 3/320⟩
def center0823 : GaussianRat :=
  ⟨-219098349/1000000000, 53182749/500000000⟩
def contact0823 : RatBall := localContactBall tau0823 center0823
def work0823 : RoundedTauEval :=
  evalTau precision tau0823 contact0823 logTwoBall

theorem center_sq0823 : (center0823.re : ℝ)^2 +
    (center0823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0823 : work0823.theta.ok = true ∧
    work0823.jac.invOK = true ∧ acceptsUnitSq work0823.out = true := by
  norm_num [work0823, contact0823, tau0823, center0823, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0823 : CellCertificate where
  tauBall := tau0823
  contactCenter := center0823
  contactBall := contact0823
  work := work0823
  center_sq := center_sq0823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0823.1
  jac_ok := checks0823.2.1
  accepted := checks0823.2.2

def cells : List CellCertificate := [cell0816, cell0817, cell0818, cell0819, cell0820, cell0821, cell0822, cell0823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0102
