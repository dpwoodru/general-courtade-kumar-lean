import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2816 : RatBall :=
  ⟨⟨-31/640, -251/640⟩, 3/1280⟩
def center2816 : GaussianRat :=
  ⟨-4984851/125000000, -286946953/1000000000⟩
def contact2816 : RatBall := localContactBall tau2816 center2816
def work2816 : RoundedTauEval :=
  evalTau precision tau2816 contact2816 logTwoBall

theorem center_sq2816 : (center2816.re : ℝ)^2 +
    (center2816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2816 : work2816.theta.ok = true ∧
    work2816.jac.invOK = true ∧ acceptsUnitSq work2816.out = true := by
  norm_num [work2816, contact2816, tau2816, center2816, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2816 : CellCertificate where
  tauBall := tau2816
  contactCenter := center2816
  contactBall := contact2816
  work := work2816
  center_sq := center_sq2816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2816.1
  jac_ok := checks2816.2.1
  accepted := checks2816.2.2

def tau2817 : RatBall :=
  ⟨⟨-29/640, -251/640⟩, 3/1280⟩
def center2817 : GaussianRat :=
  ⟨-1865689/50000000, -287062723/1000000000⟩
def contact2817 : RatBall := localContactBall tau2817 center2817
def work2817 : RoundedTauEval :=
  evalTau precision tau2817 contact2817 logTwoBall

theorem center_sq2817 : (center2817.re : ℝ)^2 +
    (center2817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2817 : work2817.theta.ok = true ∧
    work2817.jac.invOK = true ∧ acceptsUnitSq work2817.out = true := by
  norm_num [work2817, contact2817, tau2817, center2817, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2817 : CellCertificate where
  tauBall := tau2817
  contactCenter := center2817
  contactBall := contact2817
  work := work2817
  center_sq := center_sq2817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2817.1
  jac_ok := checks2817.2.1
  accepted := checks2817.2.2

def tau2818 : RatBall :=
  ⟨⟨-31/640, -249/640⟩, 3/1280⟩
def center2818 : GaussianRat :=
  ⟨-19880031/500000000, -56877303/200000000⟩
def contact2818 : RatBall := localContactBall tau2818 center2818
def work2818 : RoundedTauEval :=
  evalTau precision tau2818 contact2818 logTwoBall

theorem center_sq2818 : (center2818.re : ℝ)^2 +
    (center2818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2818 : work2818.theta.ok = true ∧
    work2818.jac.invOK = true ∧ acceptsUnitSq work2818.out = true := by
  norm_num [work2818, contact2818, tau2818, center2818, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2818 : CellCertificate where
  tauBall := tau2818
  contactCenter := center2818
  contactBall := contact2818
  work := work2818
  center_sq := center_sq2818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2818.1
  jac_ok := checks2818.2.1
  accepted := checks2818.2.2

def tau2819 : RatBall :=
  ⟨⟨-29/640, -249/640⟩, 3/1280⟩
def center2819 : GaussianRat :=
  ⟨-37202587/1000000000, -284500691/1000000000⟩
def contact2819 : RatBall := localContactBall tau2819 center2819
def work2819 : RoundedTauEval :=
  evalTau precision tau2819 contact2819 logTwoBall

theorem center_sq2819 : (center2819.re : ℝ)^2 +
    (center2819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2819 : work2819.theta.ok = true ∧
    work2819.jac.invOK = true ∧ acceptsUnitSq work2819.out = true := by
  norm_num [work2819, contact2819, tau2819, center2819, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2819 : CellCertificate where
  tauBall := tau2819
  contactCenter := center2819
  contactBall := contact2819
  work := work2819
  center_sq := center_sq2819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2819.1
  jac_ok := checks2819.2.1
  accepted := checks2819.2.2

def tau2820 : RatBall :=
  ⟨⟨-27/640, -251/640⟩, 3/1280⟩
def center2820 : GaussianRat :=
  ⟨-17373599/500000000, -287170877/1000000000⟩
def contact2820 : RatBall := localContactBall tau2820 center2820
def work2820 : RoundedTauEval :=
  evalTau precision tau2820 contact2820 logTwoBall

theorem center_sq2820 : (center2820.re : ℝ)^2 +
    (center2820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2820 : work2820.theta.ok = true ∧
    work2820.jac.invOK = true ∧ acceptsUnitSq work2820.out = true := by
  norm_num [work2820, contact2820, tau2820, center2820, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2820 : CellCertificate where
  tauBall := tau2820
  contactCenter := center2820
  contactBall := contact2820
  work := work2820
  center_sq := center_sq2820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2820.1
  jac_ok := checks2820.2.1
  accepted := checks2820.2.2

def tau2821 : RatBall :=
  ⟨⟨-5/128, -251/640⟩, 3/1280⟩
def center2821 : GaussianRat :=
  ⟨-32179167/1000000000, -57454279/200000000⟩
def contact2821 : RatBall := localContactBall tau2821 center2821
def work2821 : RoundedTauEval :=
  evalTau precision tau2821 contact2821 logTwoBall

theorem center_sq2821 : (center2821.re : ℝ)^2 +
    (center2821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2821 : work2821.theta.ok = true ∧
    work2821.jac.invOK = true ∧ acceptsUnitSq work2821.out = true := by
  norm_num [work2821, contact2821, tau2821, center2821, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2821 : CellCertificate where
  tauBall := tau2821
  contactCenter := center2821
  contactBall := contact2821
  work := work2821
  center_sq := center_sq2821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2821.1
  jac_ok := checks2821.2.1
  accepted := checks2821.2.2

def tau2822 : RatBall :=
  ⟨⟨-27/640, -249/640⟩, 3/1280⟩
def center2822 : GaussianRat :=
  ⟨-34643579/1000000000, -56921471/200000000⟩
def contact2822 : RatBall := localContactBall tau2822 center2822
def work2822 : RoundedTauEval :=
  evalTau precision tau2822 contact2822 logTwoBall

theorem center_sq2822 : (center2822.re : ℝ)^2 +
    (center2822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2822 : work2822.theta.ok = true ∧
    work2822.jac.invOK = true ∧ acceptsUnitSq work2822.out = true := by
  norm_num [work2822, contact2822, tau2822, center2822, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2822 : CellCertificate where
  tauBall := tau2822
  contactCenter := center2822
  contactBall := contact2822
  work := work2822
  center_sq := center_sq2822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2822.1
  jac_ok := checks2822.2.1
  accepted := checks2822.2.2

def tau2823 : RatBall :=
  ⟨⟨-5/128, -249/640⟩, 3/1280⟩
def center2823 : GaussianRat :=
  ⟨-32083143/1000000000, -142353243/500000000⟩
def contact2823 : RatBall := localContactBall tau2823 center2823
def work2823 : RoundedTauEval :=
  evalTau precision tau2823 contact2823 logTwoBall

theorem center_sq2823 : (center2823.re : ℝ)^2 +
    (center2823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2823 : work2823.theta.ok = true ∧
    work2823.jac.invOK = true ∧ acceptsUnitSq work2823.out = true := by
  norm_num [work2823, contact2823, tau2823, center2823, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2823 : CellCertificate where
  tauBall := tau2823
  contactCenter := center2823
  contactBall := contact2823
  work := work2823
  center_sq := center_sq2823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2823.1
  jac_ok := checks2823.2.1
  accepted := checks2823.2.2

def cells : List CellCertificate := [cell2816, cell2817, cell2818, cell2819, cell2820, cell2821, cell2822, cell2823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352
