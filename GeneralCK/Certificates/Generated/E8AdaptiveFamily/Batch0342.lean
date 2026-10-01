import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2736 : RatBall :=
  ⟨⟨-61/640, -49/128⟩, 3/1280⟩
def center2736 : GaussianRat :=
  ⟨-3096871/40000000, -138381321/500000000⟩
def contact2736 : RatBall := localContactBall tau2736 center2736
def work2736 : RoundedTauEval :=
  evalTau precision tau2736 contact2736 logTwoBall

theorem center_sq2736 : (center2736.re : ℝ)^2 +
    (center2736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2736 : work2736.theta.ok = true ∧
    work2736.jac.invOK = true ∧ acceptsUnitSq work2736.out = true := by
  norm_num [work2736, contact2736, tau2736, center2736, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2736 : CellCertificate where
  tauBall := tau2736
  contactCenter := center2736
  contactBall := contact2736
  work := work2736
  center_sq := center_sq2736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2736.1
  jac_ok := checks2736.2.1
  accepted := checks2736.2.2

def tau2737 : RatBall :=
  ⟨⟨-59/640, -247/640⟩, 3/1280⟩
def center2737 : GaussianRat :=
  ⟨-75128671/1000000000, -55898717/200000000⟩
def contact2737 : RatBall := localContactBall tau2737 center2737
def work2737 : RoundedTauEval :=
  evalTau precision tau2737 contact2737 logTwoBall

theorem center_sq2737 : (center2737.re : ℝ)^2 +
    (center2737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2737 : work2737.theta.ok = true ∧
    work2737.jac.invOK = true ∧ acceptsUnitSq work2737.out = true := by
  norm_num [work2737, contact2737, tau2737, center2737, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2737 : CellCertificate where
  tauBall := tau2737
  contactCenter := center2737
  contactBall := contact2737
  work := work2737
  center_sq := center_sq2737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2737.1
  jac_ok := checks2737.2.1
  accepted := checks2737.2.2

def tau2738 : RatBall :=
  ⟨⟨-57/640, -247/640⟩, 3/1280⟩
def center2738 : GaussianRat :=
  ⟨-72610227/1000000000, -34963383/125000000⟩
def contact2738 : RatBall := localContactBall tau2738 center2738
def work2738 : RoundedTauEval :=
  evalTau precision tau2738 contact2738 logTwoBall

theorem center_sq2738 : (center2738.re : ℝ)^2 +
    (center2738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2738 : work2738.theta.ok = true ∧
    work2738.jac.invOK = true ∧ acceptsUnitSq work2738.out = true := by
  norm_num [work2738, contact2738, tau2738, center2738, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2738 : CellCertificate where
  tauBall := tau2738
  contactCenter := center2738
  contactBall := contact2738
  work := work2738
  center_sq := center_sq2738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2738.1
  jac_ok := checks2738.2.1
  accepted := checks2738.2.2

def tau2739 : RatBall :=
  ⟨⟨-59/640, -49/128⟩, 3/1280⟩
def center2739 : GaussianRat :=
  ⟨-7491319/100000000, -34622509/125000000⟩
def contact2739 : RatBall := localContactBall tau2739 center2739
def work2739 : RoundedTauEval :=
  evalTau precision tau2739 contact2739 logTwoBall

theorem center_sq2739 : (center2739.re : ℝ)^2 +
    (center2739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2739 : work2739.theta.ok = true ∧
    work2739.jac.invOK = true ∧ acceptsUnitSq work2739.out = true := by
  norm_num [work2739, contact2739, tau2739, center2739, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2739 : CellCertificate where
  tauBall := tau2739
  contactCenter := center2739
  contactBall := contact2739
  work := work2739
  center_sq := center_sq2739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2739.1
  jac_ok := checks2739.2.1
  accepted := checks2739.2.2

def tau2740 : RatBall :=
  ⟨⟨-57/640, -49/128⟩, 3/1280⟩
def center2740 : GaussianRat :=
  ⟨-7240167/100000000, -277190643/1000000000⟩
def contact2740 : RatBall := localContactBall tau2740 center2740
def work2740 : RoundedTauEval :=
  evalTau precision tau2740 contact2740 logTwoBall

theorem center_sq2740 : (center2740.re : ℝ)^2 +
    (center2740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2740 : work2740.theta.ok = true ∧
    work2740.jac.invOK = true ∧ acceptsUnitSq work2740.out = true := by
  norm_num [work2740, contact2740, tau2740, center2740, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2740 : CellCertificate where
  tauBall := tau2740
  contactCenter := center2740
  contactBall := contact2740
  work := work2740
  center_sq := center_sq2740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2740.1
  jac_ok := checks2740.2.1
  accepted := checks2740.2.2

def tau2741 : RatBall :=
  ⟨⟨-63/640, -243/640⟩, 3/1280⟩
def center2741 : GaussianRat :=
  ⟨-79701237/1000000000, -274037749/1000000000⟩
def contact2741 : RatBall := localContactBall tau2741 center2741
def work2741 : RoundedTauEval :=
  evalTau precision tau2741 contact2741 logTwoBall

theorem center_sq2741 : (center2741.re : ℝ)^2 +
    (center2741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2741 : work2741.theta.ok = true ∧
    work2741.jac.invOK = true ∧ acceptsUnitSq work2741.out = true := by
  norm_num [work2741, contact2741, tau2741, center2741, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2741 : CellCertificate where
  tauBall := tau2741
  contactCenter := center2741
  contactBall := contact2741
  work := work2741
  center_sq := center_sq2741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2741.1
  jac_ok := checks2741.2.1
  accepted := checks2741.2.2

def tau2742 : RatBall :=
  ⟨⟨-61/640, -243/640⟩, 3/1280⟩
def center2742 : GaussianRat :=
  ⟨-77202433/1000000000, -5485179/20000000⟩
def contact2742 : RatBall := localContactBall tau2742 center2742
def work2742 : RoundedTauEval :=
  evalTau precision tau2742 contact2742 logTwoBall

theorem center_sq2742 : (center2742.re : ℝ)^2 +
    (center2742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2742 : work2742.theta.ok = true ∧
    work2742.jac.invOK = true ∧ acceptsUnitSq work2742.out = true := by
  norm_num [work2742, contact2742, tau2742, center2742, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2742 : CellCertificate where
  tauBall := tau2742
  contactCenter := center2742
  contactBall := contact2742
  work := work2742
  center_sq := center_sq2742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2742.1
  jac_ok := checks2742.2.1
  accepted := checks2742.2.2

def tau2743 : RatBall :=
  ⟨⟨-63/640, -241/640⟩, 3/1280⟩
def center2743 : GaussianRat :=
  ⟨-15895643/200000000, -271543799/1000000000⟩
def contact2743 : RatBall := localContactBall tau2743 center2743
def work2743 : RoundedTauEval :=
  evalTau precision tau2743 contact2743 logTwoBall

theorem center_sq2743 : (center2743.re : ℝ)^2 +
    (center2743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2743 : work2743.theta.ok = true ∧
    work2743.jac.invOK = true ∧ acceptsUnitSq work2743.out = true := by
  norm_num [work2743, contact2743, tau2743, center2743, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2743 : CellCertificate where
  tauBall := tau2743
  contactCenter := center2743
  contactBall := contact2743
  work := work2743
  center_sq := center_sq2743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2743.1
  jac_ok := checks2743.2.1
  accepted := checks2743.2.2

def cells : List CellCertificate := [cell2736, cell2737, cell2738, cell2739, cell2740, cell2741, cell2742, cell2743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342
