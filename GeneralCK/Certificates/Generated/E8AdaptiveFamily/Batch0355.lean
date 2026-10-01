import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2840 : RatBall :=
  ⟨⟨-31/640, -247/640⟩, 3/1280⟩
def center2840 : GaussianRat :=
  ⟨-4955369/125000000, -8807299/31250000⟩
def contact2840 : RatBall := localContactBall tau2840 center2840
def work2840 : RoundedTauEval :=
  evalTau precision tau2840 contact2840 logTwoBall

theorem center_sq2840 : (center2840.re : ℝ)^2 +
    (center2840.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2840 : work2840.theta.ok = true ∧
    work2840.jac.invOK = true ∧ acceptsUnitSq work2840.out = true := by
  norm_num [work2840, contact2840, tau2840, center2840, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2840 : CellCertificate where
  tauBall := tau2840
  contactCenter := center2840
  contactBall := contact2840
  work := work2840
  center_sq := center_sq2840
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2840.1
  jac_ok := checks2840.2.1
  accepted := checks2840.2.2

def tau2841 : RatBall :=
  ⟨⟨-29/640, -247/640⟩, 3/1280⟩
def center2841 : GaussianRat :=
  ⟨-18546463/500000000, -281946171/1000000000⟩
def contact2841 : RatBall := localContactBall tau2841 center2841
def work2841 : RoundedTauEval :=
  evalTau precision tau2841 contact2841 logTwoBall

theorem center_sq2841 : (center2841.re : ℝ)^2 +
    (center2841.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2841]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2841 : work2841.theta.ok = true ∧
    work2841.jac.invOK = true ∧ acceptsUnitSq work2841.out = true := by
  norm_num [work2841, contact2841, tau2841, center2841, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2841 : CellCertificate where
  tauBall := tau2841
  contactCenter := center2841
  contactBall := contact2841
  work := work2841
  center_sq := center_sq2841
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2841.1
  jac_ok := checks2841.2.1
  accepted := checks2841.2.2

def tau2842 : RatBall :=
  ⟨⟨-31/640, -49/128⟩, 3/1280⟩
def center2842 : GaussianRat :=
  ⟨-19763727/500000000, -279288009/1000000000⟩
def contact2842 : RatBall := localContactBall tau2842 center2842
def work2842 : RoundedTauEval :=
  evalTau precision tau2842 contact2842 logTwoBall

theorem center_sq2842 : (center2842.re : ℝ)^2 +
    (center2842.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2842]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2842 : work2842.theta.ok = true ∧
    work2842.jac.invOK = true ∧ acceptsUnitSq work2842.out = true := by
  norm_num [work2842, contact2842, tau2842, center2842, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2842 : CellCertificate where
  tauBall := tau2842
  contactCenter := center2842
  contactBall := contact2842
  work := work2842
  center_sq := center_sq2842
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2842.1
  jac_ok := checks2842.2.1
  accepted := checks2842.2.2

def tau2843 : RatBall :=
  ⟨⟨-29/640, -49/128⟩, 3/1280⟩
def center2843 : GaussianRat :=
  ⟨-4623097/125000000, -13969953/50000000⟩
def contact2843 : RatBall := localContactBall tau2843 center2843
def work2843 : RoundedTauEval :=
  evalTau precision tau2843 contact2843 logTwoBall

theorem center_sq2843 : (center2843.re : ℝ)^2 +
    (center2843.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2843]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2843 : work2843.theta.ok = true ∧
    work2843.jac.invOK = true ∧ acceptsUnitSq work2843.out = true := by
  norm_num [work2843, contact2843, tau2843, center2843, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2843 : CellCertificate where
  tauBall := tau2843
  contactCenter := center2843
  contactBall := contact2843
  work := work2843
  center_sq := center_sq2843
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2843.1
  jac_ok := checks2843.2.1
  accepted := checks2843.2.2

def tau2844 : RatBall :=
  ⟨⟨-27/640, -247/640⟩, 3/1280⟩
def center2844 : GaussianRat :=
  ⟨-34541389/1000000000, -56410273/200000000⟩
def contact2844 : RatBall := localContactBall tau2844 center2844
def work2844 : RoundedTauEval :=
  evalTau precision tau2844 contact2844 logTwoBall

theorem center_sq2844 : (center2844.re : ℝ)^2 +
    (center2844.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2844]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2844 : work2844.theta.ok = true ∧
    work2844.jac.invOK = true ∧ acceptsUnitSq work2844.out = true := by
  norm_num [work2844, contact2844, tau2844, center2844, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2844 : CellCertificate where
  tauBall := tau2844
  contactCenter := center2844
  contactBall := contact2844
  work := work2844
  center_sq := center_sq2844
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2844.1
  jac_ok := checks2844.2.1
  accepted := checks2844.2.2

def tau2845 : RatBall :=
  ⟨⟨-5/128, -247/640⟩, 3/1280⟩
def center2845 : GaussianRat :=
  ⟨-7997111/250000000, -282149129/1000000000⟩
def contact2845 : RatBall := localContactBall tau2845 center2845
def work2845 : RoundedTauEval :=
  evalTau precision tau2845 contact2845 logTwoBall

theorem center_sq2845 : (center2845.re : ℝ)^2 +
    (center2845.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2845]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2845 : work2845.theta.ok = true ∧
    work2845.jac.invOK = true ∧ acceptsUnitSq work2845.out = true := by
  norm_num [work2845, contact2845, tau2845, center2845, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2845 : CellCertificate where
  tauBall := tau2845
  contactCenter := center2845
  contactBall := contact2845
  work := work2845
  center_sq := center_sq2845
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2845.1
  jac_ok := checks2845.2.1
  accepted := checks2845.2.2

def tau2846 : RatBall :=
  ⟨⟨-27/640, -49/128⟩, 3/1280⟩
def center2846 : GaussianRat :=
  ⟨-1076269/31250000, -69875701/250000000⟩
def contact2846 : RatBall := localContactBall tau2846 center2846
def work2846 : RoundedTauEval :=
  evalTau precision tau2846 contact2846 logTwoBall

theorem center_sq2846 : (center2846.re : ℝ)^2 +
    (center2846.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2846]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2846 : work2846.theta.ok = true ∧
    work2846.jac.invOK = true ∧ acceptsUnitSq work2846.out = true := by
  norm_num [work2846, contact2846, tau2846, center2846, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2846 : CellCertificate where
  tauBall := tau2846
  contactCenter := center2846
  contactBall := contact2846
  work := work2846
  center_sq := center_sq2846
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2846.1
  jac_ok := checks2846.2.1
  accepted := checks2846.2.2

def tau2847 : RatBall :=
  ⟨⟨-5/128, -49/128⟩, 3/1280⟩
def center2847 : GaussianRat :=
  ⟨-31895051/1000000000, -13979961/50000000⟩
def contact2847 : RatBall := localContactBall tau2847 center2847
def work2847 : RoundedTauEval :=
  evalTau precision tau2847 contact2847 logTwoBall

theorem center_sq2847 : (center2847.re : ℝ)^2 +
    (center2847.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2847]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2847 : work2847.theta.ok = true ∧
    work2847.jac.invOK = true ∧ acceptsUnitSq work2847.out = true := by
  norm_num [work2847, contact2847, tau2847, center2847, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2847 : CellCertificate where
  tauBall := tau2847
  contactCenter := center2847
  contactBall := contact2847
  work := work2847
  center_sq := center_sq2847
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2847.1
  jac_ok := checks2847.2.1
  accepted := checks2847.2.2

def cells : List CellCertificate := [cell2840, cell2841, cell2842, cell2843, cell2844, cell2845, cell2846, cell2847]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355
