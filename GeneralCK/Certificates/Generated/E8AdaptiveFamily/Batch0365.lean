import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2920 : RatBall :=
  ⟨⟨21/640, -51/128⟩, 3/1280⟩
def center2920 : GaussianRat :=
  ⟨27204153/1000000000, -58521471/200000000⟩
def contact2920 : RatBall := localContactBall tau2920 center2920
def work2920 : RoundedTauEval :=
  evalTau precision tau2920 contact2920 logTwoBall

theorem center_sq2920 : (center2920.re : ℝ)^2 +
    (center2920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2920 : work2920.theta.ok = true ∧
    work2920.jac.invOK = true ∧ acceptsUnitSq work2920.out = true := by
  norm_num [work2920, contact2920, tau2920, center2920, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2920 : CellCertificate where
  tauBall := tau2920
  contactCenter := center2920
  contactBall := contact2920
  work := work2920
  center_sq := center_sq2920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2920.1
  jac_ok := checks2920.2.1
  accepted := checks2920.2.2

def tau2921 : RatBall :=
  ⟨⟨23/640, -51/128⟩, 3/1280⟩
def center2921 : GaussianRat :=
  ⟨5958069/200000000, -292519767/1000000000⟩
def contact2921 : RatBall := localContactBall tau2921 center2921
def work2921 : RoundedTauEval :=
  evalTau precision tau2921 contact2921 logTwoBall

theorem center_sq2921 : (center2921.re : ℝ)^2 +
    (center2921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2921 : work2921.theta.ok = true ∧
    work2921.jac.invOK = true ∧ acceptsUnitSq work2921.out = true := by
  norm_num [work2921, contact2921, tau2921, center2921, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2921 : CellCertificate where
  tauBall := tau2921
  contactCenter := center2921
  contactBall := contact2921
  work := work2921
  center_sq := center_sq2921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2921.1
  jac_ok := checks2921.2.1
  accepted := checks2921.2.2

def tau2922 : RatBall :=
  ⟨⟨21/640, -253/640⟩, 3/1280⟩
def center2922 : GaussianRat :=
  ⟨5424219/200000000, -290024499/1000000000⟩
def contact2922 : RatBall := localContactBall tau2922 center2922
def work2922 : RoundedTauEval :=
  evalTau precision tau2922 contact2922 logTwoBall

theorem center_sq2922 : (center2922.re : ℝ)^2 +
    (center2922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2922 : work2922.theta.ok = true ∧
    work2922.jac.invOK = true ∧ acceptsUnitSq work2922.out = true := by
  norm_num [work2922, contact2922, tau2922, center2922, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2922 : CellCertificate where
  tauBall := tau2922
  contactCenter := center2922
  contactBall := contact2922
  work := work2922
  center_sq := center_sq2922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2922.1
  jac_ok := checks2922.2.1
  accepted := checks2922.2.2

def tau2923 : RatBall :=
  ⟨⟨23/640, -253/640⟩, 3/1280⟩
def center2923 : GaussianRat :=
  ⟨14849721/500000000, -7248453/25000000⟩
def contact2923 : RatBall := localContactBall tau2923 center2923
def work2923 : RoundedTauEval :=
  evalTau precision tau2923 contact2923 logTwoBall

theorem center_sq2923 : (center2923.re : ℝ)^2 +
    (center2923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2923 : work2923.theta.ok = true ∧
    work2923.jac.invOK = true ∧ acceptsUnitSq work2923.out = true := by
  norm_num [work2923, contact2923, tau2923, center2923, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2923 : CellCertificate where
  tauBall := tau2923
  contactCenter := center2923
  contactBall := contact2923
  work := work2923
  center_sq := center_sq2923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2923.1
  jac_ok := checks2923.2.1
  accepted := checks2923.2.2

def tau2924 : RatBall :=
  ⟨⟨17/640, -251/640⟩, 3/1280⟩
def center2924 : GaussianRat :=
  ⟨21894677/1000000000, -143798363/500000000⟩
def contact2924 : RatBall := localContactBall tau2924 center2924
def work2924 : RoundedTauEval :=
  evalTau precision tau2924 contact2924 logTwoBall

theorem center_sq2924 : (center2924.re : ℝ)^2 +
    (center2924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2924 : work2924.theta.ok = true ∧
    work2924.jac.invOK = true ∧ acceptsUnitSq work2924.out = true := by
  norm_num [work2924, contact2924, tau2924, center2924, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2924 : CellCertificate where
  tauBall := tau2924
  contactCenter := center2924
  contactBall := contact2924
  work := work2924
  center_sq := center_sq2924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2924.1
  jac_ok := checks2924.2.1
  accepted := checks2924.2.2

def tau2925 : RatBall :=
  ⟨⟨19/640, -251/640⟩, 3/1280⟩
def center2925 : GaussianRat :=
  ⟨12233721/500000000, -287526937/1000000000⟩
def contact2925 : RatBall := localContactBall tau2925 center2925
def work2925 : RoundedTauEval :=
  evalTau precision tau2925 contact2925 logTwoBall

theorem center_sq2925 : (center2925.re : ℝ)^2 +
    (center2925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2925 : work2925.theta.ok = true ∧
    work2925.jac.invOK = true ∧ acceptsUnitSq work2925.out = true := by
  norm_num [work2925, contact2925, tau2925, center2925, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2925 : CellCertificate where
  tauBall := tau2925
  contactCenter := center2925
  contactBall := contact2925
  work := work2925
  center_sq := center_sq2925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2925.1
  jac_ok := checks2925.2.1
  accepted := checks2925.2.2

def tau2926 : RatBall :=
  ⟨⟨17/640, -249/640⟩, 3/1280⟩
def center2926 : GaussianRat :=
  ⟨10914601/500000000, -285027327/1000000000⟩
def contact2926 : RatBall := localContactBall tau2926 center2926
def work2926 : RoundedTauEval :=
  evalTau precision tau2926 contact2926 logTwoBall

theorem center_sq2926 : (center2926.re : ℝ)^2 +
    (center2926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2926 : work2926.theta.ok = true ∧
    work2926.jac.invOK = true ∧ acceptsUnitSq work2926.out = true := by
  norm_num [work2926, contact2926, tau2926, center2926, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2926 : CellCertificate where
  tauBall := tau2926
  contactCenter := center2926
  contactBall := contact2926
  work := work2926
  center_sq := center_sq2926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2926.1
  jac_ok := checks2926.2.1
  accepted := checks2926.2.2

def tau2927 : RatBall :=
  ⟨⟨19/640, -249/640⟩, 3/1280⟩
def center2927 : GaussianRat :=
  ⟨6098577/250000000, -142479251/500000000⟩
def contact2927 : RatBall := localContactBall tau2927 center2927
def work2927 : RoundedTauEval :=
  evalTau precision tau2927 contact2927 logTwoBall

theorem center_sq2927 : (center2927.re : ℝ)^2 +
    (center2927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2927]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2927 : work2927.theta.ok = true ∧
    work2927.jac.invOK = true ∧ acceptsUnitSq work2927.out = true := by
  norm_num [work2927, contact2927, tau2927, center2927, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2927 : CellCertificate where
  tauBall := tau2927
  contactCenter := center2927
  contactBall := contact2927
  work := work2927
  center_sq := center_sq2927
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2927.1
  jac_ok := checks2927.2.1
  accepted := checks2927.2.2

def cells : List CellCertificate := [cell2920, cell2921, cell2922, cell2923, cell2924, cell2925, cell2926, cell2927]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365
