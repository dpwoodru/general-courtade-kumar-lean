import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2888 : RatBall :=
  ⟨⟨1/128, -51/128⟩, 3/1280⟩
def center2888 : GaussianRat :=
  ⟨6481999/1000000000, -146511137/500000000⟩
def contact2888 : RatBall := localContactBall tau2888 center2888
def work2888 : RoundedTauEval :=
  evalTau precision tau2888 contact2888 logTwoBall

theorem center_sq2888 : (center2888.re : ℝ)^2 +
    (center2888.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2888 : work2888.theta.ok = true ∧
    work2888.jac.invOK = true ∧ acceptsUnitSq work2888.out = true := by
  norm_num [work2888, contact2888, tau2888, center2888, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2888 : CellCertificate where
  tauBall := tau2888
  contactCenter := center2888
  contactBall := contact2888
  work := work2888
  center_sq := center_sq2888
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2888.1
  jac_ok := checks2888.2.1
  accepted := checks2888.2.2

def tau2889 : RatBall :=
  ⟨⟨7/640, -51/128⟩, 3/1280⟩
def center2889 : GaussianRat :=
  ⟨9074409/1000000000, -292998297/1000000000⟩
def contact2889 : RatBall := localContactBall tau2889 center2889
def work2889 : RoundedTauEval :=
  evalTau precision tau2889 contact2889 logTwoBall

theorem center_sq2889 : (center2889.re : ℝ)^2 +
    (center2889.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2889]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2889 : work2889.theta.ok = true ∧
    work2889.jac.invOK = true ∧ acceptsUnitSq work2889.out = true := by
  norm_num [work2889, contact2889, tau2889, center2889, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2889 : CellCertificate where
  tauBall := tau2889
  contactCenter := center2889
  contactBall := contact2889
  work := work2889
  center_sq := center_sq2889
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2889.1
  jac_ok := checks2889.2.1
  accepted := checks2889.2.2

def tau2890 : RatBall :=
  ⟨⟨1/128, -253/640⟩, 3/1280⟩
def center2890 : GaussianRat :=
  ⟨1292431/200000000, -290433683/1000000000⟩
def contact2890 : RatBall := localContactBall tau2890 center2890
def work2890 : RoundedTauEval :=
  evalTau precision tau2890 contact2890 logTwoBall

theorem center_sq2890 : (center2890.re : ℝ)^2 +
    (center2890.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2890]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2890 : work2890.theta.ok = true ∧
    work2890.jac.invOK = true ∧ acceptsUnitSq work2890.out = true := by
  norm_num [work2890, contact2890, tau2890, center2890, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2890 : CellCertificate where
  tauBall := tau2890
  contactCenter := center2890
  contactBall := contact2890
  work := work2890
  center_sq := center_sq2890
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2890.1
  jac_ok := checks2890.2.1
  accepted := checks2890.2.2

def tau2891 : RatBall :=
  ⟨⟨7/640, -253/640⟩, 3/1280⟩
def center2891 : GaussianRat :=
  ⟨9046633/1000000000, -145205019/500000000⟩
def contact2891 : RatBall := localContactBall tau2891 center2891
def work2891 : RoundedTauEval :=
  evalTau precision tau2891 contact2891 logTwoBall

theorem center_sq2891 : (center2891.re : ℝ)^2 +
    (center2891.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2891]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2891 : work2891.theta.ok = true ∧
    work2891.jac.invOK = true ∧ acceptsUnitSq work2891.out = true := by
  norm_num [work2891, contact2891, tau2891, center2891, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2891 : CellCertificate where
  tauBall := tau2891
  contactCenter := center2891
  contactBall := contact2891
  work := work2891
  center_sq := center_sq2891
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2891.1
  jac_ok := checks2891.2.1
  accepted := checks2891.2.2

def tau2892 : RatBall :=
  ⟨⟨1/640, -251/640⟩, 3/1280⟩
def center2892 : GaussianRat :=
  ⟨1288571/1000000000, -287876293/1000000000⟩
def contact2892 : RatBall := localContactBall tau2892 center2892
def work2892 : RoundedTauEval :=
  evalTau precision tau2892 contact2892 logTwoBall

theorem center_sq2892 : (center2892.re : ℝ)^2 +
    (center2892.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2892]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2892 : work2892.theta.ok = true ∧
    work2892.jac.invOK = true ∧ acceptsUnitSq work2892.out = true := by
  norm_num [work2892, contact2892, tau2892, center2892, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2892 : CellCertificate where
  tauBall := tau2892
  contactCenter := center2892
  contactBall := contact2892
  work := work2892
  center_sq := center_sq2892
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2892.1
  jac_ok := checks2892.2.1
  accepted := checks2892.2.2

def tau2893 : RatBall :=
  ⟨⟨3/640, -251/640⟩, 3/1280⟩
def center2893 : GaussianRat :=
  ⟨193283/50000000, -143934259/500000000⟩
def contact2893 : RatBall := localContactBall tau2893 center2893
def work2893 : RoundedTauEval :=
  evalTau precision tau2893 contact2893 logTwoBall

theorem center_sq2893 : (center2893.re : ℝ)^2 +
    (center2893.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2893]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2893 : work2893.theta.ok = true ∧
    work2893.jac.invOK = true ∧ acceptsUnitSq work2893.out = true := by
  norm_num [work2893, contact2893, tau2893, center2893, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2893 : CellCertificate where
  tauBall := tau2893
  contactCenter := center2893
  contactBall := contact2893
  work := work2893
  center_sq := center_sq2893
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2893.1
  jac_ok := checks2893.2.1
  accepted := checks2893.2.2

def tau2894 : RatBall :=
  ⟨⟨1/640, -249/640⟩, 3/1280⟩
def center2894 : GaussianRat :=
  ⟨1284711/1000000000, -285303029/1000000000⟩
def contact2894 : RatBall := localContactBall tau2894 center2894
def work2894 : RoundedTauEval :=
  evalTau precision tau2894 contact2894 logTwoBall

theorem center_sq2894 : (center2894.re : ℝ)^2 +
    (center2894.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2894]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2894 : work2894.theta.ok = true ∧
    work2894.jac.invOK = true ∧ acceptsUnitSq work2894.out = true := by
  norm_num [work2894, contact2894, tau2894, center2894, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2894 : CellCertificate where
  tauBall := tau2894
  contactCenter := center2894
  contactBall := contact2894
  work := work2894
  center_sq := center_sq2894
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2894.1
  jac_ok := checks2894.2.1
  accepted := checks2894.2.2

def tau2895 : RatBall :=
  ⟨⟨3/640, -249/640⟩, 3/1280⟩
def center2895 : GaussianRat :=
  ⟨3854079/1000000000, -142647681/500000000⟩
def contact2895 : RatBall := localContactBall tau2895 center2895
def work2895 : RoundedTauEval :=
  evalTau precision tau2895 contact2895 logTwoBall

theorem center_sq2895 : (center2895.re : ℝ)^2 +
    (center2895.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2895]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2895 : work2895.theta.ok = true ∧
    work2895.jac.invOK = true ∧ acceptsUnitSq work2895.out = true := by
  norm_num [work2895, contact2895, tau2895, center2895, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2895 : CellCertificate where
  tauBall := tau2895
  contactCenter := center2895
  contactBall := contact2895
  work := work2895
  center_sq := center_sq2895
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2895.1
  jac_ok := checks2895.2.1
  accepted := checks2895.2.2

def cells : List CellCertificate := [cell2888, cell2889, cell2890, cell2891, cell2892, cell2893, cell2894, cell2895]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361
