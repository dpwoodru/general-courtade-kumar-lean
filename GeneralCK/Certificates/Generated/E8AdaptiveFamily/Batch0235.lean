import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1880 : RatBall :=
  ⟨⟨111/320, -13/64⟩, 3/640⟩
def center1880 : GaussianRat :=
  ⟨239515009/1000000000, -31500643/250000000⟩
def contact1880 : RatBall := localContactBall tau1880 center1880
def work1880 : RoundedTauEval :=
  evalTau precision tau1880 contact1880 logTwoBall

theorem center_sq1880 : (center1880.re : ℝ)^2 +
    (center1880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1880 : work1880.theta.ok = true ∧
    work1880.jac.invOK = true ∧ acceptsUnitSq work1880.out = true := by
  norm_num [work1880, contact1880, tau1880, center1880, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1880 : CellCertificate where
  tauBall := tau1880
  contactCenter := center1880
  contactBall := contact1880
  work := work1880
  center_sq := center_sq1880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1880.1
  jac_ok := checks1880.2.1
  accepted := checks1880.2.2

def tau1881 : RatBall :=
  ⟨⟨113/320, -61/320⟩, 3/640⟩
def center1881 : GaussianRat :=
  ⟨242396513/1000000000, -117649273/1000000000⟩
def contact1881 : RatBall := localContactBall tau1881 center1881
def work1881 : RoundedTauEval :=
  evalTau precision tau1881 contact1881 logTwoBall

theorem center_sq1881 : (center1881.re : ℝ)^2 +
    (center1881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1881 : work1881.theta.ok = true ∧
    work1881.jac.invOK = true ∧ acceptsUnitSq work1881.out = true := by
  norm_num [work1881, contact1881, tau1881, center1881, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1881 : CellCertificate where
  tauBall := tau1881
  contactCenter := center1881
  contactBall := contact1881
  work := work1881
  center_sq := center_sq1881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1881.1
  jac_ok := checks1881.2.1
  accepted := checks1881.2.2

def tau1882 : RatBall :=
  ⟨⟨-113/320, 61/320⟩, 3/640⟩
def center1882 : GaussianRat :=
  ⟨-242396513/1000000000, 117649273/1000000000⟩
def contact1882 : RatBall := localContactBall tau1882 center1882
def work1882 : RoundedTauEval :=
  evalTau precision tau1882 contact1882 logTwoBall

theorem center_sq1882 : (center1882.re : ℝ)^2 +
    (center1882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1882 : work1882.theta.ok = true ∧
    work1882.jac.invOK = true ∧ acceptsUnitSq work1882.out = true := by
  norm_num [work1882, contact1882, tau1882, center1882, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1882 : CellCertificate where
  tauBall := tau1882
  contactCenter := center1882
  contactBall := contact1882
  work := work1882
  center_sq := center_sq1882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1882.1
  jac_ok := checks1882.2.1
  accepted := checks1882.2.2

def tau1883 : RatBall :=
  ⟨⟨-111/320, 13/64⟩, 3/640⟩
def center1883 : GaussianRat :=
  ⟨-239515009/1000000000, 31500643/250000000⟩
def contact1883 : RatBall := localContactBall tau1883 center1883
def work1883 : RoundedTauEval :=
  evalTau precision tau1883 contact1883 logTwoBall

theorem center_sq1883 : (center1883.re : ℝ)^2 +
    (center1883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1883 : work1883.theta.ok = true ∧
    work1883.jac.invOK = true ∧ acceptsUnitSq work1883.out = true := by
  norm_num [work1883, contact1883, tau1883, center1883, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1883 : CellCertificate where
  tauBall := tau1883
  contactCenter := center1883
  contactBall := contact1883
  work := work1883
  center_sq := center_sq1883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1883.1
  jac_ok := checks1883.2.1
  accepted := checks1883.2.2

def tau1884 : RatBall :=
  ⟨⟨-109/320, 13/64⟩, 3/640⟩
def center1884 : GaussianRat :=
  ⟨-29446781/125000000, 63266993/500000000⟩
def contact1884 : RatBall := localContactBall tau1884 center1884
def work1884 : RoundedTauEval :=
  evalTau precision tau1884 contact1884 logTwoBall

theorem center_sq1884 : (center1884.re : ℝ)^2 +
    (center1884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1884 : work1884.theta.ok = true ∧
    work1884.jac.invOK = true ∧ acceptsUnitSq work1884.out = true := by
  norm_num [work1884, contact1884, tau1884, center1884, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1884 : CellCertificate where
  tauBall := tau1884
  contactCenter := center1884
  contactBall := contact1884
  work := work1884
  center_sq := center_sq1884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1884.1
  jac_ok := checks1884.2.1
  accepted := checks1884.2.2

def tau1885 : RatBall :=
  ⟨⟨-109/320, 67/320⟩, 3/640⟩
def center1885 : GaussianRat :=
  ⟨-236112247/1000000000, 65243249/500000000⟩
def contact1885 : RatBall := localContactBall tau1885 center1885
def work1885 : RoundedTauEval :=
  evalTau precision tau1885 contact1885 logTwoBall

theorem center_sq1885 : (center1885.re : ℝ)^2 +
    (center1885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1885 : work1885.theta.ok = true ∧
    work1885.jac.invOK = true ∧ acceptsUnitSq work1885.out = true := by
  norm_num [work1885, contact1885, tau1885, center1885, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1885 : CellCertificate where
  tauBall := tau1885
  contactCenter := center1885
  contactBall := contact1885
  work := work1885
  center_sq := center_sq1885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1885.1
  jac_ok := checks1885.2.1
  accepted := checks1885.2.2

def tau1886 : RatBall :=
  ⟨⟨-109/320, 69/320⟩, 3/640⟩
def center1886 : GaussianRat :=
  ⟨-236668663/1000000000, 134444337/1000000000⟩
def contact1886 : RatBall := localContactBall tau1886 center1886
def work1886 : RoundedTauEval :=
  evalTau precision tau1886 contact1886 logTwoBall

theorem center_sq1886 : (center1886.re : ℝ)^2 +
    (center1886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1886 : work1886.theta.ok = true ∧
    work1886.jac.invOK = true ∧ acceptsUnitSq work1886.out = true := by
  norm_num [work1886, contact1886, tau1886, center1886, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1886 : CellCertificate where
  tauBall := tau1886
  contactCenter := center1886
  contactBall := contact1886
  work := work1886
  center_sq := center_sq1886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1886.1
  jac_ok := checks1886.2.1
  accepted := checks1886.2.2

def tau1887 : RatBall :=
  ⟨⟨-107/320, 69/320⟩, 3/640⟩
def center1887 : GaussianRat :=
  ⟨-58174707/250000000, 67503627/500000000⟩
def contact1887 : RatBall := localContactBall tau1887 center1887
def work1887 : RoundedTauEval :=
  evalTau precision tau1887 contact1887 logTwoBall

theorem center_sq1887 : (center1887.re : ℝ)^2 +
    (center1887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1887]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1887 : work1887.theta.ok = true ∧
    work1887.jac.invOK = true ∧ acceptsUnitSq work1887.out = true := by
  norm_num [work1887, contact1887, tau1887, center1887, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1887 : CellCertificate where
  tauBall := tau1887
  contactCenter := center1887
  contactBall := contact1887
  work := work1887
  center_sq := center_sq1887
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1887.1
  jac_ok := checks1887.2.1
  accepted := checks1887.2.2

def cells : List CellCertificate := [cell1880, cell1881, cell1882, cell1883, cell1884, cell1885, cell1886, cell1887]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235
