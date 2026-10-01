import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1888 : RatBall :=
  ⟨⟨-21/64, 69/320⟩, 3/640⟩
def center1888 : GaussianRat :=
  ⟨-57177633/250000000, 13556449/100000000⟩
def contact1888 : RatBall := localContactBall tau1888 center1888
def work1888 : RoundedTauEval :=
  evalTau precision tau1888 contact1888 logTwoBall

theorem center_sq1888 : (center1888.re : ℝ)^2 +
    (center1888.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1888 : work1888.theta.ok = true ∧
    work1888.jac.invOK = true ∧ acceptsUnitSq work1888.out = true := by
  norm_num [work1888, contact1888, tau1888, center1888, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1888 : CellCertificate where
  tauBall := tau1888
  contactCenter := center1888
  contactBall := contact1888
  work := work1888
  center_sq := center_sq1888
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1888.1
  jac_ok := checks1888.2.1
  accepted := checks1888.2.2

def tau1889 : RatBall :=
  ⟨⟨-107/320, 71/320⟩, 3/640⟩
def center1889 : GaussianRat :=
  ⟨-58317051/250000000, 34747303/250000000⟩
def contact1889 : RatBall := localContactBall tau1889 center1889
def work1889 : RoundedTauEval :=
  evalTau precision tau1889 contact1889 logTwoBall

theorem center_sq1889 : (center1889.re : ℝ)^2 +
    (center1889.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1889]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1889 : work1889.theta.ok = true ∧
    work1889.jac.invOK = true ∧ acceptsUnitSq work1889.out = true := by
  norm_num [work1889, contact1889, tau1889, center1889, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1889 : CellCertificate where
  tauBall := tau1889
  contactCenter := center1889
  contactBall := contact1889
  work := work1889
  center_sq := center_sq1889
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1889.1
  jac_ok := checks1889.2.1
  accepted := checks1889.2.2

def tau1890 : RatBall :=
  ⟨⟨-21/64, 71/320⟩, 3/640⟩
def center1890 : GaussianRat :=
  ⟨-45854809/200000000, 139564933/1000000000⟩
def contact1890 : RatBall := localContactBall tau1890 center1890
def work1890 : RoundedTauEval :=
  evalTau precision tau1890 contact1890 logTwoBall

theorem center_sq1890 : (center1890.re : ℝ)^2 +
    (center1890.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1890]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1890 : work1890.theta.ok = true ∧
    work1890.jac.invOK = true ∧ acceptsUnitSq work1890.out = true := by
  norm_num [work1890, contact1890, tau1890, center1890, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1890 : CellCertificate where
  tauBall := tau1890
  contactCenter := center1890
  contactBall := contact1890
  work := work1890
  center_sq := center_sq1890
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1890.1
  jac_ok := checks1890.2.1
  accepted := checks1890.2.2

def tau1891 : RatBall :=
  ⟨⟨-21/64, 73/320⟩, 3/640⟩
def center1891 : GaussianRat :=
  ⟨-229856067/1000000000, 5742857/40000000⟩
def contact1891 : RatBall := localContactBall tau1891 center1891
def work1891 : RoundedTauEval :=
  evalTau precision tau1891 contact1891 logTwoBall

theorem center_sq1891 : (center1891.re : ℝ)^2 +
    (center1891.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1891]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1891 : work1891.theta.ok = true ∧
    work1891.jac.invOK = true ∧ acceptsUnitSq work1891.out = true := by
  norm_num [work1891, contact1891, tau1891, center1891, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1891 : CellCertificate where
  tauBall := tau1891
  contactCenter := center1891
  contactBall := contact1891
  work := work1891
  center_sq := center_sq1891
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1891.1
  jac_ok := checks1891.2.1
  accepted := checks1891.2.2

def tau1892 : RatBall :=
  ⟨⟨-21/64, 15/64⟩, 3/640⟩
def center1892 : GaussianRat :=
  ⟨-14403551/62500000, 14758413/100000000⟩
def contact1892 : RatBall := localContactBall tau1892 center1892
def work1892 : RoundedTauEval :=
  evalTau precision tau1892 contact1892 logTwoBall

theorem center_sq1892 : (center1892.re : ℝ)^2 +
    (center1892.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1892]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1892 : work1892.theta.ok = true ∧
    work1892.jac.invOK = true ∧ acceptsUnitSq work1892.out = true := by
  norm_num [work1892, contact1892, tau1892, center1892, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1892 : CellCertificate where
  tauBall := tau1892
  contactCenter := center1892
  contactBall := contact1892
  work := work1892
  center_sq := center_sq1892
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1892.1
  jac_ok := checks1892.2.1
  accepted := checks1892.2.2

def tau1893 : RatBall :=
  ⟨⟨-103/320, 73/320⟩, 3/640⟩
def center1893 : GaussianRat :=
  ⟨-5645929/25000000, 9009977/62500000⟩
def contact1893 : RatBall := localContactBall tau1893 center1893
def work1893 : RoundedTauEval :=
  evalTau precision tau1893 contact1893 logTwoBall

theorem center_sq1893 : (center1893.re : ℝ)^2 +
    (center1893.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1893]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1893 : work1893.theta.ok = true ∧
    work1893.jac.invOK = true ∧ acceptsUnitSq work1893.out = true := by
  norm_num [work1893, contact1893, tau1893, center1893, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1893 : CellCertificate where
  tauBall := tau1893
  contactCenter := center1893
  contactBall := contact1893
  work := work1893
  center_sq := center_sq1893
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1893.1
  jac_ok := checks1893.2.1
  accepted := checks1893.2.2

def tau1894 : RatBall :=
  ⟨⟨-101/320, 73/320⟩, 3/640⟩
def center1894 : GaussianRat :=
  ⟨-44359939/200000000, 72370703/500000000⟩
def contact1894 : RatBall := localContactBall tau1894 center1894
def work1894 : RoundedTauEval :=
  evalTau precision tau1894 contact1894 logTwoBall

theorem center_sq1894 : (center1894.re : ℝ)^2 +
    (center1894.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1894]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1894 : work1894.theta.ok = true ∧
    work1894.jac.invOK = true ∧ acceptsUnitSq work1894.out = true := by
  norm_num [work1894, contact1894, tau1894, center1894, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1894 : CellCertificate where
  tauBall := tau1894
  contactCenter := center1894
  contactBall := contact1894
  work := work1894
  center_sq := center_sq1894
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1894.1
  jac_ok := checks1894.2.1
  accepted := checks1894.2.2

def tau1895 : RatBall :=
  ⟨⟨-103/320, 15/64⟩, 3/640⟩
def center1895 : GaussianRat :=
  ⟨-14151969/62500000, 148191091/1000000000⟩
def contact1895 : RatBall := localContactBall tau1895 center1895
def work1895 : RoundedTauEval :=
  evalTau precision tau1895 contact1895 logTwoBall

theorem center_sq1895 : (center1895.re : ℝ)^2 +
    (center1895.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1895]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1895 : work1895.theta.ok = true ∧
    work1895.jac.invOK = true ∧ acceptsUnitSq work1895.out = true := by
  norm_num [work1895, contact1895, tau1895, center1895, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1895 : CellCertificate where
  tauBall := tau1895
  contactCenter := center1895
  contactBall := contact1895
  work := work1895
  center_sq := center_sq1895
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1895.1
  jac_ok := checks1895.2.1
  accepted := checks1895.2.2

def cells : List CellCertificate := [cell1888, cell1889, cell1890, cell1891, cell1892, cell1893, cell1894, cell1895]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236
