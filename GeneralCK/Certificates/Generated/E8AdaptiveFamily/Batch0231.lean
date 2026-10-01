import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1848 : RatBall :=
  ⟨⟨19/64, -83/320⟩, 3/640⟩
def center1848 : GaussianRat :=
  ⟨212592873/1000000000, -33409337/200000000⟩
def contact1848 : RatBall := localContactBall tau1848 center1848
def work1848 : RoundedTauEval :=
  evalTau precision tau1848 contact1848 logTwoBall

theorem center_sq1848 : (center1848.re : ℝ)^2 +
    (center1848.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1848]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1848 : work1848.theta.ok = true ∧
    work1848.jac.invOK = true ∧ acceptsUnitSq work1848.out = true := by
  norm_num [work1848, contact1848, tau1848, center1848, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1848 : CellCertificate where
  tauBall := tau1848
  contactCenter := center1848
  contactBall := contact1848
  work := work1848
  center_sq := center_sq1848
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1848.1
  jac_ok := checks1848.2.1
  accepted := checks1848.2.2

def tau1849 : RatBall :=
  ⟨⟨93/320, -81/320⟩, 3/640⟩
def center1849 : GaussianRat :=
  ⟨103905761/500000000, -163537217/1000000000⟩
def contact1849 : RatBall := localContactBall tau1849 center1849
def work1849 : RoundedTauEval :=
  evalTau precision tau1849 contact1849 logTwoBall

theorem center_sq1849 : (center1849.re : ℝ)^2 +
    (center1849.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1849]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1849 : work1849.theta.ok = true ∧
    work1849.jac.invOK = true ∧ acceptsUnitSq work1849.out = true := by
  norm_num [work1849, contact1849, tau1849, center1849, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1849 : CellCertificate where
  tauBall := tau1849
  contactCenter := center1849
  contactBall := contact1849
  work := work1849
  center_sq := center_sq1849
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1849.1
  jac_ok := checks1849.2.1
  accepted := checks1849.2.2

def tau1850 : RatBall :=
  ⟨⟨19/64, -81/320⟩, 3/640⟩
def center1850 : GaussianRat :=
  ⟨211952789/1000000000, -162910673/1000000000⟩
def contact1850 : RatBall := localContactBall tau1850 center1850
def work1850 : RoundedTauEval :=
  evalTau precision tau1850 contact1850 logTwoBall

theorem center_sq1850 : (center1850.re : ℝ)^2 +
    (center1850.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1850]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1850 : work1850.theta.ok = true ∧
    work1850.jac.invOK = true ∧ acceptsUnitSq work1850.out = true := by
  norm_num [work1850, contact1850, tau1850, center1850, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1850 : CellCertificate where
  tauBall := tau1850
  contactCenter := center1850
  contactBall := contact1850
  work := work1850
  center_sq := center_sq1850
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1850.1
  jac_ok := checks1850.2.1
  accepted := checks1850.2.2

def tau1851 : RatBall :=
  ⟨⟨93/320, -79/320⟩, 3/640⟩
def center1851 : GaussianRat :=
  ⟨207198371/1000000000, -15939079/100000000⟩
def contact1851 : RatBall := localContactBall tau1851 center1851
def work1851 : RoundedTauEval :=
  evalTau precision tau1851 contact1851 logTwoBall

theorem center_sq1851 : (center1851.re : ℝ)^2 +
    (center1851.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1851]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1851 : work1851.theta.ok = true ∧
    work1851.jac.invOK = true ∧ acceptsUnitSq work1851.out = true := by
  norm_num [work1851, contact1851, tau1851, center1851, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1851 : CellCertificate where
  tauBall := tau1851
  contactCenter := center1851
  contactBall := contact1851
  work := work1851
  center_sq := center_sq1851
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1851.1
  jac_ok := checks1851.2.1
  accepted := checks1851.2.2

def tau1852 : RatBall :=
  ⟨⟨19/64, -79/320⟩, 3/640⟩
def center1852 : GaussianRat :=
  ⟨211331481/1000000000, -158782791/1000000000⟩
def contact1852 : RatBall := localContactBall tau1852 center1852
def work1852 : RoundedTauEval :=
  evalTau precision tau1852 contact1852 logTwoBall

theorem center_sq1852 : (center1852.re : ℝ)^2 +
    (center1852.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1852]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1852 : work1852.theta.ok = true ∧
    work1852.jac.invOK = true ∧ acceptsUnitSq work1852.out = true := by
  norm_num [work1852, contact1852, tau1852, center1852, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1852 : CellCertificate where
  tauBall := tau1852
  contactCenter := center1852
  contactBall := contact1852
  work := work1852
  center_sq := center_sq1852
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1852.1
  jac_ok := checks1852.2.1
  accepted := checks1852.2.2

def tau1853 : RatBall :=
  ⟨⟨93/320, -77/320⟩, 3/640⟩
def center1853 : GaussianRat :=
  ⟨12912721/62500000, -7762627/50000000⟩
def contact1853 : RatBall := localContactBall tau1853 center1853
def work1853 : RoundedTauEval :=
  evalTau precision tau1853 contact1853 logTwoBall

theorem center_sq1853 : (center1853.re : ℝ)^2 +
    (center1853.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1853]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1853 : work1853.theta.ok = true ∧
    work1853.jac.invOK = true ∧ acceptsUnitSq work1853.out = true := by
  norm_num [work1853, contact1853, tau1853, center1853, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1853 : CellCertificate where
  tauBall := tau1853
  contactCenter := center1853
  contactBall := contact1853
  work := work1853
  center_sq := center_sq1853
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1853.1
  jac_ok := checks1853.2.1
  accepted := checks1853.2.2

def tau1854 : RatBall :=
  ⟨⟨19/64, -77/320⟩, 3/640⟩
def center1854 : GaussianRat :=
  ⟨26341087/125000000, -77331419/500000000⟩
def contact1854 : RatBall := localContactBall tau1854 center1854
def work1854 : RoundedTauEval :=
  evalTau precision tau1854 contact1854 logTwoBall

theorem center_sq1854 : (center1854.re : ℝ)^2 +
    (center1854.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1854]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1854 : work1854.theta.ok = true ∧
    work1854.jac.invOK = true ∧ acceptsUnitSq work1854.out = true := by
  norm_num [work1854, contact1854, tau1854, center1854, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1854 : CellCertificate where
  tauBall := tau1854
  contactCenter := center1854
  contactBall := contact1854
  work := work1854
  center_sq := center_sq1854
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1854.1
  jac_ok := checks1854.2.1
  accepted := checks1854.2.2

def tau1855 : RatBall :=
  ⟨⟨97/320, -17/64⟩, 3/640⟩
def center1855 : GaussianRat :=
  ⟨54347721/250000000, -170518079/1000000000⟩
def contact1855 : RatBall := localContactBall tau1855 center1855
def work1855 : RoundedTauEval :=
  evalTau precision tau1855 contact1855 logTwoBall

theorem center_sq1855 : (center1855.re : ℝ)^2 +
    (center1855.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1855]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1855 : work1855.theta.ok = true ∧
    work1855.jac.invOK = true ∧ acceptsUnitSq work1855.out = true := by
  norm_num [work1855, contact1855, tau1855, center1855, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1855 : CellCertificate where
  tauBall := tau1855
  contactCenter := center1855
  contactBall := contact1855
  work := work1855
  center_sq := center_sq1855
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1855.1
  jac_ok := checks1855.2.1
  accepted := checks1855.2.2

def cells : List CellCertificate := [cell1848, cell1849, cell1850, cell1851, cell1852, cell1853, cell1854, cell1855]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231
