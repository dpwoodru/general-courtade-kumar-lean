import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0251

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2008 : RatBall :=
  ⟨⟨-13/64, 97/320⟩, 3/640⟩
def center2008 : GaussianRat :=
  ⟨-9520441/62500000, 206807941/1000000000⟩
def contact2008 : RatBall := localContactBall tau2008 center2008
def work2008 : RoundedTauEval :=
  evalTau precision tau2008 contact2008 logTwoBall

theorem center_sq2008 : (center2008.re : ℝ)^2 +
    (center2008.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2008]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2008 : work2008.theta.ok = true ∧
    work2008.jac.invOK = true ∧ acceptsUnitSq work2008.out = true := by
  norm_num [work2008, contact2008, tau2008, center2008, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2008 : CellCertificate where
  tauBall := tau2008
  contactCenter := center2008
  contactBall := contact2008
  work := work2008
  center_sq := center_sq2008
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2008.1
  jac_ok := checks2008.2.1
  accepted := checks2008.2.2

def tau2009 : RatBall :=
  ⟨⟨-67/320, 99/320⟩, 3/640⟩
def center2009 : GaussianRat :=
  ⟨-157440099/1000000000, 210676827/1000000000⟩
def contact2009 : RatBall := localContactBall tau2009 center2009
def work2009 : RoundedTauEval :=
  evalTau precision tau2009 contact2009 logTwoBall

theorem center_sq2009 : (center2009.re : ℝ)^2 +
    (center2009.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2009]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2009 : work2009.theta.ok = true ∧
    work2009.jac.invOK = true ∧ acceptsUnitSq work2009.out = true := by
  norm_num [work2009, contact2009, tau2009, center2009, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2009 : CellCertificate where
  tauBall := tau2009
  contactCenter := center2009
  contactBall := contact2009
  work := work2009
  center_sq := center_sq2009
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2009.1
  jac_ok := checks2009.2.1
  accepted := checks2009.2.2

def tau2010 : RatBall :=
  ⟨⟨-13/64, 99/320⟩, 3/640⟩
def center2010 : GaussianRat :=
  ⟨-30588339/200000000, 211307539/1000000000⟩
def contact2010 : RatBall := localContactBall tau2010 center2010
def work2010 : RoundedTauEval :=
  evalTau precision tau2010 contact2010 logTwoBall

theorem center_sq2010 : (center2010.re : ℝ)^2 +
    (center2010.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2010]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2010 : work2010.theta.ok = true ∧
    work2010.jac.invOK = true ∧ acceptsUnitSq work2010.out = true := by
  norm_num [work2010, contact2010, tau2010, center2010, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2010 : CellCertificate where
  tauBall := tau2010
  contactCenter := center2010
  contactBall := contact2010
  work := work2010
  center_sq := center_sq2010
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2010.1
  jac_ok := checks2010.2.1
  accepted := checks2010.2.2

def tau2011 : RatBall :=
  ⟨⟨-71/320, 101/320⟩, 3/640⟩
def center2011 : GaussianRat :=
  ⟨-167059951/1000000000, 10691611/50000000⟩
def contact2011 : RatBall := localContactBall tau2011 center2011
def work2011 : RoundedTauEval :=
  evalTau precision tau2011 contact2011 logTwoBall

theorem center_sq2011 : (center2011.re : ℝ)^2 +
    (center2011.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2011]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2011 : work2011.theta.ok = true ∧
    work2011.jac.invOK = true ∧ acceptsUnitSq work2011.out = true := by
  norm_num [work2011, contact2011, tau2011, center2011, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2011 : CellCertificate where
  tauBall := tau2011
  contactCenter := center2011
  contactBall := contact2011
  work := work2011
  center_sq := center_sq2011
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2011.1
  jac_ok := checks2011.2.1
  accepted := checks2011.2.2

def tau2012 : RatBall :=
  ⟨⟨-69/320, 101/320⟩, 3/640⟩
def center2012 : GaussianRat :=
  ⟨-32516539/200000000, 26813809/125000000⟩
def contact2012 : RatBall := localContactBall tau2012 center2012
def work2012 : RoundedTauEval :=
  evalTau precision tau2012 contact2012 logTwoBall

theorem center_sq2012 : (center2012.re : ℝ)^2 +
    (center2012.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2012]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2012 : work2012.theta.ok = true ∧
    work2012.jac.invOK = true ∧ acceptsUnitSq work2012.out = true := by
  norm_num [work2012, contact2012, tau2012, center2012, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2012 : CellCertificate where
  tauBall := tau2012
  contactCenter := center2012
  contactBall := contact2012
  work := work2012
  center_sq := center_sq2012
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2012.1
  jac_ok := checks2012.2.1
  accepted := checks2012.2.2

def tau2013 : RatBall :=
  ⟨⟨-71/320, 103/320⟩, 3/640⟩
def center2013 : GaussianRat :=
  ⟨-83877437/500000000, 218307477/1000000000⟩
def contact2013 : RatBall := localContactBall tau2013 center2013
def work2013 : RoundedTauEval :=
  evalTau precision tau2013 contact2013 logTwoBall

theorem center_sq2013 : (center2013.re : ℝ)^2 +
    (center2013.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2013]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2013 : work2013.theta.ok = true ∧
    work2013.jac.invOK = true ∧ acceptsUnitSq work2013.out = true := by
  norm_num [work2013, contact2013, tau2013, center2013, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2013 : CellCertificate where
  tauBall := tau2013
  contactCenter := center2013
  contactBall := contact2013
  work := work2013
  center_sq := center_sq2013
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2013.1
  jac_ok := checks2013.2.1
  accepted := checks2013.2.2

def tau2014 : RatBall :=
  ⟨⟨-69/320, 103/320⟩, 3/640⟩
def center2014 : GaussianRat :=
  ⟨-40815707/250000000, 219004401/1000000000⟩
def contact2014 : RatBall := localContactBall tau2014 center2014
def work2014 : RoundedTauEval :=
  evalTau precision tau2014 contact2014 logTwoBall

theorem center_sq2014 : (center2014.re : ℝ)^2 +
    (center2014.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2014]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2014 : work2014.theta.ok = true ∧
    work2014.jac.invOK = true ∧ acceptsUnitSq work2014.out = true := by
  norm_num [work2014, contact2014, tau2014, center2014, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2014 : CellCertificate where
  tauBall := tau2014
  contactCenter := center2014
  contactBall := contact2014
  work := work2014
  center_sq := center_sq2014
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2014.1
  jac_ok := checks2014.2.1
  accepted := checks2014.2.2

def tau2015 : RatBall :=
  ⟨⟨-67/320, 101/320⟩, 3/640⟩
def center2015 : GaussianRat :=
  ⟨-158087121/1000000000, 215173931/1000000000⟩
def contact2015 : RatBall := localContactBall tau2015 center2015
def work2015 : RoundedTauEval :=
  evalTau precision tau2015 contact2015 logTwoBall

theorem center_sq2015 : (center2015.re : ℝ)^2 +
    (center2015.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2015]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2015 : work2015.theta.ok = true ∧
    work2015.jac.invOK = true ∧ acceptsUnitSq work2015.out = true := by
  norm_num [work2015, contact2015, tau2015, center2015, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2015 : CellCertificate where
  tauBall := tau2015
  contactCenter := center2015
  contactBall := contact2015
  work := work2015
  center_sq := center_sq2015
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2015.1
  jac_ok := checks2015.2.1
  accepted := checks2015.2.2

def cells : List CellCertificate := [cell2008, cell2009, cell2010, cell2011, cell2012, cell2013, cell2014, cell2015]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0251
