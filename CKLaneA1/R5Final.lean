import CKLaneA1.R5Assembly
import CKLaneA1.R5Data.C000
import CKLaneA1.R5Data.C001
import CKLaneA1.R5Data.C002
import CKLaneA1.R5Data.C003
import CKLaneA1.R5Data.C004
import CKLaneA1.R5Data.C005
import CKLaneA1.R5Data.C006
import CKLaneA1.R5Data.C007
import CKLaneA1.R5Data.C008
import CKLaneA1.R5Data.C009
import CKLaneA1.R5Data.C010
import CKLaneA1.R5Data.C011
import CKLaneA1.R5Data.C012
import CKLaneA1.R5Data.C013
import CKLaneA1.R5Data.C014
import CKLaneA1.R5Data.C015
import CKLaneA1.R5Data.C016
import CKLaneA1.R5Data.C017

/-!
# CKLaneA1.R5Final — CE-stat row 5: `HighTCExclusion`

No retained stationary Case-E point has `t_C ≥ 1/100`: `highTC_of_cover` applied to the
kernel-checked cover `allStrips` (246 strips / 5514 cells, chunks `CKLaneA1.R5Data.C000–C017`).
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK CKLaneP CKLaneN1.CEStat CKLaneA1.R5Data

/-- The full row-5 cover. -/
def allStrips : List Strip := strips000 ++ strips001 ++ strips002 ++ strips003 ++ strips004 ++ strips005 ++ strips006 ++ strips007 ++ strips008 ++ strips009 ++ strips010 ++ strips011 ++ strips012 ++ strips013 ++ strips014 ++ strips015 ++ strips016 ++ strips017

theorem allStrips_ok : allStrips.all stripOK = true := by
  simp only [allStrips, List.all_append, strips000_ok, strips001_ok, strips002_ok, strips003_ok, strips004_ok, strips005_ok, strips006_ok, strips007_ok, strips008_ok, strips009_ok, strips010_ok, strips011_ok, strips012_ok, strips013_ok, strips014_ok, strips015_ok, strips016_ok, strips017_ok, Bool.and_self, Bool.and_true, Bool.true_and]

theorem allStrips_chain : chainOK T0N allStrips = true := by decide +kernel

/-- **CE-stat S.3 row 5 (`HighTCExclusion`).** -/
theorem highTCExclusion : HighTCExclusion := highTC_of_cover allStrips allStrips_ok allStrips_chain

/-- Binding to Lane N1's Prop (verbatim). -/
theorem highTCExclusion_binding : CKLaneN1.CEStat.HighTCExclusion := highTCExclusion

#print axioms highTCExclusion
#print axioms allStrips_ok
#print axioms allStrips_chain

end CKLaneA1.R5
