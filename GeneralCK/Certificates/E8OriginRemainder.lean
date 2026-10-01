import GeneralCK.Certificates.E8OriginPilot

/-!
# Exact rational E8 origin remainder arithmetic

This ports the eight nonzero inverse-series coefficient boxes and the
degree-17 remainder expression from `cert_local_K.cpp`.  Each endpoint below
is the exact rational denoted by the corresponding decimal string in that
source file.
-/

namespace GeneralCK.Certificates.E8OriginRemainder

structure RatBox where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def a1 : RatBox :=
  ⟨86643397569993163677154015182272071009437516795031 / 10^51,
   86643397569993163677154015182272071009437516795032 / 10^51⟩
def a3 : RatBox :=
  ⟨20190357754602742566760427441576401741651194898083 / 10^52,
   20190357754602742566760427441576401741651194898084 / 10^52⟩
def a5 : RatBox :=
  ⟨47604159111341188944061553923038778295342715255614 / 10^54,
   47604159111341188944061553923038778295342715255615 / 10^54⟩
def a7 : RatBox :=
  ⟨80569262255247070383370657352476730501696155150848 / 10^56,
   80569262255247070383370657352476730501696155150849 / 10^56⟩
def a9 : RatBox :=
  ⟨54076519396689673612356417373933496131679168248524 / 10^58,
   54076519396689673612356417373933496131679168248525 / 10^58⟩
def a11 : RatBox :=
  ⟨-15424954614716222971884551676487548665934024967255 / 10^59,
   -15424954614716222971884551676487548665934024967254 / 10^59⟩
def a13 : RatBox :=
  ⟨-44311840242740163610503116715320921269073057459071 / 10^61,
   -44311840242740163610503116715320921269073057459070 / 10^61⟩
def a15 : RatBox :=
  ⟨28044137413127432944783452992882373767619152721204 / 10^63,
   28044137413127432944783452992882373767619152721205 / 10^63⟩

def coefficientsOrdered : Bool := decide
  (a1.lo ≤ a1.hi ∧ a3.lo ≤ a3.hi ∧ a5.lo ≤ a5.hi ∧ a7.lo ≤ a7.hi ∧
   a9.lo ≤ a9.hi ∧ a11.lo ≤ a11.hi ∧ a13.lo ≤ a13.hi ∧ a15.lo ≤ a15.hi)

theorem coefficientsOrdered_accepts : coefficientsOrdered = true := by
  norm_num [coefficientsOrdered, a1, a3, a5, a7, a9, a11, a13, a15]

/-- Conservative absolute upper bounds extracted from the coefficient
boxes.  Even indices are zero in the odd inverse series. -/
def coeffAbsUpper : ℕ → ℚ
  | 1 => a1.hi
  | 3 => a3.hi
  | 5 => a5.hi
  | 7 => a7.hi
  | 9 => a9.hi
  | 11 => -a11.lo
  | 13 => -a13.lo
  | 15 => a15.hi
  | _ => 0

def radius : ℚ := 2 / 25
def q17AbsBound : ℚ := 290000000000000

def p0c : ℚ :=
  ∑ n ∈ Finset.range 16,
    coeffAbsUpper n * 2 ^ n * radius ^ (n - 1)

def p1c : ℚ :=
  ∑ n ∈ Finset.range 16,
    coeffAbsUpper n * n * 2 ^ (n - 1) * radius ^ (n - 1)

def p2c : ℚ :=
  ∑ n ∈ Finset.Icc 3 15,
    coeffAbsUpper n * n * (n - 1) * 2 ^ (n - 2) * radius ^ (n - 3)

def p3c : ℚ :=
  ∑ n ∈ Finset.Icc 3 15,
    coeffAbsUpper n * n * (n - 1) * (n - 2) *
      2 ^ (n - 3) * radius ^ (n - 3)

def tailError (j : ℕ) : ℚ :=
  q17AbsBound * 2 ^ (17 - j) / (17 - j).factorial

/-- The exact remainder expression in `cert_local_K.cpp`. -/
def remainderOverRadiusCubed : ℚ :=
  18 * (p0c * tailError 3 * radius ^ 12 +
    p3c * tailError 0 * radius ^ 14 +
    tailError 0 * tailError 3 * radius ^ 28) +
  28 * (p1c * tailError 2 * radius ^ 12 +
    p2c * tailError 1 * radius ^ 14 +
    tailError 1 * tailError 2 * radius ^ 28)

/-- Kernel evaluation reproduces the conservative `1.3e-5` upper bound
used by the origin summary. -/
theorem remainderOverRadiusCubed_lt :
    remainderOverRadiusCubed < 13 / 1000000 := by
  norm_num [remainderOverRadiusCubed, p0c, p1c, p2c, p3c,
    tailError, q17AbsBound, radius, coeffAbsUpper, a1, a3, a5, a7, a9,
    a11, a13, a15, Finset.sum_range_succ, Finset.sum_Icc_succ_top]

/-- Combining the ported remainder estimate with any polynomial lower bound
of `5.99e-5` leaves a strictly positive normalized margin. -/
theorem polynomial_sub_remainder_pos :
    0 < (599 / 10000000 : ℚ) - remainderOverRadiusCubed := by
  linarith [remainderOverRadiusCubed_lt]

/-- The computed remainder leaves room for the retained summary's checked
`4.6e-5` lower endpoint. -/
theorem retained_margin_lt :
    (46 / 1000000 : ℚ) < 599 / 10000000 - remainderOverRadiusCubed := by
  linarith [remainderOverRadiusCubed_lt]

end GeneralCK.Certificates.E8OriginRemainder
