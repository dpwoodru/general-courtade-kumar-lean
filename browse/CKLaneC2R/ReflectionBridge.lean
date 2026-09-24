import CKLaneC2R.HCompact
import GeneralCK.ReflectionSmallBias
import GeneralCK.ReflectionRemainingRegionsCertified

/-!
# Lane C2: the reflection field at its exact type

`GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band` (F-C root) reduces the
reflection curvature inequality to
* `hsmall` — supplied by `GeneralCK.Reflection.curvature_nonneg_small_bias`
  (module `GeneralCK.ReflectionSmallBias`; the 113-module small-bias chain from
  `~/gck_lanes/P-REFL/work/farm_insitu`, whose whole import closure is byte-identical to this
  provider apart from those 113 modules — see C2/LOG.md 03:24Z), and
* `hcompact` — `CKLaneC2R.hcompact_certified` (5,079 compact + 2,922 endpoint reflective cells).
-/

namespace CKLaneC2R

/-- The consumer with the certified compact input; conditional only on `hsmall`. -/
theorem reflection_of_hsmall
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3 / 20 → 0 ≤ GeneralCK.Reflection.curvature a b) :
    ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ GeneralCK.Reflection.curvature a b :=
  fun _ _ hb hba ha =>
    GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band hsmall
      hcompact_certified hb hba ha

/-- The reflection field (`Theorem71Components.reflection` / `ProductionOwners.reflection`). -/
theorem reflection_certified :
    ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ GeneralCK.Reflection.curvature a b :=
  reflection_of_hsmall GeneralCK.Reflection.curvature_nonneg_small_bias

end CKLaneC2R
