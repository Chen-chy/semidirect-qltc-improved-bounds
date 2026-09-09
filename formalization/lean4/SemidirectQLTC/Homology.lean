import Mathlib

/-!
# Actual homology and the dimension-counting part of the shifted-rate argument

The homology space is `ker D / im B`, with the boundary map restricted to
cycles using a supplied chain identity.  The general dimension inequality is
proved using rank-nullity.  The DLV isomorphism between the original and shifted
complexes is NOT constructed in this module.
-/

set_option autoImplicit false

namespace SemidirectQLTC.Homology

noncomputable section

variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The image of the preceding differential as an actual subspace of cycles. -/
def boundaryToCycles (B : U →ₗ[K] V) (D : V →ₗ[K] W)
    (hchain : ∀ u, D (B u) = 0) : U →ₗ[K] LinearMap.ker D where
  toFun u := ⟨B u, hchain u⟩
  map_add' u v := Subtype.ext (map_add B u v)
  map_smul' a u := Subtype.ext (map_smul B a u)

abbrev Space (B : U →ₗ[K] V) (D : V →ₗ[K] W) (hchain : ∀ u, D (B u) = 0) :=
  (LinearMap.ker D) ⧸ LinearMap.range (boundaryToCycles B D hchain)

/-- The dimension bound valid for every three-term finite-dimensional complex. -/
theorem dimension_lower_bound (B : U →ₗ[K] V) (D : V →ₗ[K] W)
    (hchain : ∀ u, D (B u) = 0) :
    Module.finrank K V ≤ Module.finrank K (Space B D hchain) +
      Module.finrank K U + Module.finrank K W := by
  have hB := (boundaryToCycles B D hchain).finrank_range_add_finrank_ker
  have hD := D.finrank_range_add_finrank_ker
  have hQ := (LinearMap.range (boundaryToCycles B D hchain)).finrank_quotient_add_finrank
  have hRD : Module.finrank K (LinearMap.range D) ≤ Module.finrank K W :=
    Submodule.finrank_le _
  change Module.finrank K ((LinearMap.ker D) ⧸
      LinearMap.range (boundaryToCycles B D hchain)) +
      Module.finrank K (LinearMap.range (boundaryToCycles B D hchain)) =
      Module.finrank K (LinearMap.ker D) at hQ
  change Module.finrank K V ≤ Module.finrank K ((LinearMap.ker D) ⧸
      LinearMap.range (boundaryToCycles B D hchain)) + _ + _
  omega

/-- A positive excess of the middle dimension supplies nonzero homology. -/
theorem positive_dimension (B : U →ₗ[K] V) (D : V →ₗ[K] W)
    (hchain : ∀ u, D (B u) = 0)
    (hexcess : Module.finrank K U + Module.finrank K W < Module.finrank K V) :
    0 < Module.finrank K (Space B D hchain) := by
  have h := dimension_lower_bound B D hchain
  omega

/-- Pure scalar part of the corrected shifted-rate argument.  `h` is the
    homology dimension; `cj,cp,cn` are *shifted* chain dimensions.  Relating
    shifted homology to original homology remains an external dependency. -/
theorem shifted_rate_estimate {h cj cp cn total base q : ℝ}
    (hhom : cj ≤ h + cp + cn) (hsum : cj + cp + cn ≤ total)
    (hface : base ≤ cj) (htotal : total ≤ base * q) :
    base * (2 - q) ≤ h := by
  nlinarith

/-- For `t=4`, a concrete sufficiently small fixed row fraction works in the
    scalar bracket; this does not produce the required robust local matrices. -/
theorem t4_positive_bracket : 0 < 2 - (1 + 2 * (1 / 100 : ℚ)) ^ 4 := by
  norm_num

end
end SemidirectQLTC.Homology
