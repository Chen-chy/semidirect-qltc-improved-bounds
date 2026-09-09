import T4.BinaryPresentation

/-!
# The shifted dimension argument

The input `e` is an ACTUAL linear equivalence of homology spaces. Its existence
is not postulated by a new axiom or an instance. The DLV construction of this
linear equivalence is still missing from this project. No metric estimate is
transported through `e`.
-/
set_option autoImplicit false

namespace SemidirectQLTC.T4Rate
noncomputable section

open SemidirectQLTC.Homology

variable {ι σ τ U V W : Type*} [Fintype ι] [Fintype σ] [Fintype τ]
variable [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]
variable [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
variable [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]

/-- Derive the shifted-rate estimate from a supplied homology equivalence and
    shifted chain-dimension bounds, instead of assuming positive original rate. -/
theorem rate_from_shift (C : BinaryChain σ ι τ)
    (B : U →ₗ[F2] V) (D : V →ₗ[F2] W) (hchain : ∀ u, D (B u) = 0)
    (e : C.LogicalSpace ≃ₗ[F2] Space B D hchain)
    {N degree ν total : ℝ}
    (hface : N * degree ^ 4 ≤ (Module.finrank F2 V : ℝ))
    (hsum : (Module.finrank F2 V : ℝ) + (Module.finrank F2 U : ℝ) +
      (Module.finrank F2 W : ℝ) ≤ total)
    (htotal : total ≤ N * degree ^ 4 * (1 + 2 * ν) ^ 4) :
    N * degree ^ 4 * (2 - (1 + 2 * ν) ^ 4) ≤ (C.logicalDimension : ℝ) := by
  have hdim := dimension_lower_bound B D hchain
  have heq : Module.finrank F2 C.LogicalSpace =
      Module.finrank F2 (Space B D hchain) := e.finrank_eq
  rw [← heq] at hdim
  have hhom : (Module.finrank F2 V : ℝ) ≤
      (C.logicalDimension : ℝ) + (Module.finrank F2 U : ℝ) +
        (Module.finrank F2 W : ℝ) := by
    exact_mod_cast hdim
  exact shifted_rate_estimate hhom hsum hface htotal

/-- A concrete rational choice for the purely scalar positive-rate bracket. -/
theorem positive_bracket : 0 < (2 : ℝ) - (1 + 2 * (1 / 100 : ℝ)) ^ 4 := by
  norm_num

/-- Normalization to the physical number of binary coordinates. -/
theorem rate_normalization {N κ degree ν n k : ℝ}
    (hκ : 0 < κ) (hn : n = κ * N)
    (hk : N * degree ^ 4 * (2 - (1 + 2 * ν) ^ 4) ≤ k) :
    (degree ^ 4 * (2 - (1 + 2 * ν) ^ 4) / κ) * n ≤ k := by
  have hid : (degree ^ 4 * (2 - (1 + 2 * ν) ^ 4) / κ) * n =
      N * degree ^ 4 * (2 - (1 + 2 * ν) ^ 4) := by
    rw [hn]
    field_simp [ne_of_gt hκ] <;> ring
  rwa [hid]

end
end SemidirectQLTC.T4Rate
