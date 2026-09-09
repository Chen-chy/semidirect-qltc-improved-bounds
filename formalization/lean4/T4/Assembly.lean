import T4.Scale
import T4.ShiftedRate
import T4.Geometry

/-!
# Conditional t = 4 parameter assembly

IMPORTANT: `logSquare_of_inputs` is a conditional theorem, not a closed
existence theorem. Its sector-expansion and distance premises are precisely
quantitative inputs still to be obtained by formalising and applying DLV.
Its matrix sparsity and size premises must come from the actual cubical
construction. No theorem in this file claims those premises are inhabited.

This separation is also enforced by `tools/verify.py`: successful compilation
alone is never reported as completion of the full qLTC existence proof.
-/
set_option autoImplicit false

namespace SemidirectQLTC.T4
open scoped BigOperators
noncomputable section

variable {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ]

/-- A bound on the number of listed checks yields a lower bound on n/m. -/
theorem normalization_bound {n m μ : ℝ}
    (hm : 0 < m) (hμ : 0 < μ) (hchecks : m ≤ μ * n) :
    1 / μ ≤ n / m := by
  apply (div_le_div_iff₀ hμ hm).mpr
  nlinarith

/-- The finite-scale tester theorem on the actual binary presentation. -/
theorem testability_at_scale (C : BinaryChain σ ι τ)
    {b aX aZ μ : ℝ}
    (hb : 0 < b) (haX : 0 ≤ aX) (haZ : 0 ≤ aZ) (hμ : 0 < μ)
    (hn : 0 < C.length) (hm : 0 < C.listedChecks)
    (hchecks : (C.listedChecks : ℝ) ≤ μ * (C.length : ℝ))
    (hX : SectorExpansion C.syndromeX (aZ * (1 / b ^ 2)))
    (hZ : SectorExpansion C.syndromeZ (aX * (1 / b ^ 2))) :
    C.GloballyTestable ((min aX aZ / μ) / b ^ 2) := by
  have hη : (0 : ℝ) ≤ 1 / b ^ 2 := by positivity
  have ht := C.two_sector_to_testability haX haZ hη hn hm hX hZ
  apply C.testability_mono ?_ ht
  have hnorm := normalization_bound
    (show (0 : ℝ) < C.listedChecks by exact_mod_cast hm) hμ hchecks
  have hmin : 0 ≤ min aX aZ := le_min haX haZ
  have h := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ min aX aZ * (1 / b ^ 2) by positivity)
  convert h using 1 <;> ring

/-- Explicit constants in the log-square distance and global Pauli tester
    bounds. All constants are independent of b when the supplied inputs are.

    This theorem intentionally does not assert an existential code family.
    In particular `hX`, `hZ`, and `hd` have not been derived from group expansion
    or local product-expansion inside Lean in this package. -/
theorem logSquare_of_inputs (C : BinaryChain σ ι τ)
    {κ b a A d aX aZ μ : ℝ} {s L : ℕ}
    (hsize : (C.length : ℝ) = κ * (2 : ℝ) ^ s * b ^ 3)
    (hκ : 1 ≤ κ) (hb : 1 ≤ b)
    (ha : 0 < a) (hdpos : 0 < d) (haX : 0 < aX) (haZ : 0 < aZ)
    (hμ : 0 < μ)
    (hslo : a * b ≤ (s : ℝ)) (hshi : (s : ℝ) ≤ A * b)
    (hn : 0 < C.length) (hm : 0 < C.listedChecks)
    (hchecks : (C.listedChecks : ℝ) ≤ μ * (C.length : ℝ))
    (hX : SectorExpansion C.syndromeX (aZ * (1 / b ^ 2)))
    (hZ : SectorExpansion C.syndromeZ (aX * (1 / b ^ 2)))
    (hd : C.DistanceAtLeast (d * (C.length : ℝ) / b ^ 2))
    (hloc : C.BoundarySparsity L) :
    C.DistanceAtLeast
        ((d * (a * Real.log 2) ^ 2) * (C.length : ℝ) /
          Real.log (C.length : ℝ) ^ 2) ∧
    C.GloballyTestable
        (((min aX aZ / μ) * (a * Real.log 2) ^ 2) /
          Real.log (C.length : ℝ) ^ 2) ∧
    C.LocalityAtMost (6 * L) (6 * L) ∧
    0 < d * (a * Real.log 2) ^ 2 ∧
    0 < (min aX aZ / μ) * (a * Real.log 2) ^ 2 := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have halog : 0 < a * Real.log 2 := mul_pos ha T4Scale.log_two_pos
  have hlogpos : 0 < Real.log (C.length : ℝ) :=
    T4Scale.log_positive hsize hκ hb ha hslo
  have hscale := (T4Scale.logarithmic_bounds hsize hκ hb hslo hshi).1
  have hdscale := T4Scale.inverse_square hbpos hlogpos halog
    (show 0 ≤ d * (C.length : ℝ) by positivity) hscale
  have hdr : C.DistanceAtLeast
      ((d * (a * Real.log 2) ^ 2) * (C.length : ℝ) /
        Real.log (C.length : ℝ) ^ 2) := by
    apply C.distance_mono ?_ hd
    convert hdscale using 1 <;> ring
  have hmin : 0 < min aX aZ := lt_min haX haZ
  have hs := testability_at_scale C hbpos haX.le haZ.le hμ hn hm hchecks hX hZ
  have hrscale := T4Scale.inverse_square hbpos hlogpos halog
    (show 0 ≤ min aX aZ / μ by positivity) hscale
  refine ⟨hdr, C.testability_mono hrscale hs, C.t4_locality hloc, ?_, ?_⟩
  · positivity
  · positivity

/-- Extension to nonnegative syndrome weights after a syndrome decomposition
    has been supplied. This is a finite expectation theorem, NOT the missing
    construction of stabilizer projectors or a Loewner-order theorem. -/
theorem expectation_of_global_testability (C : BinaryChain σ ι τ)
    {S : Type*} [Fintype S] (x z : S → ι → F2) (p : S → ℝ)
    {rho : ℝ} (hp : ∀ s, 0 ≤ p s) (h : C.GloballyTestable rho) :
    rho * (∑ s, p s * ((C.pauliDistance (x s) (z s) : ℝ) / (C.length : ℝ))) ≤
      ∑ s, p s * C.rejection (x s) (z s) := by
  exact syndrome_expectation p (fun s => C.rejection (x s) (z s))
    (fun s => (C.pauliDistance (x s) (z s) : ℝ) / (C.length : ℝ))
    rho hp (fun s => h (x s) (z s))

end
end SemidirectQLTC.T4
