import T4.Assembly

/-!
# All requested parameter inequalities, conditional on precise certificates

This is NOT an unconditional existence theorem for the semidirect qLTC family.
The input chain, shifted homology equivalence, incidence bounds and global
metric estimates have to be constructed independently.  See the proof boundary
before treating compilation of this theorem as evidence for a qLTC construction.
-/
set_option autoImplicit false

namespace SemidirectQLTC.T4
noncomputable section

variable {ι σ τ U V W : Type*} [Fintype ι] [Fintype σ] [Fintype τ]
variable [AddCommGroup U] [Module F2 U] [FiniteDimensional F2 U]
variable [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
variable [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]

/-- Fixed positive bracket from ν = 1/100. -/
def rateBracket : ℝ := 2 - (1 + 2 * (1 / 100 : ℝ)) ^ 4

theorem rateBracket_pos : 0 < rateBracket := T4Rate.positive_bracket

/-- The conjunction uses the actual code's logical dimension, check counts,
    Pauli metric and binary rows throughout. All constants below are explicit.
    There is no conclusion or premise asserting that such certificates exist. -/
theorem t4_parameters_from_certificates
    (C : BinaryChain σ ι τ)
    (B : U →ₗ[F2] V) (D : V →ₗ[F2] W) (hchain : ∀ u, D (B u) = 0)
    (e : C.LogicalSpace ≃ₗ[F2] Homology.Space B D hchain)
    {κ λ b a A ell degree d aX aZ total : ℝ} {s L : ℕ}
    (hκ : 1 ≤ κ) (hλ : 0 < λ) (hb : 1 ≤ b)
    (ha : 0 < a) (hell : 0 < ell) (hdegree : 0 < degree)
    (hdpos : 0 < d) (haX : 0 < aX) (haZ : 0 < aZ)
    (hsize : (C.length : ℝ) = κ * (2 : ℝ) ^ s * b ^ 3)
    (hcheckSize : (C.listedChecks : ℝ) = λ * (2 : ℝ) ^ s * b ^ 3)
    (hslo : a * b ≤ (s : ℝ)) (hshi : (s : ℝ) ≤ A * b)
    (hface : ell * ((2 : ℝ) ^ s * b ^ 3) * degree ^ 4 ≤
      (Module.finrank F2 V : ℝ))
    (hsum : (Module.finrank F2 V : ℝ) + (Module.finrank F2 U : ℝ) +
      (Module.finrank F2 W : ℝ) ≤ total)
    (htotal : total ≤ ell * ((2 : ℝ) ^ s * b ^ 3) * degree ^ 4 *
      (1 + 2 * (1 / 100 : ℝ)) ^ 4)
    (hX : SectorExpansion C.syndromeX (aZ * (1 / b ^ 2)))
    (hZ : SectorExpansion C.syndromeZ (aX * (1 / b ^ 2)))
    (hd : C.DistanceAtLeast (d * (C.length : ℝ) / b ^ 2))
    (hloc : C.BoundarySparsity L) :
    let R := ell * degree ^ 4 * rateBracket / κ
    let d0 := d * (a * Real.log 2) ^ 2
    let rho0 := (min aX aZ / (λ / κ)) * (a * Real.log 2) ^ 2
    0 < R ∧ 0 < d0 ∧ 0 < rho0 ∧
      R * (C.length : ℝ) ≤ (C.logicalDimension : ℝ) ∧
      C.logicalDimension ≤ C.length ∧
      (C.listedChecks : ℝ) = (λ / κ) * (C.length : ℝ) ∧
      C.DistanceAtLeast (d0 * (C.length : ℝ) / Real.log (C.length : ℝ) ^ 2) ∧
      C.GloballyTestable (rho0 / Real.log (C.length : ℝ) ^ 2) ∧
      C.LocalityAtMost (6 * L) (6 * L) := by
  dsimp only
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hnR : (0 : ℝ) < C.length := by rw [hsize]; positivity
  have hmR : (0 : ℝ) < C.listedChecks := by rw [hcheckSize]; positivity
  have hn : 0 < C.length := by exact_mod_cast hnR
  have hm : 0 < C.listedChecks := by exact_mod_cast hmR
  have hμ : 0 < λ / κ := div_pos hλ hκpos
  have hcheckRatio : (C.listedChecks : ℝ) = (λ / κ) * (C.length : ℝ) := by
    rw [hcheckSize, hsize]
    field_simp [ne_of_gt hκpos] <;> ring
  have hmetric := logSquare_of_inputs C hsize hκ hb ha hdpos haX haZ hμ hslo hshi
    hn hm hcheckRatio.le hX hZ hd hloc
  have hrate := T4Rate.rate_from_shift C B D hchain e hface hsum htotal
  have hrateNormalized : (ell * degree ^ 4 * rateBracket / κ) * (C.length : ℝ) ≤
      (C.logicalDimension : ℝ) := by
    calc
      _ = ell * ((2 : ℝ) ^ s * b ^ 3) * degree ^ 4 * rateBracket := by
        rw [hsize]
        field_simp [ne_of_gt hκpos] <;> ring
      _ ≤ _ := hrate
  refine ⟨?_, hmetric.2.2.2.1, hmetric.2.2.2.2, hrateNormalized,
    C.logicalDimension_le_length, hcheckRatio, hmetric.1, hmetric.2.1, hmetric.2.2.1⟩
  have hbracket := rateBracket_pos
  positivity

end
end SemidirectQLTC.T4
