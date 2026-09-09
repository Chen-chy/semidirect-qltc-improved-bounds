import SemidirectQLTC.CSS
import SemidirectQLTC.Homology

/-!
# Actual binary matrices, their linear maps, and their homology

The two syndrome maps and logical dimension below are derived from the same
binary chain. They are not unrelated fields in an abstract parameter record.
The construction of this binary chain from cubical local coefficients remains
an explicit outstanding obligation; see `docs/PROOF_BOUNDARY.zh-CN.md`.
-/
set_option autoImplicit false

namespace SemidirectQLTC

open scoped BigOperators
noncomputable section

variable {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ]

/-- Concrete matrix action, using the actual listed row/column indices. -/
def matrixMap (M : Matrix σ ι F2) : (ι → F2) →ₗ[F2] (σ → F2) where
  toFun x := fun s => ∑ i, M s i * x i
  map_add' x y := by
    funext s
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem matrixMap_apply (M : Matrix σ ι F2) (x : ι → F2) (s : σ) :
    matrixMap M x s = ∑ i, M s i * x i := rfl

@[simp] theorem matrixMap_zero (x : ι → F2) :
    matrixMap (0 : Matrix σ ι F2) x = 0 := by
  funext s
  simp [matrixMap_apply]

theorem matrixMap_mul (M : Matrix σ ι F2) (N : Matrix ι τ F2) (x : τ → F2) :
    matrixMap (M * N) x = matrixMap M (matrixMap N x) := by
  funext s
  simp only [matrixMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

namespace BinaryChain

variable (C : BinaryChain σ ι τ)

def syndromeX : (ι → F2) →ₗ[F2] (σ → F2) := matrixMap C.lower
def syndromeZ : (ι → F2) →ₗ[F2] (τ → F2) := matrixMap C.upper.transpose

def boundaryZ : (τ → F2) →ₗ[F2] (ι → F2) := matrixMap C.upper
def boundaryX : (σ → F2) →ₗ[F2] (ι → F2) := matrixMap C.lower.transpose

theorem chainZ (u : τ → F2) : C.syndromeX (C.boundaryZ u) = 0 := by
  change matrixMap C.lower (matrixMap C.upper u) = 0
  rw [← matrixMap_mul, C.boundary_squared, matrixMap_zero]

theorem chainX (u : σ → F2) : C.syndromeZ (C.boundaryX u) = 0 := by
  change matrixMap C.upper.transpose (matrixMap C.lower.transpose u) = 0
  rw [← matrixMap_mul, ← Matrix.transpose_mul, C.boundary_squared,
    Matrix.transpose_zero, matrixMap_zero]

abbrev LogicalSpace := Homology.Space C.boundaryZ C.syndromeX C.chainZ

def logicalDimension : ℕ := Module.finrank F2 C.LogicalSpace

def length (_ : BinaryChain σ ι τ) : ℕ := Fintype.card ι

def listedChecks (_ : BinaryChain σ ι τ) : ℕ := Fintype.card σ + Fintype.card τ

/-- The logical space is a quotient of a subspace of the physical space. -/
theorem logicalDimension_le_length : C.logicalDimension ≤ C.length := by
  have hQ := (LinearMap.range
    (Homology.boundaryToCycles C.boundaryZ C.syndromeX C.chainZ)).finrank_quotient_add_finrank
  have hker : Module.finrank F2 (LinearMap.ker C.syndromeX) ≤
      Module.finrank F2 (ι → F2) := Submodule.finrank_le _
  have hfun : Module.finrank F2 (ι → F2) = Fintype.card ι := Module.finrank_pi F2
  change C.logicalDimension + Module.finrank F2 (LinearMap.range
    (Homology.boundaryToCycles C.boundaryZ C.syndromeX C.chainZ)) =
      Module.finrank F2 (LinearMap.ker C.syndromeX) at hQ
  change C.logicalDimension ≤ Fintype.card ι
  rw [hfun] at hker
  omega

/-- Union-support distance to the centralizer of this same presentation. -/
def pauliDistance (x z : ι → F2) : ℕ :=
  centralizerDistance C.syndromeX C.syndromeZ x z

def violations (x z : ι → F2) : ℕ :=
  weight (C.syndromeZ x) + weight (C.syndromeX z)

/-- Uniform sampling is over all listed rows, including redundant rows. -/
def rejection (x z : ι → F2) : ℝ :=
  (C.violations x z : ℝ) / (C.listedChecks : ℝ)

def GloballyTestable (rho : ℝ) : Prop :=
  ∀ x z : ι → F2,
    rho * ((C.pauliDistance x z : ℝ) / (C.length : ℝ)) ≤ C.rejection x z

/-- Both logical-sector distance lower bounds, with real thresholds. -/
def DistanceAtLeast (d : ℝ) : Prop :=
  (∀ x : ι → F2, C.syndromeZ x = 0 → x ∉ LinearMap.range C.boundaryX →
    d ≤ (weight x : ℝ)) ∧
  (∀ z : ι → F2, C.syndromeX z = 0 → z ∉ LinearMap.range C.boundaryZ →
    d ≤ (weight z : ℝ))

theorem testability_mono {a b : ℝ} (hab : a ≤ b)
    (ht : C.GloballyTestable b) : C.GloballyTestable a := by
  intro x z
  exact (mul_le_mul_of_nonneg_right hab (by positivity)).trans (ht x z)

theorem distance_mono {a b : ℝ} (hab : a ≤ b)
    (hd : C.DistanceAtLeast b) : C.DistanceAtLeast a := by
  exact ⟨fun x hx hnx => hab.trans (hd.1 x hx hnx),
    fun z hz hnz => hab.trans (hd.2 z hz hnz)⟩

theorem two_sector_to_testability {a b eta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (heta : 0 ≤ eta)
    (hn : 0 < C.length) (hm : 0 < C.listedChecks)
    (hX : SectorExpansion C.syndromeX (b * eta))
    (hZ : SectorExpansion C.syndromeZ (a * eta)) :
    C.GloballyTestable
      ((min a b * eta) * (C.length : ℝ) / (C.listedChecks : ℝ)) := by
  intro x z
  have h := uniform_tester_bound C.syndromeX C.syndromeZ ha hb heta
    (show (0 : ℝ) < C.length by exact_mod_cast hn)
    (show (0 : ℝ) < C.listedChecks by exact_mod_cast hm) hX hZ x z
  simpa [GloballyTestable, pauliDistance, rejection, violations, Nat.cast_add] using h

/-- Column/row sparsity on the *binary* boundaries.  Obtaining these estimates
    from the cubical construction is a separate proof obligation. -/
structure BoundarySparsity (L : ℕ) : Prop where
  lower_row : ∀ s : σ, weight (C.lower s) ≤ 3 * L
  lower_column : ∀ i : ι, weight (C.lower.transpose i) ≤ 4 * L
  upper_row : ∀ i : ι, weight (C.upper i) ≤ 2 * L
  upper_column : ∀ t : τ, weight (C.upper.transpose t) ≤ 6 * L

/-- Single-check weight and combined participation, not independent ranks. -/
def LocalityAtMost (w Δ : ℕ) : Prop :=
  (∀ s : σ, weight (C.hX s) ≤ w) ∧
  (∀ t : τ, weight (C.hZ t) ≤ w) ∧
  (∀ i : ι, weight (C.hX.transpose i) + weight (C.hZ.transpose i) ≤ Δ)

theorem t4_locality {L : ℕ} (h : C.BoundarySparsity L) :
    C.LocalityAtMost (6 * L) (6 * L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    change weight (C.lower s) ≤ 6 * L
    have hs := h.lower_row s
    omega
  · intro t
    exact h.upper_column t
  · intro i
    change weight (C.lower.transpose i) + weight (C.upper.transpose.transpose i) ≤ 6 * L
    rw [Matrix.transpose_transpose]
    have hl := h.lower_column i
    have hu := h.upper_row i
    omega

end BinaryChain
end
end SemidirectQLTC
