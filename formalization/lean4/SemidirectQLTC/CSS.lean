import SemidirectQLTC.Filling

/-!
# CSS commutation, centralizer metric, and tester conversion

The matrix construction takes the **actual binary transpose**.  The metric
minimises over errors with the same two syndromes, and is proved equivalent to
minimisation over the centralizer.  No quotient by the stabilizer is substituted.

The final expectation lemma is a finite weighted-syndrome statement.  The
Hilbert-space construction of stabilizer projectors is NOT formalised here.
-/

set_option autoImplicit false

namespace SemidirectQLTC

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev F2 := ZMod 2

/-- Two consecutive binary boundary matrices, on the original listed indices. -/
structure BinaryChain (checksX qubits checksZ : Type*)
    [Fintype qubits] [Fintype checksZ] where
  lower : Matrix checksX qubits F2
  upper : Matrix qubits checksZ F2
  boundary_squared : lower * upper = 0

namespace BinaryChain

variable {checksX qubits checksZ : Type*} [Fintype qubits] [Fintype checksZ]

def hX (C : BinaryChain checksX qubits checksZ) : Matrix checksX qubits F2 := C.lower

def hZ (C : BinaryChain checksX qubits checksZ) : Matrix checksZ qubits F2 := C.upper.transpose

/-- Q03: binary CSS commutation, with no independent field-transpose expansion. -/
theorem css_commutes (C : BinaryChain checksX qubits checksZ) :
    C.hX * C.hZ.transpose = 0 := by
  simpa [hX, hZ] using C.boundary_squared

end BinaryChain

variable {ι σX σZ : Type*} [Fintype ι]
variable (HX : (ι → F2) →ₗ[F2] (σX → F2))
variable (HZ : (ι → F2) →ₗ[F2] (σZ → F2))

/-- Pauli exponents commuting with all listed CSS checks. -/
def InCentralizer (x z : ι → F2) : Prop := HZ x = 0 ∧ HX z = 0

private theorem joint_filling_exists (x z : ι → F2) :
    ∃ w : ℕ, ∃ y u : ι → F2,
      HZ y = HZ x ∧ HX u = HX z ∧ pauliWeight y u = w :=
  ⟨pauliWeight x z, x, z, rfl, rfl, rfl⟩

/-- Minimum Pauli weight among errors with the same syndrome. -/
def centralizerDistance (x z : ι → F2) : ℕ :=
  Nat.find (joint_filling_exists HX HZ x z)

theorem centralizerDistance_spec (x z : ι → F2) :
    ∃ y u : ι → F2, HZ y = HZ x ∧ HX u = HX z ∧
      pauliWeight y u = centralizerDistance HX HZ x z :=
  Nat.find_spec (joint_filling_exists HX HZ x z)

theorem centralizerDistance_le (x z y u : ι → F2)
    (hy : HZ y = HZ x) (hu : HX u = HX z) :
    centralizerDistance HX HZ x z ≤ pauliWeight y u :=
  Nat.find_min' (joint_filling_exists HX HZ x z) ⟨y, u, hy, hu, rfl⟩

/-- This supplies the centralizer interpretation of the syndrome definition. -/
theorem centralizer_minimizer (x z : ι → F2) :
    ∃ cx cz : ι → F2, InCentralizer HX HZ cx cz ∧
      pauliWeight (x - cx) (z - cz) = centralizerDistance HX HZ x z := by
  rcases centralizerDistance_spec HX HZ x z with ⟨y, u, hy, hu, hw⟩
  refine ⟨x - y, z - u, ?_, ?_⟩
  · constructor <;> simp [map_sub, hy, hu]
  · simpa using hw

/-- An exact minimum-distance characterisation, for every radius. -/
theorem centralizerDistance_le_iff (x z : ι → F2) (a : ℕ) :
    centralizerDistance HX HZ x z ≤ a ↔
      ∃ cx cz : ι → F2, InCentralizer HX HZ cx cz ∧
        pauliWeight (x - cx) (z - cz) ≤ a := by
  constructor
  · intro h
    rcases centralizer_minimizer HX HZ x z with ⟨cx, cz, hc, hw⟩
    exact ⟨cx, cz, hc, hw.le.trans h⟩
  · rintro ⟨cx, cz, ⟨hcx, hcz⟩, hw⟩
    exact (centralizerDistance_le HX HZ x z (x - cx) (z - cz)
      (by simp [map_sub, hcx]) (by simp [map_sub, hcz])).trans hw

theorem sector_filling_le_centralizer (x z : ι → F2) :
    filling HZ (syndrome HZ x) ≤ centralizerDistance HX HZ x z ∧
    filling HX (syndrome HX z) ≤ centralizerDistance HX HZ x z := by
  rcases centralizerDistance_spec HX HZ x z with ⟨y, u, hy, hu, hw⟩
  constructor
  · exact (filling_le HZ _ y hy).trans ((weight_left_le_pauliWeight y u).trans_eq hw)
  · exact (filling_le HX _ u hu).trans ((weight_right_le_pauliWeight y u).trans_eq hw)

theorem centralizer_le_sector_sum (x z : ι → F2) :
    centralizerDistance HX HZ x z ≤
      filling HZ (syndrome HZ x) + filling HX (syndrome HX z) := by
  rcases filling_spec HZ (syndrome HZ x) with ⟨y, hy, hwy⟩
  rcases filling_spec HX (syndrome HX z) with ⟨u, hu, hwu⟩
  calc
    centralizerDistance HX HZ x z ≤ pauliWeight y u :=
      centralizerDistance_le HX HZ x z y u hy hu
    _ ≤ weight y + weight u := pauliWeight_le_add y u
    _ = _ := by rw [hwy, hwu]

/-- A mixed centralizer multiplier cannot shorten a pure-sector minimum. -/
theorem pureX_distance (x : ι → F2) :
    centralizerDistance HX HZ x 0 = filling HZ (syndrome HZ x) := by
  apply Nat.le_antisymm
  · rcases filling_spec HZ (syndrome HZ x) with ⟨y, hy, hw⟩
    have h := centralizerDistance_le HX HZ x 0 y 0 hy rfl
    simpa [hw] using h
  · exact (sector_filling_le_centralizer HX HZ x 0).1

theorem pureZ_distance (z : ι → F2) :
    centralizerDistance HX HZ 0 z = filling HX (syndrome HX z) := by
  apply Nat.le_antisymm
  · rcases filling_spec HX (syndrome HX z) with ⟨u, hu, hw⟩
    have h := centralizerDistance_le HX HZ 0 z 0 u rfl hu
    simpa [hw] using h
  · exact (sector_filling_le_centralizer HX HZ 0 z).2

theorem centralizerDistance_zero_iff (x z : ι → F2) :
    centralizerDistance HX HZ x z = 0 ↔ InCentralizer HX HZ x z := by
  constructor
  · intro h
    rcases centralizerDistance_spec HX HZ x z with ⟨y, u, hy, hu, hw⟩
    rcases (pauliWeight_eq_zero y u).mp (hw.trans h) with ⟨hy0, hu0⟩
    constructor
    · simpa [hy0] using hy.symm
    · simpa [hu0] using hu.symm
  · rintro ⟨hx, hz⟩
    apply Nat.eq_zero_of_le_zero
    simpa using centralizerDistance_le HX HZ x z 0 0
      (by simp [hx]) (by simp [hz])

theorem centralizerDistance_le_length (x z : ι → F2) :
    centralizerDistance HX HZ x z ≤ Fintype.card ι :=
  (centralizerDistance_le HX HZ x z x z rfl rfl).trans (pauliWeight_le_card x z)

variable [Fintype σX] [Fintype σZ]

/-- Q04, Pauli part: global sector expansion implies global centralizer soundness. -/
theorem two_sector_soundness {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hX : SectorExpansion HX (b * r)) (hZ : SectorExpansion HZ (a * r))
    (x z : ι → F2) :
    (min a b * r) * (centralizerDistance HX HZ x z : ℝ) ≤
      (weight (HZ x) : ℝ) + (weight (HX z) : ℝ) := by
  have hc : 0 ≤ min a b * r := mul_nonneg (le_min ha hb) hr
  have hdist : (centralizerDistance HX HZ x z : ℝ) ≤
      (filling HZ (syndrome HZ x) : ℝ) + (filling HX (syndrome HX z) : ℝ) := by
    exact_mod_cast centralizer_le_sector_sum HX HZ x z
  have hx : (min a b * r) * (filling HZ (syndrome HZ x) : ℝ) ≤
      (weight (HZ x) : ℝ) := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left a b) hr) (by positivity)).trans (hZ x)
  have hz : (min a b * r) * (filling HX (syndrome HX z) : ℝ) ≤
      (weight (HX z) : ℝ) := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right a b) hr) (by positivity)).trans (hX z)
  calc
    _ ≤ (min a b * r) * ((filling HZ (syndrome HZ x) : ℝ) +
        (filling HX (syndrome HX z) : ℝ)) := mul_le_mul_of_nonneg_left hdist hc
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add hx hz

/-- Uniform sampling keeps all listed checks; `m` is not the independent rank. -/
theorem uniform_tester_bound {a b r n m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hn : 0 < n) (hm : 0 < m)
    (hX : SectorExpansion HX (b * r)) (hZ : SectorExpansion HZ (a * r))
    (x z : ι → F2) :
    ((min a b * r) * n / m) * ((centralizerDistance HX HZ x z : ℝ) / n) ≤
      ((weight (HZ x) : ℝ) + (weight (HX z) : ℝ)) / m := by
  have heq : ((min a b * r) * n / m) * ((centralizerDistance HX HZ x z : ℝ) / n) =
      ((min a b * r) * (centralizerDistance HX HZ x z : ℝ)) / m := by
    field_simp [ne_of_gt hn, ne_of_gt hm] <;> ring
  rw [heq]
  exact div_le_div_of_nonneg_right (two_sector_soundness HX HZ ha hb hr hX hZ x z) (le_of_lt hm)

/-- Generic bound, before normalisation: δ ≤ n times the number of violated checks. -/
theorem generic_pauli_bound (x z : ι → F2) :
    centralizerDistance HX HZ x z ≤
      Fintype.card ι * (weight (HZ x) + weight (HX z)) := by
  by_cases hd : centralizerDistance HX HZ x z = 0
  · simp [hd]
  · have hv : 1 ≤ weight (HZ x) + weight (HX z) := by
      by_contra h
      have hzero : weight (HZ x) + weight (HX z) = 0 := by omega
      have hx : HZ x = 0 := (weight_eq_zero _).mp (by omega)
      have hz : HX z = 0 := (weight_eq_zero _).mp (by omega)
      exact hd ((centralizerDistance_zero_iff HX HZ x z).mpr ⟨hx, hz⟩)
    exact (centralizerDistance_le_length HX HZ x z).trans
      (by simpa using Nat.mul_le_mul_left (Fintype.card ι) hv)

/-- The expectation step once a syndrome decomposition has been supplied. -/
theorem syndrome_expectation {S : Type*} [Fintype S]
    (p v δ : S → ℝ) (c : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h : ∀ s, c * δ s ≤ v s) :
    c * (∑ s, p s * δ s) ≤ ∑ s, p s * v s := by
  calc
    _ = ∑ s, p s * (c * δ s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (hp s))

end
end SemidirectQLTC
