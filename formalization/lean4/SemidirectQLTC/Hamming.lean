import Mathlib

/-!
# Concrete finite Hamming spaces

All weights are counts of actual nonzero coordinates.  In particular, they
are not abstract functions assumed to satisfy the conclusion of a coding lemma.
The development works over any field; the CSS specialization uses `ZMod 2`.

STATUS: proof source; not compiled in the authoring environment.  See
`verification/status.json`.  There are no proof-hole declarations in this file.
-/

set_option autoImplicit false

namespace SemidirectQLTC

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The listed coordinate support, retaining the original coordinate indexing. -/
def support (x : ι → K) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

/-- Unnormalised Hamming weight. -/
def weight (x : ι → K) : ℕ := (support x).card

@[simp] theorem mem_support (x : ι → K) (i : ι) :
    i ∈ support x ↔ x i ≠ 0 := by
  classical
  simp [support]

@[simp] theorem weight_zero : weight (0 : ι → K) = 0 := by
  classical
  simp [weight, support]

@[simp] theorem weight_eq_zero (x : ι → K) : weight x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro hx
    have hs : support x = ∅ := Finset.card_eq_zero.mp hx
    funext i
    by_contra hi
    have hm : i ∈ support x := (mem_support x i).mpr hi
    simpa [hs] using hm
  · rintro rfl
    exact weight_zero

theorem weight_le_card (x : ι → K) : weight x ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem weight_add_le (x y : ι → K) : weight (x + y) ≤ weight x + weight y := by
  classical
  have hs : support (x + y) ⊆ support x ∪ support y := by
    intro i hi
    simp only [mem_support, Pi.add_apply, Finset.mem_union] at hi ⊢
    by_contra h
    push_neg at h
    exact hi (by simp [h.1, h.2])
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

@[simp] theorem weight_neg (x : ι → K) : weight (-x) = weight x := by
  classical
  simp [weight, support]

theorem weight_sub_le (x y : ι → K) : weight (x - y) ≤ weight x + weight y := by
  simpa [sub_eq_add_neg] using weight_add_le x (-y)

theorem weight_smul_le (c : K) (x : ι → K) : weight (c • x) ≤ weight x := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [mem_support, Pi.smul_apply, smul_eq_mul] at hi ⊢
  exact fun h => hi (by simp [h])

theorem weight_sum_le {κ : Type*} (s : Finset κ) (f : κ → ι → K) :
    weight (∑ i ∈ s, f i) ≤ ∑ i ∈ s, weight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (weight_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A coordinate vector.  This is used instead of an opaque spanning hypothesis. -/
def unitVec (i : ι) : ι → K := by
  classical
  exact fun j => if j = i then 1 else 0

@[simp] theorem unitVec_apply (i j : ι) :
    unitVec (K := K) i j = if j = i then 1 else 0 := by
  classical
  rfl

@[simp] theorem weight_unitVec (i : ι) : weight (unitVec (K := K) i) = 1 := by
  classical
  have hs : support (unitVec (K := K) i) = {i} := by
    ext j
    by_cases h : j = i <;> simp [support, unitVec, h]
  simp [weight, hs]

/-- Explicit spanning by coordinate vectors. -/
theorem sum_units (x : ι → K) : x = ∑ i, x i • unitVec (K := K) i := by
  classical
  funext j
  simp [unitVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, eq_comm]

/-- The Pauli support is a union, not the sum of the two component weights. -/
def pauliWeight (x z : ι → K) : ℕ := (support x ∪ support z).card

theorem weight_left_le_pauliWeight (x z : ι → K) : weight x ≤ pauliWeight x z := by
  classical
  exact Finset.card_le_card Finset.subset_union_left

theorem weight_right_le_pauliWeight (x z : ι → K) : weight z ≤ pauliWeight x z := by
  classical
  exact Finset.card_le_card Finset.subset_union_right

theorem pauliWeight_le_add (x z : ι → K) :
    pauliWeight x z ≤ weight x + weight z := by
  classical
  exact Finset.card_union_le _ _

@[simp] theorem pauliWeight_zero_right (x : ι → K) : pauliWeight x 0 = weight x := by
  classical
  simp [pauliWeight, weight, support]

@[simp] theorem pauliWeight_zero_left (z : ι → K) : pauliWeight 0 z = weight z := by
  classical
  simp [pauliWeight, weight, support]

@[simp] theorem pauliWeight_eq_zero (x z : ι → K) :
    pauliWeight x z = 0 ↔ x = 0 ∧ z = 0 := by
  constructor
  · intro h
    have hx : weight x = 0 := Nat.eq_zero_of_le_zero (h ▸ weight_left_le_pauliWeight x z)
    have hz : weight z = 0 := Nat.eq_zero_of_le_zero (h ▸ weight_right_le_pauliWeight x z)
    exact ⟨(weight_eq_zero x).mp hx, (weight_eq_zero z).mp hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem pauliWeight_le_card (x z : ι → K) : pauliWeight x z ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card (Finset.subset_univ _)

end
end SemidirectQLTC
