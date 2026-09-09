import SemidirectQLTC.Hamming

/-!
# Global minimum syndrome filling

Syndromes are elements of the actual range of `H`.  The empty-fibre convention
therefore cannot accidentally give a zero filling to an inadmissible syndrome.
The minimisation is over all errors, without a small-error hypothesis.
-/

set_option autoImplicit false

namespace SemidirectQLTC

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K ι σ : Type*} [Field K] [Fintype ι]

abbrev Syndrome (H : (ι → K) →ₗ[K] (σ → K)) := LinearMap.range H

def syndrome (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) : Syndrome H :=
  ⟨H x, ⟨x, rfl⟩⟩

@[simp] theorem syndrome_val (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) :
    (syndrome H x).val = H x := rfl

private theorem filling_exists (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    ∃ w : ℕ, ∃ x : ι → K, H x = s.val ∧ weight x = w := by
  rcases s.property with ⟨x, hx⟩
  exact ⟨weight x, x, hx, rfl⟩

/-- `F_H(s)`, as a genuine minimum over the syndrome fibre. -/
def filling (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) : ℕ :=
  Nat.find (filling_exists H s)

theorem filling_spec (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    ∃ x : ι → K, H x = s.val ∧ weight x = filling H s :=
  Nat.find_spec (filling_exists H s)

theorem filling_le (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H)
    (x : ι → K) (hx : H x = s.val) : filling H s ≤ weight x :=
  Nat.find_min' (filling_exists H s) ⟨x, hx, rfl⟩

theorem filling_le_weight (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) :
    filling H (syndrome H x) ≤ weight x := filling_le H _ x rfl

theorem filling_le_card (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    filling H s ≤ Fintype.card ι := by
  rcases filling_spec H s with ⟨x, _, hx⟩
  rw [← hx]
  exact weight_le_card x

@[simp] theorem filling_zero (H : (ι → K) →ₗ[K] (σ → K)) :
    filling H 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using filling_le H 0 0 (by simp)

theorem filling_eq_zero_iff (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    filling H s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    rcases filling_spec H s with ⟨x, hx, hw⟩
    have hx0 : x = 0 := (weight_eq_zero x).mp (hw.trans hs)
    apply Subtype.ext
    simpa [hx0] using hx.symm
  · rintro rfl
    exact filling_zero H

/-- A selected minimum filler. This function need not, and is not claimed to, be linear. -/
def minimumFiller (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) : ι → K :=
  Classical.choose (filling_spec H s)

@[simp] theorem minimumFiller_syndrome (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    H (minimumFiller H s) = s.val :=
  (Classical.choose_spec (filling_spec H s)).1

@[simp] theorem minimumFiller_weight (H : (ι → K) →ₗ[K] (σ → K)) (s : Syndrome H) :
    weight (minimumFiller H s) = filling H s :=
  (Classical.choose_spec (filling_spec H s)).2

private theorem kernel_distance_exists (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) :
    ∃ w : ℕ, ∃ k : ι → K, H k = 0 ∧ weight (x - k) = w :=
  ⟨weight (x - 0), 0, map_zero H, rfl⟩

/-- Independently defined Hamming distance to the kernel, not the boundary space. -/
def kernelDistance (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) : ℕ :=
  Nat.find (kernel_distance_exists H x)

theorem kernelDistance_spec (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) :
    ∃ k : ι → K, H k = 0 ∧ weight (x - k) = kernelDistance H x :=
  Nat.find_spec (kernel_distance_exists H x)

theorem kernelDistance_le (H : (ι → K) →ₗ[K] (σ → K)) (x k : ι → K)
    (hk : H k = 0) : kernelDistance H x ≤ weight (x - k) :=
  Nat.find_min' (kernel_distance_exists H x) ⟨k, hk, rfl⟩

/-- The metric identity used in the global two-sector tester bound. -/
theorem filling_eq_kernelDistance (H : (ι → K) →ₗ[K] (σ → K)) (x : ι → K) :
    filling H (syndrome H x) = kernelDistance H x := by
  apply Nat.le_antisymm
  · rcases kernelDistance_spec H x with ⟨k, hk, hw⟩
    rw [← hw]
    apply filling_le
    simp [map_sub, hk]
  · rcases filling_spec H (syndrome H x) with ⟨y, hy, hw⟩
    have hk : H (x - y) = 0 := by simp [map_sub, hy]
    have h := kernelDistance_le H x (x - y) hk
    simpa [sub_sub_cancel, hw] using h

/-- A global sector expansion coefficient, in unnormalised Hamming units. -/
def SectorExpansion [Fintype σ] (H : (ι → K) →ₗ[K] (σ → K)) (c : ℝ) : Prop :=
  ∀ x : ι → K, c * (filling H (syndrome H x) : ℝ) ≤ (weight (H x) : ℝ)

/-- A global filling bound for the supplied matrix. -/
def GlobalFillingBound [Fintype σ] (H : (ι → K) →ₗ[K] (σ → K)) (L : ℝ) : Prop :=
  ∀ s : Syndrome H, (filling H s : ℝ) ≤ L * (weight s.val : ℝ)

/-- Equivalence between filling and expansion; no decoder linearity is assumed. -/
theorem globalFilling_iff_expansion [Fintype σ]
    (H : (ι → K) →ₗ[K] (σ → K)) {L : ℝ} (hL : 0 < L) :
    GlobalFillingBound H L ↔ SectorExpansion H (1 / L) := by
  constructor
  · intro h x
    have hx := h (syndrome H x)
    dsimp only [syndrome] at hx
    have hx' : (filling H (syndrome H x) : ℝ) ≤ (weight (H x) : ℝ) * L := by
      simpa [mul_comm] using hx
    have := (div_le_iff₀ hL).mpr hx'
    simpa [div_eq_mul_inv, mul_comm] using this
  · intro h s
    rcases s.property with ⟨x, hx⟩
    have hs : syndrome H x = s := Subtype.ext hx
    have he := h x
    rw [hs] at he
    have he' : (filling H s : ℝ) / L ≤ (weight (H x) : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using he
    simpa [hx, mul_comm] using (div_le_iff₀ hL).mp he'

end
end SemidirectQLTC
