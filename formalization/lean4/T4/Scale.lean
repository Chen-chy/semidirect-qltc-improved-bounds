import Mathlib

/-!
# Exact logarithms and the log-square parameter conversion

The logarithm here is `Real.log`, not an unconstrained variable called log n.
The exact construction-size equation is an explicit premise.  This file does
not assert the existence of a classical code or of robust local gadgets.
-/
set_option autoImplicit false

namespace SemidirectQLTC.T4Scale
noncomputable section

/-- The exact size expected after fixing all local coefficient dimensions. -/
def size (κ s b : ℕ) : ℕ := κ * 2 ^ s * b ^ 3

theorem exact_log {κ b : ℝ} (s : ℕ) (hκ : 0 < κ) (hb : 0 < b) :
    Real.log (κ * (2 : ℝ) ^ s * b ^ 3) =
      Real.log κ + (s : ℝ) * Real.log 2 + 3 * Real.log b := by
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hκ) (pow_ne_zero s (by norm_num)))
      (pow_ne_zero 3 (ne_of_gt hb)),
    Real.log_mul (ne_of_gt hκ) (pow_ne_zero s (by norm_num)),
    Real.log_pow, Real.log_pow]
  norm_num

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- From the exact size and linear classical dimension, obtain BOTH sides
    of the logarithmic comparison. No comparison is assumed as a conclusion. -/
theorem logarithmic_bounds {n κ b a A : ℝ} {s : ℕ}
    (hsize : n = κ * (2 : ℝ) ^ s * b ^ 3)
    (hκ : 1 ≤ κ) (hb : 1 ≤ b)
    (hslo : a * b ≤ (s : ℝ)) (hshi : (s : ℝ) ≤ A * b) :
    (a * Real.log 2) * b ≤ Real.log n ∧
      Real.log n ≤ (Real.log κ + A * Real.log 2 + 3) * b := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hklog : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hblog : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlog2 : 0 ≤ Real.log 2 := le_of_lt log_two_pos
  have hident : Real.log n =
      Real.log κ + (s : ℝ) * Real.log 2 + 3 * Real.log b := by
    rw [hsize]
    exact exact_log s hκpos hbpos
  have hlow := mul_le_mul_of_nonneg_right hslo hlog2
  have hhigh := mul_le_mul_of_nonneg_right hshi hlog2
  have hblog_upper : Real.log b ≤ b := by
    have h := Real.log_le_sub_one_of_pos hbpos
    linarith
  have hklog_upper : Real.log κ ≤ Real.log κ * b := by
    have h := mul_le_mul_of_nonneg_left hb hklog
    simpa using h
  constructor <;> nlinarith

theorem log_positive {n κ b a : ℝ} {s : ℕ}
    (hsize : n = κ * (2 : ℝ) ^ s * b ^ 3)
    (hκ : 1 ≤ κ) (hb : 1 ≤ b) (ha : 0 < a)
    (hslo : a * b ≤ (s : ℝ)) :
    0 < Real.log n := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hklog : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hblog : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlow := mul_le_mul_of_nonneg_right hslo (le_of_lt log_two_pos)
  have hpos : 0 < (a * Real.log 2) * b := mul_pos (mul_pos ha log_two_pos) hbpos
  rw [hsize, exact_log s hκpos hbpos]
  nlinarith

/-- Quantitative inverse-square conversion. The constant is explicit. -/
theorem inverse_square {b ell a c : ℝ}
    (hb : 0 < b) (hell : 0 < ell) (ha : 0 < a) (hc : 0 ≤ c)
    (hscale : a * b ≤ ell) :
    c * a ^ 2 / ell ^ 2 ≤ c / b ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hsq : (a * b) ^ 2 ≤ ell ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hscale)
      (show 0 ≤ ell + a * b by positivity)
    nlinarith
  have hdiv : c / ell ^ 2 ≤ c / (a * b) ^ 2 :=
    div_le_div_of_nonneg_left hc (by positivity) hsq
  have hmul := mul_le_mul_of_nonneg_left hdiv (sq_nonneg a)
  have hid : a ^ 2 * (c / (a * b) ^ 2) = c / b ^ 2 := by
    field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
  calc
    _ = a ^ 2 * (c / ell ^ 2) := by ring
    _ ≤ a ^ 2 * (c / (a * b) ^ 2) := hmul
    _ = _ := hid

/-- Size growth is independent of any expansion theorem. -/
theorem size_ge_scale (κ s b : ℕ) (hκ : 1 ≤ κ) (hb : 1 ≤ b) :
    b ≤ size κ s b := by
  have hp0 : 0 < (2 : ℕ) ^ s := pow_pos (by norm_num) s
  have hp : 1 ≤ (2 : ℕ) ^ s := by omega
  have hb2 : b ≤ b * b := by simpa using Nat.mul_le_mul_left b hb
  have hb3 : b * b ≤ b ^ 3 := by
    have h := Nat.mul_le_mul_left (b * b) hb
    simpa [pow_succ, pow_two] using h
  have hκp : 1 ≤ κ * 2 ^ s := by nlinarith
  have hmult := Nat.mul_le_mul_right (b ^ 3) hκp
  exact hb2.trans (hb3.trans (by simpa [size] using hmult))

/-- The parameter sequence gives unbounded lengths for arbitrary dimensions s.
    This theorem does not construct a code of any of these lengths. -/
theorem sizes_unbounded (κ : ℕ) (s : ℕ → ℕ) (hκ : 1 ≤ κ) (K : ℕ) :
    ∃ b : ℕ, 1 ≤ b ∧ K < size κ (s b) b := by
  refine ⟨K + 1, by omega, ?_⟩
  have h := size_ge_scale κ (s (K + 1)) (K + 1) hκ (by omega)
  omega

end
end SemidirectQLTC.T4Scale
