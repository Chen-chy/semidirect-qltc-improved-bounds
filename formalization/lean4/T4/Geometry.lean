import SemidirectQLTC.Geometry

/-!
# The four-direction specialization

These are statements about an actual left-coset space, not an abstract size
record. No normality assumption on `lambda` is used. The compiler status of
this source is recorded separately in `verification/status.json`.
-/
set_option autoImplicit false

namespace SemidirectQLTC.T4Geometry

open SemidirectQLTC.Geometry

noncomputable section

variable {A Q : Type*} [AddCommGroup A] [Group Q]
variable (ρ : Q →* AddAut A)

/-- Four directions, with one coordinate singled out for exact counting. -/
abbrev Dir := Option (Fin 3)

abbrev Ambient := Dir → Point ρ
abbrev X := Ambient ρ ⧸ lambda (I := Dir) ρ

theorem card_directions : Fintype.card Dir = 4 := by simp [Dir]

theorem another_direction (i : Dir) : ∃ j : Dir, j ≠ i := by
  cases i with
  | none => exact ⟨some 0, by simp⟩
  | some k => exact ⟨none, by simp⟩

theorem free_at_every_coset (i : Dir) (p : Point ρ) (x : X ρ) :
    leftAction (lambda (I := Dir) ρ) (coordinate ρ i p) x = x → p = 1 :=
  coordinate_action_free ρ i (another_direction i) p x

/-- The orbit map is injective for each point, not just for the identity coset. -/
theorem orbitMap_injective (i : Dir) (x : X ρ) :
    Function.Injective
      (fun p : Point ρ => leftAction (lambda (I := Dir) ρ) (coordinate ρ i p) x) := by
  intro p q hpq
  have hfix : leftAction (lambda (I := Dir) ρ)
      (coordinate ρ i (q⁻¹ * p)) x = x := by
    calc
      _ = leftAction (lambda (I := Dir) ρ) (coordinate ρ i q⁻¹)
          (leftAction (lambda (I := Dir) ρ) (coordinate ρ i p) x) := by
            rw [coordinate_mul, leftAction_mul]
      _ = leftAction (lambda (I := Dir) ρ) (coordinate ρ i q⁻¹)
          (leftAction (lambda (I := Dir) ρ) (coordinate ρ i q) x) := by rw [hpq]
      _ = x := by
        rw [← leftAction_mul, ← coordinate_mul, inv_mul_cancel, coordinate_one,
          leftAction_one]
  have hone := free_at_every_coset ρ i (q⁻¹ * p) x hfix
  have h := congrArg (fun z : Point ρ => q * z) hone
  simpa [mul_assoc] using h

variable [Fintype A] [Fintype Q]

theorem subgroup_cardinality :
    Nat.card (lambda (I := Dir) ρ) = Fintype.card A ^ 3 * Fintype.card Q := by
  simpa [Dir] using card_lambda (I := Fin 3) ρ

theorem coset_cardinality :
    Nat.card (X ρ) = Fintype.card A * Fintype.card Q ^ 3 := by
  simpa [X, Ambient, Dir] using card_cosets (I := Fin 3) ρ

/-- Each directional orbit has the cardinality of the semidirect product. -/
theorem directional_orbit_cardinality (i : Dir) (x : X ρ) :
    Nat.card (Set.range
      (fun p : Point ρ => leftAction (lambda (I := Dir) ρ) (coordinate ρ i p) x)) =
      Fintype.card A * Fintype.card Q := by
  calc
    _ = Nat.card (Point ρ) :=
      (Nat.card_congr (Equiv.ofInjective _ (orbitMap_injective ρ i x))).symm
    _ = Nat.card (A × Q) := Nat.card_congr (pointEquiv ρ)
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- Exact arithmetic of N = (orbit size) * b^2. This is not a substitute
    for constructing and counting the orbit-quotient type. -/
theorem component_size_identity (M b : ℕ) :
    (M * b) * b ^ 2 = M * b ^ 3 := by ring

end
end SemidirectQLTC.T4Geometry
