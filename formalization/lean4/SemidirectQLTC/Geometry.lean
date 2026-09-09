import Mathlib

/-!
# Semidirect subgroup and left-coset geometry

`Point ρ` has multiplication `(a,g)(b,h) = (a + ρ(g)b, gh)`.
Translations need only be an additive abelian group for these lemmas.
No normality instance is assumed or manufactured for `lambda`.

For counting, directions are indexed by `Option I`, so `t = card I + 1`.
This avoids silently applying a `t-1` formula to `t=0`.
-/

set_option autoImplicit false

namespace SemidirectQLTC.Geometry

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A Q I : Type*} [AddCommGroup A] [Group Q]
variable (ρ : Q →* AddAut A)

@[ext] structure Point (ρ : Q →* AddAut A) where
  a : A
  q : Q

private theorem act_one (a : A) : ρ 1 a = a := by
  rw [map_one]
  rfl

private theorem act_mul (g h : Q) (a : A) : ρ (g * h) a = ρ g (ρ h a) := by
  rw [map_mul]
  rfl

/-- The group law is proved, rather than postulated as a semidirect interface. -/
instance pointGroup : Group (Point ρ) where
  one := ⟨0, 1⟩
  mul x y := ⟨x.a + ρ x.q y.a, x.q * y.q⟩
  inv x := ⟨-(ρ x.q⁻¹ x.a), x.q⁻¹⟩
  mul_assoc x y z := by
    apply Point.ext
    · change (x.a + ρ x.q y.a) + ρ (x.q * y.q) z.a =
        x.a + ρ x.q (y.a + ρ y.q z.a)
      rw [act_mul, map_add]
      exact add_assoc _ _ _
    · exact mul_assoc _ _ _
  one_mul x := by
    apply Point.ext
    · change 0 + ρ 1 x.a = x.a
      rw [act_one, zero_add]
    · exact one_mul _
  mul_one x := by
    apply Point.ext
    · change x.a + ρ x.q 0 = x.a
      rw [map_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel x := by
    apply Point.ext
    · change -(ρ x.q⁻¹ x.a) + ρ x.q⁻¹ x.a = 0
      exact neg_add_cancel _
    · exact inv_mul_cancel _

@[simp] theorem one_a : (1 : Point ρ).a = 0 := rfl
@[simp] theorem one_q : (1 : Point ρ).q = 1 := rfl
@[simp] theorem mul_a (x y : Point ρ) :
    (x * y).a = x.a + ρ x.q y.a := rfl
@[simp] theorem mul_q (x y : Point ρ) : (x * y).q = x.q * y.q := rfl
@[simp] theorem inv_a (x : Point ρ) : (x⁻¹).a = -(ρ x.q⁻¹ x.a) := rfl
@[simp] theorem inv_q (x : Point ρ) : (x⁻¹).q = x.q⁻¹ := rfl

/-- Equal group coordinates and zero total translation. -/
def lambda [Fintype I] : Subgroup (I → Point ρ) where
  carrier := {x | (∃ g : Q, ∀ i, (x i).q = g) ∧ ∑ i, (x i).a = 0}
  one_mem' := by
    refine ⟨⟨1, fun _ => rfl⟩, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨⟨g, hg⟩, hx⟩ ⟨⟨h, hh⟩, hy⟩
    refine ⟨⟨g * h, fun i => by simp [hg i, hh i]⟩, ?_⟩
    change (∑ i, (x i).a + ρ (x i).q (y i).a) = 0
    simp_rw [hg]
    calc
      _ = (∑ i, (x i).a) + ρ g (∑ i, (y i).a) := by
        rw [Finset.sum_add_distrib, map_sum]
      _ = 0 := by rw [hx, hy, map_zero, add_zero]
  inv_mem' := by
    rintro x ⟨⟨g, hg⟩, hx⟩
    refine ⟨⟨g⁻¹, fun i => by simp [hg i]⟩, ?_⟩
    change (∑ i, -(ρ (x i).q⁻¹ (x i).a)) = 0
    simp_rw [hg]
    rw [Finset.sum_neg_distrib, ← map_sum, hx, map_zero, neg_zero]

/-- A single coordinate subgroup, without identifying any quotient as a group. -/
def coordinate (i : I) (p : Point ρ) : I → Point ρ := by
  classical
  exact fun j => if j = i then p else 1

@[simp] theorem coordinate_self (i : I) (p : Point ρ) :
    coordinate ρ i p i = p := by
  classical
  simp [coordinate]

@[simp] theorem coordinate_one (i : I) :
    coordinate ρ i (1 : Point ρ) = 1 := by
  classical
  funext j
  simp [coordinate]

theorem coordinate_mul (i : I) (p q : Point ρ) :
    coordinate ρ i (p * q) = coordinate ρ i p * coordinate ρ i q := by
  classical
  funext j
  by_cases h : j = i <;> simp [coordinate, h]

theorem coordinate_commute {i j : I} (hij : i ≠ j)
    (p q : Point ρ) :
    coordinate ρ i p * coordinate ρ j q = coordinate ρ j q * coordinate ρ i p := by
  classical
  funext k
  by_cases hi : k = i
  · subst k
    simp [coordinate, hij, Ne.symm hij]
  · by_cases hj : k = j
    · subst k
      simp [coordinate, hi]
    · simp [coordinate, hi, hj]

/-- The coordinate subgroup is normal in the product, proved by a direct formula. -/
theorem conjugate_coordinate (i : I) (p : Point ρ)
    (h : I → Point ρ) :
    h⁻¹ * (coordinate ρ i p * h) = coordinate ρ i ((h i)⁻¹ * p * h i) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinate, mul_assoc]
  · simp [coordinate, hj]

/-- G02: `H_i ∩ Λ = {1}` whenever there is another direction. -/
theorem coordinate_mem_lambda_iff [Fintype I] (i : I)
    (hother : ∃ j : I, j ≠ i) (p : Point ρ) :
    coordinate ρ i p ∈ lambda (I := I) ρ ↔ p = 1 := by
  classical
  constructor
  · rintro ⟨⟨g, hg⟩, ha⟩
    rcases hother with ⟨j, hj⟩
    have hg1 : g = 1 := by simpa [coordinate, hj] using (hg j).symm
    have hpq : p.q = 1 := by simpa [hg1] using hg i
    have hpa : p.a = 0 := by simpa [coordinate, apply_ite] using ha
    exact Point.ext hpa hpq
  · rintro rfl
    rw [coordinate_one]
    exact (lambda (I := I) ρ).one_mem

section LeftCosets

variable {G : Type*} [Group G]

/-- Left multiplication descends to left cosets for an arbitrary subgroup. -/
def leftAction (L : Subgroup G) (g : G) : G ⧸ L → G ⧸ L :=
  Quotient.map' (fun h => g * h) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)

@[simp] theorem leftAction_mk (L : Subgroup G) (g h : G) :
    leftAction L g (QuotientGroup.mk h) = QuotientGroup.mk (g * h) := rfl

@[simp] theorem leftAction_one (L : Subgroup G) (x : G ⧸ L) : leftAction L 1 x = x := by
  refine QuotientGroup.induction_on x ?_
  intro h
  simp

theorem leftAction_mul (L : Subgroup G) (g h : G) (x : G ⧸ L) :
    leftAction L (g * h) x = leftAction L g (leftAction L h x) := by
  refine QuotientGroup.induction_on x ?_
  intro z
  simp [mul_assoc]

theorem leftAction_commute (L : Subgroup G) {g h : G} (hc : g * h = h * g) (x : G ⧸ L) :
    leftAction L g (leftAction L h x) = leftAction L h (leftAction L g x) := by
  rw [← leftAction_mul, hc, leftAction_mul]

end LeftCosets

/-- Freeness at every coset, not only at the identity coset. -/
theorem coordinate_action_free [Fintype I] (i : I) (hother : ∃ j : I, j ≠ i)
    (p : Point ρ)
    (x : (I → Point ρ) ⧸ lambda (I := I) ρ) :
    leftAction (lambda (I := I) ρ) (coordinate ρ i p) x = x → p = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro h hfix
  have hm : h⁻¹ * (coordinate ρ i p * h) ∈ lambda (I := I) ρ :=
    QuotientGroup.eq.mp hfix.symm
  rw [conjugate_coordinate] at hm
  have heq := (coordinate_mem_lambda_iff ρ i hother _).mp hm
  have hcancel := congrArg (fun z => h i * z * (h i)⁻¹) heq
  simpa [mul_assoc] using hcancel

section Counting

variable [Fintype I] [Fintype A] [Fintype Q]

def pointEquiv : Point ρ ≃ A × Q where
  toFun p := (p.a, p.q)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

local instance pointFintype : Fintype (Point ρ) :=
  Fintype.ofEquiv (A × Q) (pointEquiv ρ).symm

/-- The last translation is determined by all the others. -/
def lambdaEquiv : (lambda (I := Option I) ρ) ≃ ((I → A) × Q) where
  toFun x := (fun i => (x.val (some i)).a, (x.val none).q)
  invFun v := ⟨fun o => ⟨o.elim (-(∑ i, v.1 i)) v.1, v.2⟩, by
    refine ⟨⟨v.2, fun _ => rfl⟩, ?_⟩
    simp [Fintype.sum_option]⟩
  left_inv x := by
    apply Subtype.ext
    funext o
    apply Point.ext
    · cases o with
      | none =>
          have hs : (x.val none).a + ∑ i, (x.val (some i)).a = 0 := by
            simpa [Fintype.sum_option] using x.property.2
          have hc := congrArg (fun z => z - ∑ i, (x.val (some i)).a) hs
          simpa using hc.symm
      | some i => rfl
    · rcases x.property.1 with ⟨g, hg⟩
      exact (hg none).trans (hg o).symm
  right_inv v := by cases v; rfl

/-- Exact subgroup size for `t = card I + 1`. -/
theorem card_lambda :
    Nat.card (lambda (I := Option I) ρ) =
      Fintype.card A ^ Fintype.card I * Fintype.card Q := by
  classical
  rw [Nat.card_congr (lambdaEquiv (I := I) ρ), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_fun]

/-- Exact left-coset count, without normality. -/
theorem card_cosets :
    Nat.card ((Option I → Point ρ) ⧸ lambda (I := Option I) ρ) =
      Fintype.card A * Fintype.card Q ^ Fintype.card I := by
  classical
  let L := lambda (I := Option I) ρ
  have hp : Fintype.card (Point ρ) = Fintype.card A * Fintype.card Q := by
    rw [Fintype.card_congr (pointEquiv ρ), Fintype.card_prod]
  have hcard : Nat.card (Option I → Point ρ) =
      (Fintype.card A * Fintype.card Q) ^ (Fintype.card I + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_option, hp]
  have hlag := L.card_mul_index
  dsimp only [L] at hlag
  rw [card_lambda, hcard] at hlag
  have hpos : 0 < Fintype.card A ^ Fintype.card I * Fintype.card Q := by
    have hA : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
    have hQ : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨1⟩
    positivity
  change L.index = _
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = (Fintype.card A * Fintype.card Q) ^ (Fintype.card I + 1) := hlag
    _ = _ := by simp only [mul_pow, pow_succ]; ring

end Counting
end
end SemidirectQLTC.Geometry
