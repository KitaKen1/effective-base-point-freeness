/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Hironaka.Scheme.Snc.EtaleParameters
public import Hironaka.Algebra.Local.Defs
public import Hironaka.Algebra.Local.RegularSystem
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
A new element transverse to selected regular parameters can be added while
retaining those parameters exactly. Lift a finite residue-field linear
combination to the local ring, then extend the resulting independent cotangent
classes to a regular system. No parameter-exchange or basis certificate is input.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A cotangent linear combination lifts to membership in the square plus the generated ideal. -/
theorem cotangent_mem_span_implies_mem_sq_sup_span
    {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type*} [Fintype ι]
    (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R) (a : R) (ha : a ∈ maximalIdeal R)
    (h : (maximalIdeal R).toCotangent ⟨a, ha⟩ ∈ Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩)) :
    a ∈ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range w) := by
  classical
  obtain ⟨ℓ, hℓ⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).mp h
  choose c hc using fun i => residue_surjective (R := R) (ℓ i)
  let b : maximalIdeal R := ∑ i, c i • (⟨w i, hw i⟩ : maximalIdeal R)
  have hb : (b : R) ∈ Ideal.span (Set.range w) := by
    simp only [b, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  have hcot : (maximalIdeal R).toCotangent b = (maximalIdeal R).toCotangent ⟨a, ha⟩ := by
    rw [show (maximalIdeal R).toCotangent b =
        ∑ i, ℓ i • (maximalIdeal R).toCotangent ⟨w i, hw i⟩ from ?_, hℓ]
    simp only [b, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i, ← ResidueField.algebraMap_eq, algebraMap_smul]
  have hdiff : a - (b : R) ∈ maximalIdeal R ^ 2 :=
    (Ideal.toCotangent_eq _).mp hcot.symm
  rw [show a = (a - (b : R)) + (b : R) by ring]
  exact Submodule.add_mem_sup hdiff hb

/-- Retain any selected regular parameters and add a transverse element as one further parameter. -/
theorem exists_regular_parameters_with_transverse_element
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (z : Fin n → R) (hz : IsRegularSystemOfParameters z)
    {ι : Type*} [Fintype ι] (c : ι → Fin n) (hcinj : Function.Injective c)
    (a : R) (ha : a ∈ maximalIdeal R)
    (htrans : a ∉ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range (z ∘ c))) :
    ∃ (m : ℕ) (y : Fin m → R), IsRegularSystemOfParameters y ∧
      ∃ τ : Option ι → Fin m, Function.Injective τ ∧
        y (τ none) = a ∧ ∀ i, y (τ (some i)) = z (c i) := by
  classical
  let hw : ∀ i, z (c i) ∈ maximalIdeal R :=
    fun i => x_mem_maximalIdeal_of_span_eq z hz.1.symm (c i)
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  have hli : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨z (c i), hw i⟩) := by
    convert b.linearIndependent.comp c hcinj using 1
    funext i
    exact (hb (c i)).symm
  have hnot : (maximalIdeal R).toCotangent ⟨a, ha⟩ ∉ Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨z (c i), hw i⟩) := by
    intro h
    exact htrans (cotangent_mem_span_implies_mem_sq_sup_span (z ∘ c) hw a ha h)
  let w : Option ι → R := fun i => i.elim a (z ∘ c)
  have hwm : ∀ i, w i ∈ maximalIdeal R := by
    intro i
    cases i with
    | none => exact ha
    | some i => exact hw i
  have hliw : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨w i, hwm i⟩) := by
    convert hli.option hnot using 1
    funext i
    cases i <;> rfl
  obtain ⟨m, y, hy, τ, hτ, hτy⟩ := exists_span_eq_maximalIdeal_of_linearIndependent w hwm hliw
  exact ⟨m, y, hy, τ, hτ, hτy none, fun i => hτy (some i)⟩

end MixedFujita
