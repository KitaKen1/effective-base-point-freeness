/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalImageIdealNonvanishing
public import MixedFujita.HironakaSNCModelExistence

/-! Use the actual nonzero ideal in the existing SNC principalization theorem.
The generic-point hypothesis is supplied internally on the integral base.
The result retains marked Cartier supports and the actual effective Cartier
representation of the inverse-image ideal on a higher projective model. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {B : Scheme.{u}}
  [IsIntegral B] [B.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (B ↘ Spec (CommRingCat.of K))]
  [IsSeparated (B ↘ Spec (CommRingCat.of K))]

/-- A nonzero actual ideal has a higher smooth projective birational
principalizing model, with no supplied generic-point avoidance hypothesis. -/
theorem exists_projective_snc_model_principalizing_nonzero_ideal
    {ι : Type*} [Finite ι] (c : EtaleChart K B n) (f : B.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor B) (G : ι → CartierDivisor B)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) :
    ∃ (B' : Scheme.{u}) (_ : IsIntegral B') (_ : B'.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian B')
      (_ : SmoothOfRelativeDimension n (B' ↘ Spec (CommRingCat.of K)))
      (ρ : B' ⟶ B) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K)))
      (_ : IsProper ρ) (_ : IsProjective ρ)
      (_ : LocallyOfFiniteType (B' ↘ Spec (CommRingCat.of K)))
      (_ : QuasiCompact (B' ↘ Spec (CommRingCat.of K)))
      (_ : IsSeparated (B' ↘ Spec (CommRingCat.of K)))
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (c' : EtaleChart K B' n) (r : ℕ) (ξ : Fin r → B'),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D c' etaleCharts_cover)
          (t : B') = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint B'), (t : B') ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : B') = 0) ∧
      (∀ (N : ℕ) (e : B ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
        e ≫ polynomialProjectiveToBase N K = B ↘ Spec (CommRingCat.of K) →
        ∃ (M : ℕ) (e' : B' ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
          e' ≫ polynomialProjectiveToBase M K = B' ↘ Spec (CommRingCat.of K)) ∧
      (∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ →
        (t : B') ∉ (I.comap ρ).support) ∧
      (I.comap ρ).IsInvertible ∧
      (∃ a : B' ⟶ I.blowUp, a ≫ I.blowUpπ = ρ) ∧
      ∃ (P : CartierDivisor B') (hP : P.IsEffective),
        effectiveCartierIdealSheaf P hP = I.comap ρ ∧
        ∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ → cartierCoefficient P (t : B') = 0 := by
  obtain ⟨B', hBi, instB, hBN, hBsm, ρ, hρdom, hρover, hρprop, hρproj,
    hρ, c', r, ξ, hinj, hcod, hsnc, hboundary, hG, hemb, hoff, hall⟩ :=
    exists_projective_snc_model_principalizing c f d D G (fun _ : Unit => I)
      (fun _ => integral_genericPoint_notMem_support_of_ideal_ne_bot I hI)
  have hBft : LocallyOfFiniteType (B' ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hBqc : QuasiCompact (B' ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hBsep : IsSeparated (B' ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨hInv, hlift, P, hP, hPI, hPsupp⟩ := hall Unit.unit
  exact ⟨B', hBi, instB, hBN, hBsm, ρ, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, hρ, c', r, ξ, hinj, hcod, hsnc, hboundary, hG, hemb,
    hoff Unit.unit, hInv, hlift, P, hP, hPI, hPsupp⟩

end MixedFujita
