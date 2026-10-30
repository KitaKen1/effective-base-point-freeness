/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.BlowUpLiftPoints
public import Hironaka.Scheme.BlowUp.BlowUpMap

/-!+Principalizing the inverse image of a base ideal on a source SNC model constructs the
commuting morphism to the base blow-up. Its dominance and properness are consequences of
the original proper dominant morphism. No lift or commuting-square certificate is an input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Dominance preserves avoidance of the generic point by the support of a pulled-back ideal. -/
theorem ideal_comap_genericPoint_notMem_support {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (g : X ⟶ Y) [IsDominant g] (I : Y.IdealSheafData)
    (hη : genericPoint Y ∉ (I.support : Set Y)) :
    genericPoint X ∉ ((I.comap g).support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  change g (genericPoint X) ∉ (I.support : Set Y)
  rwa [dominant_map_genericPoint]

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A proper dominant morphism has a projective birational SNC source model over any base
blow-up whose centre avoids the generic point. The same SNC family contains the divisor
principalizing the pulled-back base ideal. -/
theorem exists_snc_source_model_over_base_blowUp (g : X ⟶ Y) [IsProper g] [IsDominant g]
    [g.IsOver (Spec (CommRingCat.of K))] (I : Y.IdealSheafData)
    (hη : genericPoint Y ∉ (I.support : Set Y))
    [I.blowUp.Over (Spec (CommRingCat.of K))]
    [I.blowUpπ.IsOver (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (π : T ⟶ X) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K)))
      (_ : IsProper π) (_ : IsProjective π)
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (N : ℕ) (e : X ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
        e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K) →
        ∃ (M : ℕ) (e' : T ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
          e' ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K)) ∧
      ∃ (q : T ⟶ I.blowUp) (_ : IsDominant q) (_ : IsProper q)
        (_ : q.IsOver (Spec (CommRingCat.of K))), q ≫ I.blowUpπ = π ≫ g ∧
        (I.comap (π ≫ g)).IsInvertible ∧
        ∃ (E : CartierDivisor T) (hE : E.IsEffective),
          effectiveCartierIdealSheaf E hE = I.comap (π ≫ g) ∧
          ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
            cartierCoefficient E (t : T) = 0 := by
  classical
  let 𝔠 : Fin 1 → X.IdealSheafData := fun _ => I.comap g
  have h𝔠 : ∀ j, genericPoint X ∉ ((𝔠 j).support : Set X) :=
    fun _ => ideal_comap_genericPoint_notMem_support g I hη
  obtain ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
      hinj, hcod, hsnc, hB, -, hemb, -, hpr⟩ :=
    exists_projective_snc_model_principalizing c f d D (fun j : Empty => j.elim) 𝔠 h𝔠
  have hBi : IsIntegral I.blowUp := blowUp_isIntegral_of_genericPoint_notMem_support I hη
  have hInv : (I.comap (π ≫ g)).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (hpr 0).1
  let q : T ⟶ I.blowUp := Scheme.IdealSheafData.blowUp.lift I (π ≫ g) hInv
  have hq : q ≫ I.blowUpπ = π ≫ g := Scheme.IdealSheafData.blowUp.lift_π I (π ≫ g) hInv
  have hqdom : IsDominant q := blowUp_lift_isDominant I hη (π ≫ g) q hq
  have hqprop : IsProper q := by
    have hIprop : IsProper I.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π I
    have : IsProper (q ≫ I.blowUpπ) := by rw [hq]; infer_instance
    exact IsProper.of_comp q I.blowUpπ
  have hqover : q.IsOver (Spec (CommRingCat.of K)) := ⟨by
    rw [← HomIsOver.comp_over (f := I.blowUpπ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hq, Category.assoc, HomIsOver.comp_over, HomIsOver.comp_over]⟩
  obtain ⟨E, hE, hEI, hEsupp⟩ := (hpr 0).2.2
  refine ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
    hinj, hcod, hsnc, hB, hemb, q, hqdom, hqprop, hqover, hq, hInv, E, hE, ?_, hEsupp⟩
  rw [Scheme.IdealSheafData.comap_comp]
  exact hEI

end MixedFujita
