/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompatibleSmoothBaseSNCModel
public import MixedFujita.SteinBirationalModelInvariance
public import MixedFujita.SmoothStalkNormality

/-!
The compatible smooth base and klt SNC source models carry the actual Stein condition.
It is derived from the original all-open isomorphisms, via relative algebraic closure,
properness and normality of the constructed smooth base. Connected fibers follow from
Zariski connectedness. No new contraction certificate is an additional input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n k : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- An original normal klt Stein morphism has compatible smooth base and projective SNC
source models whose new proper dominant morphism also satisfies the all-open Stein condition
and has connected fibers. Its crepant boundary support and strict coefficient bounds are retained. -/
theorem exists_compatible_smooth_base_klt_stein_snc_models
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)
    (cY : EtaleChart K Y k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) :
    ∃ I : Y.IdealSheafData, (I.support : Set Y) = Y.singularLocus ∧
      genericPoint Y ∉ (I.support : Set Y) ∧
      ∃ (_ : IsIntegral I.blowUp) (_ : I.blowUp.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian I.blowUp)
        (_ : SmoothOfRelativeDimension k (I.blowUp ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant I.blowUpπ) (_ : I.blowUpπ.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper I.blowUpπ) (_ : IsProjective I.blowUpπ)
        (cB : EtaleChart K I.blowUp k),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) I.blowUpπ) ∧
        (∀ (N : ℕ) (e : Y ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
          e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K) →
          ∃ (M : ℕ) (e' : I.blowUp ⟶ polynomialProjectiveScheme M K),
            IsClosedImmersion e' ∧
            e' ≫ polynomialProjectiveToBase M K = I.blowUp ↘ Spec (CommRingCat.of K)) ∧
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
          (∀ i, cartierCoefficient
            (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) (ξ i) < (d : ℤ)) ∧
          (∀ (N : ℕ) (e : X ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
            e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K) →
            ∃ (M : ℕ) (e' : T ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
              e' ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K)) ∧
          ∃ (q : T ⟶ I.blowUp) (_ : IsDominant q) (_ : IsProper q)
            (_ : q.IsOver (Spec (CommRingCat.of K))), q ≫ I.blowUpπ = π ≫ g ∧
            (∀ V : I.blowUp.Opens, Function.Bijective (q.app V).hom) ∧
            (∀ b : I.blowUp, ConnectedSpace (q.fiber b)) ∧
            (I.comap (π ≫ g)).IsInvertible ∧
            ∃ (E : CartierDivisor T) (hE : E.IsEffective),
              effectiveCartierIdealSheaf E hE = I.comap (π ≫ g) ∧
              ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
                cartierCoefficient E (t : T) = 0 := by
  obtain ⟨I, hsupp, hη, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj, cB,
      hρ, hembB, T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
      hinj, hcod, hsnc, hB, hb, hembT, q, hqdom, hqprop, hqover, hq, hInv, E, hE, hEI, hEsupp⟩ :=
    exists_compatible_smooth_base_klt_snc_source_models g cY c f d hd D hklt
  have hBSmooth : Smooth (I.blowUp ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth k _
  have hnormB : ∀ b : I.blowUp, IsIntegrallyClosed (I.blowUp.presheaf.stalk b) :=
    fun b => smooth_stalk_isIntegrallyClosed (K := K) b
  have hqapp := stein_all_open_app_bijective_of_birational_square g π I.blowUpπ q
    hnormX hnormB (fun U => (happ U).2) hπ hρ hq
  have hqiso (V : I.blowUp.Opens) : IsIso (q.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hqapp V)
  have hconnected := zariskiConnectednessStatement T I.blowUp q hqiso
  exact ⟨I, hsupp, hη, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj, cB,
    hρ, hembB, T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
    hinj, hcod, hsnc, hB, hb, hembT, q, hqdom, hqprop, hqover, hq, hqapp, hconnected,
    hInv, E, hE, hEI, hEsupp⟩

end MixedFujita
