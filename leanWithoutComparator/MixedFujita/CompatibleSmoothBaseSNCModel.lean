/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothBaseBlowUpResolution
public import MixedFujita.SNCModelOverBaseBlowUp

/-!+Compatible smooth base and SNC source models of an original proper dominant klt pair.
Both modifications, the morphism between them, its commuting square and the strict crepant
boundary bounds are constructed internally. This is a model construction, not a proof of
the Stein condition, moduli descent or moduli positivity on the new base.
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

/-- An original klt pair over a proper dominant morphism admits compatible smooth base and
projective SNC source modifications. The source boundary may have negative coefficients;
its full support is retained and all its SNC coefficients are strictly below the denominator. -/
theorem exists_compatible_smooth_base_klt_snc_source_models
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
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
            (I.comap (π ≫ g)).IsInvertible ∧
            ∃ (E : CartierDivisor T) (hE : E.IsEffective),
              effectiveCartierIdealSheaf E hE = I.comap (π ≫ g) ∧
              ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
                cartierCoefficient E (t : T) = 0 := by
  classical
  have hYN : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  obtain ⟨I, hsupp, hη, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj, hρ, hembB⟩ :=
    exists_smooth_base_single_blowUp cY
  obtain ⟨cB⟩ : Nonempty (EtaleChart K I.blowUp k) := by
    obtain ⟨b⟩ : Nonempty I.blowUp := inferInstance
    exact ⟨Classical.choose (show ∃ e : EtaleChart K I.blowUp k, b ∈ e.U from
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := I.blowUp) (n := k)).symm ▸
        Opens.mem_top b))⟩
  obtain ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
      hinj, hcod, hsnc, hB, hembT, q, hqdom, hqprop, hqover, hq, hInv, E, hE, hEI, hEsupp⟩ :=
    exists_snc_source_model_over_base_blowUp g I hη c f d D
  have hTS : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hTsep : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hb := (logPairIsKlt_iff_crepant_snc_coefficients π hπ c f d hd D cT ξ hinj hcod
    hsnc hB).mp hklt
  exact ⟨I, hsupp, hη, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj, cB,
    hρ, hembB, T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
    hinj, hcod, hsnc, hB, hb, hembT, q, hqdom, hqprop, hqover, hq, hInv, E, hE, hEI, hEsupp⟩

end MixedFujita
