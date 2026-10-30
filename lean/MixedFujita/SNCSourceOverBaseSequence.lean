/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModelOverBaseBlowUp
public import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp

/-! Compress a base blow-up sequence to one actual blow-up, reuse the existing
source principalization, and transport its lift back through the actual isomorphism.
The compatible source model, commuting square and projectivity are constructed. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- An actual base blow-up sequence avoiding the generic point has a compatible SNC source. -/
theorem exists_snc_source_model_over_base_sequence (g : X ⟶ Y)
    [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (S : Scheme.BlowUpSequence Y) (Z : Closeds Y)
    (hc : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set Y))
    (hZη : genericPoint Y ∉ (Z : Set Y))
    [IsIntegral S.last] [S.last.Over (Spec (CommRingCat.of K))]
    [S.composite.IsOver (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (π : T ⟶ X) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K)))
      (_ : IsProper π) (_ : IsProjective π)
      (_ : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)))
      (_ : QuasiCompact (T ↘ Spec (CommRingCat.of K)))
      (_ : IsSeparated (T ↘ Spec (CommRingCat.of K)))
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
      ∃ (q : T ⟶ S.last) (_ : IsDominant q) (_ : IsProper q)
        (_ : q.IsOver (Spec (CommRingCat.of K))), q ≫ S.composite = π ≫ g := by
  classical
  obtain ⟨I, hIsupp, e, he, -⟩ := exists_blowUp_composite_iso S
  have hηI : genericPoint Y ∉ (I.support : Set Y) := by
    intro h
    rw [hIsupp] at h
    obtain ⟨i, z, hz, hmap⟩ := Set.mem_iUnion.mp h
    exact hZη (hmap ▸ hc i z hz)
  have hIint : IsIntegral I.blowUp := blowUp_isIntegral_of_genericPoint_notMem_support I hηI
  let instI : I.blowUp.Over (Spec (CommRingCat.of K)) :=
    ⟨I.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have hIover : I.blowUpπ.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have heinv : e.inv ≫ S.composite = I.blowUpπ := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have heover : e.inv.IsOver (Spec (CommRingCat.of K)) := ⟨by
    change e.inv ≫ (S.last ↘ Spec (CommRingCat.of K)) =
      I.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))
    rw [← HomIsOver.comp_over (f := S.composite) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, heinv]⟩
  obtain ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj, hπ, cT, r, ξ,
      hinj, hcod, hsnc, hB, hemb, q', hq'dom, hq'prop, hq'over, hq', -⟩ :=
    exists_snc_source_model_over_base_blowUp g I hηI c f d D
  have hTS : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hTft : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := inferInstance
  have hTqc : QuasiCompact (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hTsep : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  let q : T ⟶ S.last := q' ≫ e.inv
  have hqdom : IsDominant q := inferInstanceAs (IsDominant (q' ≫ e.inv))
  have hqprop : IsProper q := inferInstanceAs (IsProper (q' ≫ e.inv))
  have hqover : q.IsOver (Spec (CommRingCat.of K)) := inferInstanceAs
    ((q' ≫ e.inv).IsOver (Spec (CommRingCat.of K)))
  refine ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, r, ξ, hinj, hcod, hsnc, hB, hemb,
    q, hqdom, hqprop, hqover, ?_⟩
  change (q' ≫ e.inv) ≫ S.composite = π ≫ g
  rw [Category.assoc, heinv, hq']

end MixedFujita
