/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogCanonicalNonproperBirationalTests
public import MixedFujita.KltNonproperBirationalTests
public import MixedFujita.LogCanonicalProperCrepantDescent

/-!
Proper crepant birational changes preserve the actual base-point klt and lc predicates.
The strict descent proof lifts each test valuation locally and compares discrepancies on
its actual stalk; the converse uses the existing dictionary for nonproper birational tests.
No boundary effectivity is required.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The original all-model klt predicate descends along a proper actual crepant birational model. -/
theorem logPairIsKltOverBasePoint_of_proper_crepant_pullback
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (cT : EtaleChart K T n)
    (hlc : LogPairIsKltOverBasePoint (ρ ≫ g) η cT
      (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D)) :
    LogPairIsKltOverBasePoint g η c f d D := by
  intro U _ _ _ _ σ _ _ _ hσ cU x hx hxη
  let x : CodimensionOnePoint U := ⟨x, hx⟩
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  letI : Nonempty W := ⟨⟨(x : U), hx⟩⟩
  letI : IsIntegral W.toScheme := hW
  letI : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  haveI : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant α := hdom
  letI : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  haveI : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨(x : U), hx⟩
  have hw : Order.coheight w = 1 := by
    exact (coheight_eq_of_stalkMap_bijective W.ι w
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))).trans x.property
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ e : EtaleChart K W.toScheme n, w ∈ e.U from
      TopologicalSpace.Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
          TopologicalSpace.Opens.mem_top w))⟩
  have hηW : η ∈ closure ({(α ≫ (ρ ≫ g)) (p : W.toScheme)} : Set Y) := by
    have heq : (α ≫ (ρ ≫ g)) (p : W.toScheme) = (σ ≫ g) (x : U) := by
      rw [← Category.assoc, hcomm, Category.assoc]
      rfl
    simpa only [heq] using hxη
  have h := logPairIsKltOverBasePoint_discrepancy_bound_on_birational_test
    (ρ ≫ g) η cT (crepantPullbackFormUnit ρ hρ c f cT) d hd (cartierPullback ρ D)
    hlc α hα cW p hηW
  rw [← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover] at h
  have h' : -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n (W.ι ≫ σ)
        (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι)
        c f d D cW etaleCharts_cover) (p : W.toScheme) := by
    simpa only [hcomm] using h
  have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
    σ W.ι hσ hι c f d D cU cW p x.property
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))
  simpa [heq, p, w] using h'

variable [IsLocallyNoetherian X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- Base-point klt is invariant under an actual proper crepant birational pullback. -/
theorem logPairIsKltOverBasePoint_iff_proper_crepant_pullback
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (cT : EtaleChart K T n) :
    LogPairIsKltOverBasePoint g η c f d D ↔
      LogPairIsKltOverBasePoint (ρ ≫ g) η cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) :=
  ⟨fun h => logPairIsKltOverBasePoint_crepant_pullback_without_properness ρ hρ
      g η c f d hd D h cT,
    logPairIsKltOverBasePoint_of_proper_crepant_pullback ρ hρ g η c f d hd D cT⟩

/-- Base-point lc is invariant under the same actual proper crepant birational pullback. -/
theorem logPairIsLogCanonicalOverBasePoint_iff_proper_crepant_pullback
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (cT : EtaleChart K T n) :
    LogPairIsLogCanonicalOverBasePoint g η c f d D ↔
      LogPairIsLogCanonicalOverBasePoint (ρ ≫ g) η cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) :=
  ⟨fun h => logPairIsLogCanonicalOverBasePoint_crepant_pullback_without_properness ρ hρ
      g η c f d hd D h cT,
    logPairIsLogCanonicalOverBasePoint_of_proper_crepant_pullback ρ hρ g η c f d hd D cT⟩

end MixedFujita
