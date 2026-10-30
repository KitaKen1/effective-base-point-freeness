/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBirationalPrimeLifts
public import Hironaka.Scheme.BlowUpSequence.SmoothParameters
public import Hironaka.Scheme.Snc.Coordinates
public import Hironaka.Algebra.RegularSmooth.Defs

/-!
A base DVR uniformizer is a regular parameter. At an actual smooth point over
that base prime, extend it to regular parameters of the actual source stalk.
Only local regularity of the source is used; global smoothness of the base is
unnecessary. The base is locally of finite type over a perfect field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- An actual DVR uniformizer is a one-element regular system of parameters. -/
theorem dvr_uniformizer_isRegularSystemOfParameters
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : Irreducible a) : IsRegularSystemOfParameters (fun _ : Fin 1 => a) := by
  constructor
  · simpa only [Set.range_const] using ha.maximalIdeal_eq.symm
  · simpa using (IsDiscreteValuationRing.ringKrullDim_eq_one R).symm

/-- At a smooth point over a normal base prime, the pulled uniformizer is an actual source parameter. -/
theorem smooth_base_prime_stalk_uniformizer_parameters
    {K : Type u} [Field K] [PerfectField K] {T Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [LocallyOfFinitePresentation g] (t : T)
    (hsm : t ∈ g.smoothLocus) (hcoh : Order.coheight (g t) = 1)
    [IsIntegrallyClosed (Y.presheaf.stalk (g t))] (hreg : T.IsRegularAt t)
    (a : Y.presheaf.stalk (g t)) (ha : Irreducible a) :
    ∃ (m : ℕ) (z : Fin m → T.presheaf.stalk t), IsRegularSystemOfParameters z ∧
      ∃ j : Fin m, z j = (g.stalkMap t).hom a := by
  letI := normal_codimensionOne_stalk_DVR (⟨g t, hcoh⟩ : CodimensionOnePoint Y)
  letI := (Y ↘ Spec (CommRingCat.of K)).stalkAlgebra (g t)
  letI : Algebra (Y.presheaf.stalk (g t)) (T.presheaf.stalk t) := (g.stalkMap t).hom.toAlgebra
  letI : Algebra K (T.presheaf.stalk t) :=
    ((g.stalkMap t).hom.comp (algebraMap K (Y.presheaf.stalk (g t)))).toAlgebra
  letI : IsScalarTower K (Y.presheaf.stalk (g t)) (T.presheaf.stalk t) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsRegularLocalRing (T.presheaf.stalk t) := hreg
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (g t)) (T.presheaf.stalk t)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap t).hom)
  haveI : Algebra.FormallySmooth (Y.presheaf.stalk (g t)) (T.presheaf.stalk t) :=
    (Scheme.Hom.mem_smoothLocus).mp hsm
  haveI : Algebra.EssFiniteType K (Y.presheaf.stalk (g t)) :=
    essFiniteType_stalk_of_locallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)) (g t)
  haveI : Algebra.EssFiniteType K (ResidueField (Y.presheaf.stalk (g t))) :=
    inferInstanceAs (Algebra.EssFiniteType K (_ ⧸ maximalIdeal (Y.presheaf.stalk (g t))))
  obtain ⟨m, z, hz, σ, hinj, hσ⟩ := exists_isRegularSystemOfParameters_extend (k := K)
    (A := Y.presheaf.stalk (g t)) (B := T.presheaf.stalk t)
    (fun _ : Fin 1 => a) (dvr_uniformizer_isRegularSystemOfParameters a ha)
  exact ⟨m, z, hz, σ 0, hσ 0⟩

/-- The pulled base uniformizer has nonzero class in the actual source cotangent space. -/
theorem smooth_base_prime_stalk_uniformizer_notMem_sq
    {K : Type u} [Field K] [PerfectField K] {T Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [LocallyOfFinitePresentation g] (t : T)
    (hsm : t ∈ g.smoothLocus) (hcoh : Order.coheight (g t) = 1)
    [IsIntegrallyClosed (Y.presheaf.stalk (g t))] (hreg : T.IsRegularAt t)
    (a : Y.presheaf.stalk (g t)) (ha : Irreducible a) :
    (g.stalkMap t).hom a ∈ maximalIdeal (T.presheaf.stalk t) ∧
      (g.stalkMap t).hom a ∉ maximalIdeal (T.presheaf.stalk t) ^ 2 := by
  letI : IsRegularLocalRing (T.presheaf.stalk t) := hreg
  obtain ⟨m, z, hz, j, hj⟩ := smooth_base_prime_stalk_uniformizer_parameters (K := K)
    g t hsm hcoh hreg a ha
  rw [← hj]
  exact mem_maximalIdeal_and_notMem_sq_of_span_eq hz j

end MixedFujita
