/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CotangentTransverseDifferential
public import MixedFujita.CartierSectionSNC
public import MixedFujita.EtaleChartStalkParameterExtension

/-!
At any point of an actual etale chart, a regular function transverse to the
protected coordinate ideal has a nonvanishing partial derivative outside
those coordinates. Use the actual germ map and its localization algebra,
so no rationality or closed-point hypothesis is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing KaehlerDifferential

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- An actual transverse germ detects a partial derivative away from the protected coordinates. -/
theorem exists_coordinateDerivation_mem_basicOpen_of_transverse_germ
    (c : EtaleChart K X n) (S : Finset (Fin n)) (g : Γ(X, c.U)) (x : X) (hx : x ∈ c.U)
    (hS : ∀ j ∈ S, X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X j)) ∈
      maximalIdeal (X.presheaf.stalk x))
    (hg : X.presheaf.germ c.U x hx g ∈ maximalIdeal (X.presheaf.stalk x))
    (htrans : X.presheaf.germ c.U x hx g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      Ideal.span (Set.range fun j : S => X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X j)))) :
    ∃ j ∉ S, x ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j g) := by
  classical
  let A := Γ(X, c.U)
  let R := X.presheaf.stalk x
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := c.isAffine.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra K R := ((X.presheaf.germ c.U x hx).hom.comp (algebraMap K A)).toAlgebra
  letI : IsScalarTower K A R := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K A := sectionsBaseOpen_finiteType (K := K) c.isAffine
  haveI : Algebra.EssFiniteType A R := Algebra.EssFiniteType.of_isLocalization (S := R)
    (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  haveI : Algebra.EssFiniteType K R := Algebra.EssFiniteType.comp K A R
  haveI : Algebra.EssFiniteType K (ResidueField R) :=
    inferInstanceAs (Algebra.EssFiniteType K (R ⧸ maximalIdeal R))
  have hD : D K A g = ∑ j, etaleCoordinateDerivation c.coords c.formallyEtale j g •
      D K A (c.coords (MvPolynomial.X j)) := by
    conv_lhs => rw [← (etaleCoordinateBasis c.coords c.formallyEtale).sum_repr (D K A g)]
    apply Finset.sum_congr rfl
    intro j _
    rw [etaleCoordinateBasis_apply, etaleCoordinateDerivation_apply]
  have hDR : D K R (algebraMap A R g) =
      ∑ j, algebraMap A R (etaleCoordinateDerivation c.coords c.formallyEtale j g) •
        D K R (algebraMap A R (c.coords (MvPolynomial.X j))) := by
    have h := congrArg (KaehlerDifferential.map K K A R) hD
    simpa only [KaehlerDifferential.map_D, map_sum, map_smul, algebraMap_smul] using h
  obtain ⟨j, hj, hjm⟩ := transverse_element_exists_differential_coefficient_notMem (K := K)
    (fun j => algebraMap A R (c.coords (MvPolynomial.X j))) S hS
    (algebraMap A R g) hg htrans
    (fun j => algebraMap A R (etaleCoordinateDerivation c.coords c.formallyEtale j g)) hDR
  refine ⟨j, hj, (X.mem_basicOpen _ x hx).mpr ?_⟩
  have hunit : IsUnit (algebraMap A R (etaleCoordinateDerivation c.coords c.formallyEtale j g)) := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hjm
  have heq : algebraMap A R (etaleCoordinateDerivation c.coords c.formallyEtale j g) =
      X.presheaf.germ c.U x hx (etaleCoordinateDerivation c.coords c.formallyEtale j g) := rfl
  rw [← heq]
  exact hunit

end MixedFujita
