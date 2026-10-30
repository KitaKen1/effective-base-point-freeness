/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveIntegral
public import MixedFujita.CartierSectionSNCPerturbation
public import MixedFujita.CoordinateExceptionalStandardBaseChange
public import Hironaka.Scheme.Smooth.ExceptionalBundle

/-! Integrality of actual exceptional schemes, from the projective fibers of
a smooth center or from the coordinate base-change model. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme.IdealSheafData
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem scheme_irreducible_of_open_integral_fibers
    {Y Z : Scheme.{u}} [IrreducibleSpace Z] (q : Y ⟶ Z)
    (hq : IsOpenMap q) (hf : ∀ z, IsIntegral (q.fiber z)) : IrreducibleSpace Y := by
  have hpre : ∀ z, IsPreirreducible (q ⁻¹' {z}) := by
    intro z
    let := hf z
    rw [← q.range_fiberι z, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).2.image _
      (q.fiberι z).continuous.continuousOn
  have hY : IsPreirreducible (Set.univ : Set Y) := by
    simpa only [Set.preimage_univ] using
      (IrreducibleSpace.isIrreducible_univ Z).2.preimage_of_isPreirreducible_fiber q hq hpre
  let z : Z := Classical.arbitrary Z
  let := hf z
  exact { isPreirreducible_univ := hY
          toNonempty := ⟨q.fiberι z (Classical.arbitrary (q.fiber z))⟩ }

theorem smoothCentre_exceptional_isIntegral
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)]
    [IsIntegral Z.subscheme] (hrn : r ≤ n) (hr : 0 < r) :
    IsIntegral Z.exceptionalDivisor.subscheme := by
  let q := subschemeMap (Z.comap Z.blowUpπ) Z Z.blowUpπ (le_map_comap Z Z.blowUpπ)
  have hfib (z : Z.subscheme) : IsIntegral (q.fiber z) := by
    obtain ⟨e, _⟩ := exists_iso_fiber_proj f n r Z hrn z
    let := polynomialProjectiveScheme_isIntegral (Z.subscheme.residueField z) ⟨0, hr⟩
    exact IsIntegral.of_isIso e.inv
  let := smoothOfRelativeDimension_subschemeMap_exceptional f n r Z hrn
  let : Smooth q := SmoothOfRelativeDimension.smooth (r - 1) q
  let : IrreducibleSpace Z.exceptionalDivisor.subscheme :=
    scheme_irreducible_of_open_integral_fibers q q.isOpenMap hfib
  let : Smooth (Z.exceptionalDivisor.subschemeι ≫ Z.blowUpπ ≫ f) :=
    smooth_exceptional f n r Z hrn
  let : IsReduced Z.exceptionalDivisor.subscheme :=
    smoothScheme_isReduced (Z.exceptionalDivisor.subschemeι ≫ Z.blowUpπ ≫ f)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem coordinateBaseChanged_exceptional_isIntegral
    (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n) (hr : 0 < r)
    {S : Type u} [CommRing S] (φ : MvPolynomial (Fin n) A →+* S) (hφ : φ.Flat)
    [(CoordinateSubspace.centerIdeal A n r).map φ |>.IsPrime] :
    IsIntegral (affineBlowUp.exceptionalIdeal ((CoordinateSubspace.centerIdeal A n r).map φ)).subscheme := by
  let := polynomialProjectiveScheme_isIntegral
    (S ⧸ (CoordinateSubspace.centerIdeal A n r).map φ) ⟨0, hr⟩
  exact IsIntegral.of_isIso (coordinateBaseChangedExceptionalProjectiveIso A n r hrn φ hφ).inv

end MixedFujita
