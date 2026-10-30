/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierConormalIntegerRestriction
public import MixedFujita.CoordinateBaseChangedProjectiveVanishing

/-! Whole-blowup Cartier vanishing over a Noetherian local domain.
The divisor class consists of a base pullback plus a nonnegative multiple
of the actual exceptional Cartier divisor. Identifying a general SNC
adjoint with this class is a separate obligation. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CoordinateSubspace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

theorem proper_localBase_cartier_vanish_of_projective_exceptional
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (I : Ideal R) (hI : I ≠ ⊤) (E : CartierDivisor X) (hE : E.IsEffective)
    (hJ : effectiveCartierIdealSheaf E hE = infinitesimalBaseIdealSheaf f I)
    (B : Type u) [CommRing B] (r : ℕ)
    (e : (effectiveCartierIdealSheaf E hE).subscheme ≅ polynomialProjectiveScheme (r + 1) B)
    (p : polynomialProjectiveScheme (r + 1) B ⟶ X) [IsClosedImmersion p]
    (hp : e.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = p)
    (a : (Scheme.Modules.pullback p).obj (-E).sheaf ≅ projectiveSpace.twist (Fin (r + 1)) B 1)
    (P : CartierDivisor (Spec (CommRingCat.of R))) (F : CartierDivisor X)
    (b : F.sheaf ≅ (Scheme.Modules.pullback f).obj P.sheaf)
    (k q : ℕ) (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology (F + k • E).sheaf (q + 1)) := by
  let := (F + k • E).isInvertible_sheaf
  let := invertible_module_isCoherent (F + k • E).sheaf
  have hjac : I ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.le_maximalIdeal hI).trans (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  let bP : (Scheme.Modules.pullback p).obj (F + k • E).sheaf ≅
      projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ)) := by
    simpa only [natCast_zsmul] using cartierLocalBasePlusConormalPowerIso R f p P F E b
      (projectiveSpace.twistingBundle (Fin (r + 1)) B) a (k : ℤ)
  exact proper_cartier_cohomology_vanish_of_projective_exceptional_divisor f I E hE hJ
    (F + k • E) B r k e p hp a bP hjac q h

variable (A : Type u) [CommRing A] [IsDomain A] (n r : ℕ)
  {S : Type u} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
  (φ : MvPolynomial (Fin n) A →+* S) (hφ : φ.Flat) (hs : r + 1 ≤ n)
noncomputable local instance coordinateLocalCartierQuotientCommRing :
    CommRing (S ⧸ (centerIdeal A n (r + 1)).map φ) := Ideal.Quotient.commRing _

theorem coordinateLocal_exists_exceptional_cartier_vanishing
    (hJ : (centerIdeal A n (r + 1)).map φ ≠ ⊤) :
    let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
      (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
    ∃ (E : CartierDivisor (affineBlowUp ((centerIdeal A n (r + 1)).map φ))) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal ((centerIdeal A n (r + 1)).map φ) ∧
      ∀ (P : CartierDivisor (Spec (CommRingCat.of S)))
        (F : CartierDivisor (affineBlowUp ((centerIdeal A n (r + 1)).map φ))),
        Nonempty (F.sheaf ≅ (Scheme.Modules.pullback
          (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))).obj P.sheaf) →
        (∀ j : ℤ, Nonempty ((Scheme.Modules.pullback
          (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)).obj (F + j • E).sheaf ≅
            projectiveSpace.twist (Fin (r + 1)) (S ⧸ (centerIdeal A n (r + 1)).map φ) (-j))) ∧
        ∀ k q : ℕ, q + 1 ≠ r ∨ k ≤ r →
          Subsingleton (Scheme.Modules.Cohomology (F + k • E).sheaf (q + 1)) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
    (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
  obtain ⟨E, hE, hEI, ⟨a⟩⟩ := coordinateBaseChanged_exists_standard_conormal A n (r + 1) hs φ hφ
    (Nat.zero_lt_succ _)
  refine ⟨E, hE, hEI, ?_⟩
  intro P F ⟨b⟩
  let p := coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ
  let e := idealSubschemeIsoOfClosedImmersion (effectiveCartierIdealSheaf E hE) p
    ((coordinateBaseChangedProjectiveImmersion_ker A n (r + 1) hs φ hφ).trans hEI.symm)
  have hp := idealSubschemeIsoOfClosedImmersion_inv_inclusion (effectiveCartierIdealSheaf E hE) p
    ((coordinateBaseChangedProjectiveImmersion_ker A n (r + 1) hs φ hφ).trans hEI.symm)
  constructor
  · intro j
    exact ⟨cartierLocalBasePlusConormalPowerIso S _ p P F E b
      (projectiveSpace.twistingBundle (Fin (r + 1)) _) a j⟩
  · intro k q h
    exact proper_localBase_cartier_vanish_of_projective_exceptional S _ _ hJ E hE hEI
      (S ⧸ (centerIdeal A n (r + 1)).map φ) r e p hp a P F b k q h

theorem coordinateLocal_exists_base_cartier_model_vanishing
    (hJ : (centerIdeal A n (r + 1)).map φ ≠ ⊤)
    (P : CartierDivisor (Spec (CommRingCat.of S))) :
    let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
      (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
    ∃ (E : CartierDivisor (affineBlowUp ((centerIdeal A n (r + 1)).map φ))) (hE : E.IsEffective)
      (F : CartierDivisor (affineBlowUp ((centerIdeal A n (r + 1)).map φ))),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal ((centerIdeal A n (r + 1)).map φ) ∧
      Nonempty (F.sheaf ≅ (Scheme.Modules.pullback
        (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))).obj P.sheaf) ∧
      (∀ j : ℤ, Nonempty ((Scheme.Modules.pullback
        (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)).obj (F + j • E).sheaf ≅
          projectiveSpace.twist (Fin (r + 1)) (S ⧸ (centerIdeal A n (r + 1)).map φ) (-j))) ∧
      ∀ k q : ℕ, q + 1 ≠ r ∨ k ≤ r →
        Subsingleton (Scheme.Modules.Cohomology (F + k • E).sheaf (q + 1)) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
    (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
  obtain ⟨E, hE, hEI, hv⟩ := coordinateLocal_exists_exceptional_cartier_vanishing A n r φ hφ hs hJ
  obtain ⟨F, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor P
    (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))
  exact ⟨E, hE, F, hEI, ⟨b.symm⟩, hv P F ⟨b.symm⟩⟩

end MixedFujita
