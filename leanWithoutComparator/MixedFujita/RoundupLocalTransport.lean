/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierRoundupConstruction
public import MixedFujita.EffectiveCartierIdealProduct
public import MixedFujita.BirationalComposition
public import MixedFujita.FixedIdealLemmaThree

/-! Transport a globally established rounded-divisor decomposition to a local
coordinate blow-up. Equality of actual center ideals identifies the pulled
exceptional Cartier divisor. The projective model, conormal, and positive
cohomology vanishing are supplied by the existing coordinate construction.
No new round-up calculation or relative canonical chart on the local base is
required. The commuting dominant square and center coordinate ideal remain
explicit geometric inputs. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CoordinateSubspace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cartier_decomposition_pullback_square
    {X T S Y : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral S] [IsIntegral Y]
    (f : T ⟶ X) (g : Y ⟶ S) (σ : S ⟶ X) (τ : Y ⟶ T)
    [IsDominant f] [IsDominant g] [IsDominant σ] [IsDominant τ]
    (hsq : τ ≫ f = g ≫ σ) (Q : CartierDivisor X) (C E : CartierDivisor T)
    (j : ℕ) (hC : C = cartierPullback f Q + j • E) :
    cartierPullback τ C = cartierPullback g (cartierPullback σ Q) +
      j • cartierPullback τ E := by
  rw [hC, cartierPullback_add, cartierPullback_nsmul, ← cartierPullback_comp,
    cartierPullback_congr_hom hsq, cartierPullback_comp]

theorem effective_cartier_pullback_eq_of_center_square
    {X T S Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : T ⟶ X) (g : Y ⟶ S) (σ : S ⟶ X) (τ : Y ⟶ T) [IsDominant τ]
    (hsq : τ ≫ f = g ≫ σ) (Z : X.IdealSheafData) (I : S.IdealSheafData)
    (hI : Z.comap σ = I) (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.comap f)
    (E' : CartierDivisor Y) (hE' : E'.IsEffective)
    (hE'I : effectiveCartierIdealSheaf E' hE' = I.comap g) :
    cartierPullback τ E = E' := by
  apply effectiveCartier_eq_of_idealSheaf_eq _ _ (cartierPullback_isEffective τ E hE) hE'
  rw [effectiveCartierIdealSheaf_cartierPullback τ E hE, hEI, hE'I,
    ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp, hI]

set_option maxHeartbeats 800000 in
theorem coordinateLocal_roundup_pullback_vanish
    (A : Type u) [CommRing A] [IsDomain A] (n r : ℕ)
    {S : Type u} [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : MvPolynomial (Fin n) A →+* S) (hφ : φ.Flat) (hs : r + 1 ≤ n)
    (hJ : (centerIdeal A n (r + 1)).map φ ≠ ⊤)
    [IsDominant (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))]
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (f : T ⟶ X) [IsDominant f] (σ : Spec (CommRingCat.of S) ⟶ X) [IsDominant σ]
    (τ : affineBlowUp ((centerIdeal A n (r + 1)).map φ) ⟶ T) [IsDominant τ]
    (hsq : τ ≫ f = affineBlowUp.π ((centerIdeal A n (r + 1)).map φ) ≫ σ)
    (Z : X.IdealSheafData)
    (hZ : Z.comap σ = specIdealSheaf ((centerIdeal A n (r + 1)).map φ))
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.comap f)
    (Q : CartierDivisor X) (C : CartierDivisor T) (j : ℕ) (hj : j ≤ r)
    (hC : C = cartierPullback f Q + j • E) :
    let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
      (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
    Nonempty ((Scheme.Modules.pullback
      (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)).obj
        (cartierPullback τ C).sheaf ≅
          projectiveSpace.twist (Fin (r + 1)) (S ⧸ (centerIdeal A n (r + 1)).map φ) (-(j : ℤ))) ∧
    ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology (cartierPullback τ C).sheaf (q + 1)) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n (r + 1)).map φ)
    (coordinateBaseChanged_center_ne_bot A n (r + 1) hs φ (Nat.zero_lt_succ _) hφ)
  let : IsLocallyNoetherian (affineBlowUp ((centerIdeal A n (r + 1)).map φ)) :=
    LocallyOfFiniteType.isLocallyNoetherian (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))
  dsimp only
  obtain ⟨E', hE', hE'I, hv⟩ := coordinateLocal_exists_exceptional_cartier_vanishing
    A n r φ hφ hs hJ
  have hEE : cartierPullback τ E = E' :=
    effective_cartier_pullback_eq_of_center_square f _ σ τ hsq Z _ hZ E hE hEI E' hE' hE'I
  have heq : cartierPullback τ C =
      cartierPullback (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ)) (cartierPullback σ Q) +
        j • E' := by
    rw [cartier_decomposition_pullback_square f _ σ τ hsq Q C E j hC, hEE]
  let P := cartierPullback σ Q
  let g := affineBlowUp.π ((centerIdeal A n (r + 1)).map φ)
  let a : (cartierPullback g P).sheaf ≅ (Scheme.Modules.pullback g).obj P.sheaf :=
    localSpecActualCartierPullbackFrameIso S g P ≪≫ (localSpecCartierPullbackFrameIso S g P).symm
  obtain ⟨hres, hvan⟩ := hv P (cartierPullback g P) ⟨a⟩
  rw [heq]
  constructor
  · simpa only [natCast_zsmul] using hres (j : ℤ)
  · intro q
    exact hvan j q (Or.inr hj)

end MixedFujita
