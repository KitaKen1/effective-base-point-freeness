/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierBlowupRoundupDecomposition
public import MixedFujita.CoordinateLocalCartierVanishing

/-! One-step signed roundup vanishing with explicit geometric input.
Total transforms, distinct strict-transform prime divisors and the exceptional
projective model imply the actual roundup decomposition and its positive
cohomology vanishing. Automatic construction of those prime and canonical
transformation data for a general SNC blow-up is still separate. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

noncomputable def localSpecActualCartierPullbackFrameIso
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    {T : Scheme.{u}} [IsIntegral T] (f : T ⟶ Spec (CommRingCat.of R)) [IsDominant f]
    (P : CartierDivisor (Spec (CommRingCat.of R))) :
    (cartierPullback f P).sheaf ≅ unitModule T := by
  let a := Classical.choose (localSpec_cartier_exists_principal R P)
  have ha := Classical.choose_spec (localSpec_cartier_exists_principal R P)
  have h : cartierPullback f P = principalCartierDivisor T
      (Units.map (dominantFunctionFieldMap f).hom.toMonoidHom a) := by
    rw [← ha, cartierPullback_principal]
  exact eqToIso (congrArg CartierDivisor.sheaf h) ≪≫
    (CartierDivisor.unitIsoSheafPrincipalCartierDivisor _ _).symm

theorem cartierPullback_integer_combination {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (f : T ⟶ X) [IsDominant f] {m : ℕ} (P : Fin m → CartierDivisor X) (a : Fin m → ℤ) :
    cartierPullback f (∑ i, a i • P i) = ∑ i, a i • cartierPullback f (P i) := by
  let pb : CartierDivisor X →+ CartierDivisor T :=
    { toFun := cartierPullback f
      map_zero' := cartierPullback_zero f
      map_add' := cartierPullback_add f }
  exact (map_sum pb _ _).trans (Finset.sum_congr rfl (fun i _ => map_zsmul pb (a i) (P i)))

theorem proper_local_signed_roundup_cohomology_vanish
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (f : T ⟶ Spec (CommRingCat.of R)) [IsDominant f] [IsProper f]
    (I : Ideal R) (hI : I ≠ ⊤) (E : CartierDivisor T) (hEff : E.IsEffective)
    (hJ : effectiveCartierIdealSheaf E hEff = infinitesimalBaseIdealSheaf f I)
    (B : Type u) [CommRing B] (r : ℕ)
    (e : (effectiveCartierIdealSheaf E hEff).subscheme ≅ polynomialProjectiveScheme (r + 1) B)
    (p : polynomialProjectiveScheme (r + 1) B ⟶ T) [IsClosedImmersion p]
    (hp : e.inv ≫ (effectiveCartierIdealSheaf E hEff).subschemeι = p)
    (a : (Scheme.Modules.pullback p).obj (-E).sheaf ≅ projectiveSpace.twist (Fin (r + 1)) B 1)
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    {m : ℕ} (ξ : Fin m → T) (hinj : Function.Injective ξ)
    (G : Fin m → CartierDivisor T)
    (hG : ∀ (i : Fin m) (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = if (t : T) = η then 1 else 0)
    (hη : ∀ i, ξ i ≠ η) (s : Finset (Fin m)) (hs : s.card ≤ r + 1)
    (P : Fin m → CartierDivisor (Spec (CommRingCat.of R)))
    (hPG : ∀ i, cartierPullback f (P i) = G i + if i ∈ s then E else 0)
    (b : Fin m → ℤ) (d : ℕ) (hd : 1 ≤ d) (C : CartierDivisor T)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-((cartierCoefficient
        (cartierPullback f (∑ i, b i • P i) - ((d : ℤ) * r) • E) (t : T) : ℝ) / (d : ℝ))⌉) :
    ∃ k : ℕ, k ≤ r ∧
      C = cartierPullback f (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) + k • E ∧
      Nonempty ((Scheme.Modules.pullback p).obj C.sheaf ≅
        projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ))) ∧
      ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology C.sheaf (q + 1)) := by
  let Q := ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i
  let k := blowupRoundupCorrection s b d r
  obtain ⟨hk0, hkr⟩ := blowupRoundupCorrection_mem_Icc s b d r hd hs
  have heq : C = cartierPullback f Q + k.toNat • E := by
    have hc := cartier_roundup_totalTransform_eq hnorm ξ hinj G
      (fun i => cartierPullback f (P i)) hG η E hE hη s hPG b d r C (by
        intro t
        simpa only [cartierPullback_integer_combination] using hC t)
    rw [← cartierPullback_integer_combination] at hc
    change C = cartierPullback f Q + k • E at hc
    have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← hk, natCast_zsmul] at hc
    exact hc
  have hkn : k.toNat ≤ r := by omega
  let c : (cartierPullback f Q).sheaf ≅ (Scheme.Modules.pullback f).obj Q.sheaf :=
    localSpecActualCartierPullbackFrameIso R f Q ≪≫ (localSpecCartierPullbackFrameIso R f Q).symm
  refine ⟨k.toNat, hkn, heq, ?_, ?_⟩
  · rw [heq]
    refine ⟨?_⟩
    simpa only [natCast_zsmul] using
      (cartierLocalBasePlusConormalPowerIso R f p Q (cartierPullback f Q) E c
        (projectiveSpace.twistingBundle (Fin (r + 1)) B) a (k.toNat : ℤ))
  · intro q
    rw [heq]
    exact proper_localBase_cartier_vanish_of_projective_exceptional R f I hI E hEff hJ B r
      e p hp a Q (cartierPullback f Q) c k.toNat q (Or.inr hkn)

end MixedFujita
