/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHyperplaneWeakBad
public import MixedFujita.KltWeakBadOpenImmersion
public import MixedFujita.KltConnectednessBoundary
public import MixedFujita.NonkltAdjacentMember
public import MixedFujita.SNCChartTwoMembers
public import MixedFujita.ExceptionalCutConnectedness
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.SmoothKawamataNumericalFreeness
public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.CanonicalBasePrimeThresholdUpperBound
public import MixedFujita.NormalEffectiveCartierPrime
public import MixedFujita.SNCChartPullbackPrime

/-!
The hypersurface step of the klt restriction theorem on Y × W (step 15).

Let (Y, D₀) be a pair with effective boundary on a normal variety, P = Spec B ×_K Y with étale
coordinates u_0, …, u_e of B, H = Spec(B/(u_0)) ×_K Y with B/(u_0) a domain, w a K-point of B on
u_0 = 0 and y a closed point of an affine open V of Y on which D₀ = div δ. If a family g on
P|_V has threshold at most 1/M at (w, y) in the weak model form and does not vanish on H, its
restriction to H has threshold at most 1/M at (w, y) in the weak model form
(`klt_hypersurface_step_weakBad`): on the affine piece X = Spec Γ(P|_V) with the transported pair,
a compactified principalizing model of u_0 and g carries a bad member (the weak badness at the
point) and the strict transform of H; the Kawamata–Viehweg vanishing for the roundup of
−(dM·H + M·B + d·G)/(dM) makes the non-klt members over the point connected, so a non-klt member
meets the strict transform over the point, and adjunction along the strict transform
(`klt_hyperplane_adjunction_weakBad`) gives the weak badness on H.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Fibre

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

/-- The fibre of the product over a K-point of B is a closed immersion: it is a section of the
separated second projection. -/
theorem specFibreProductFibre_isClosedImmersion (w : B →ₐ[K] K) :
    IsClosedImmersion (specFibreProductFibre (V := Y) w) := by
  have : IsAffineHom (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated (specFibreProductSnd K B Y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsClosedImmersion (specFibreProductFibre (V := Y) w ≫ specFibreProductSnd K B Y) := by
    rw [specFibreProductFibre_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (specFibreProductFibre (V := Y) w) (specFibreProductSnd K B Y)

/-- The fibre point over a closed point is closed. -/
theorem specFibreProductFibre_isClosed_point (w : B →ₐ[K] K) (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    IsClosed ({specFibreProductFibre (V := Y) w y} : Set (specFibreProduct K B Y)) := by
  have := specFibreProductFibre_isClosedImmersion (Y := Y) w
  have h := (specFibreProductFibre (V := Y) w).isClosedEmbedding.isClosedMap _ hy
  rwa [Set.image_singleton] at h

end Fibre

section Germs

/-- The function of a restricted pullback of a section does not depend on the open. -/
theorem germToFunctionField_appLE_eq {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) (V : Y.Opens)
    (U U' : X.Opens) [Nonempty U] [Nonempty U'] (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) :
    X.germToFunctionField U (f.appLE V U e s) = X.germToFunctionField U' (f.appLE V U' e' s) := by
  change X.presheaf.germ U _ _ (f.appLE V U e s) = X.presheaf.germ U' _ _ (f.appLE V U' e' s)
  rw [appLE_germ_eq_stalkMap_germ, appLE_germ_eq_stalkMap_germ]

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] structureSectionsAlgebra specFibreProductOverAlgebra

/-- The constants of B on an open of the product are pulled back along the first projection. -/
theorem specFibreProduct_algebraMap_eq_appLE (U : (specFibreProduct K B Y).Opens) (b : B) :
    algebraMap B Γ(specFibreProduct K B Y, U) b =
      (specFibreProductFst K B Y).appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  change (((specFibreProduct K B Y).baseRingToStructurePresheaf B).app (op U)) b = _
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  rfl

/-- On an affine open of the product, the spectrum of the functions maps to Spec B through the
constants. -/
theorem specFibreProduct_fromSpec_comp_fst {U : (specFibreProduct K B Y).Opens}
    (hU : IsAffineOpen U) :
    hU.fromSpec ≫ specFibreProductFst K B Y =
      Spec.map (CommRingCat.ofHom (algebraMap B Γ(specFibreProduct K B Y, U))) := by
  apply ext_of_isAffine
  have e1 : (⊤ : (Spec Γ(specFibreProduct K B Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  have h1 : (hU.fromSpec ≫ specFibreProductFst K B Y).appTop =
      (specFibreProductFst K B Y).appLE ⊤ U le_top ≫
        (Scheme.ΓSpecIso Γ(specFibreProduct K B Y, U)).inv := by
    rw [← affineOpen_fromSpec_appLE_self hU e1, Scheme.Hom.appLE_comp_appLE]
    exact (Scheme.Hom.appLE_eq_app _ (U := ⊤)).symm
  have h3 : CommRingCat.ofHom (algebraMap B Γ(specFibreProduct K B Y, U)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specFibreProductFst K B Y).appLE ⊤ U le_top := by
    ext b
    exact specFibreProduct_algebraMap_eq_appLE U b
  have h2 : (Spec.map (CommRingCat.ofHom (algebraMap B Γ(specFibreProduct K B Y, U)))).appTop =
      (specFibreProductFst K B Y).appLE ⊤ U le_top ≫
        (Scheme.ΓSpecIso Γ(specFibreProduct K B Y, U)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of B)).inv, ← Scheme.ΓSpecIso_inv_naturality,
      h3, Category.assoc]
    rfl
  rw [h1, h2]

end Germs

section Units

variable {K : Type u} [Field K]

/-- A rational function pulled back from the generic point of Y has order zero at a point over the
generic point. -/
theorem scheme_ord_pullback_eq_zero_of_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral Y] [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] (p : X)
    (hp : π p = genericPoint Y) (u : Y.functionFieldˣ) :
    X.ord ((dominantFunctionFieldMap π).hom (u : Y.functionField)) p = 0 := by
  obtain ⟨b, hb⟩ := exists_stalk_eq_of_eq_genericPoint (K := K) hp (u : Y.functionField)
  obtain ⟨b', hb'⟩ := exists_stalk_eq_of_eq_genericPoint (K := K) hp
    ((u⁻¹ : Y.functionFieldˣ) : Y.functionField)
  have hbb : b * b' = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk (π p)) Y.functionField
    change stalkFunctionFieldAlgHom (K := K) (π p) (b * b') = stalkFunctionFieldAlgHom (K := K) (π p) 1
    rw [map_mul, hb, hb', map_one, Units.mul_inv]
  let v : (Y.presheaf.stalk (π p))ˣ := ⟨b, b', hbb, (mul_comm b' b).trans hbb⟩
  have h1 := congrArg (fun φ => φ b) (dominantFunctionFieldAlgHom_comp_stalk (K := K) π p)
  simp only [AlgHom.comp_apply] at h1
  rw [hb] at h1
  have h2 := scheme_ord_stalk_unit p (Units.map (π.stalkMap p).hom.toMonoidHom v)
  rw [Units.coe_map] at h2
  change X.ord (dominantFunctionFieldAlgHom (K := K) π (u : Y.functionField)) p = 0
  rw [h1]
  exact h2

/-- A section whose restriction to an integral closed subscheme H has nonzero function is a unit
at the image of the generic point of H. -/
theorem germ_isUnit_of_restriction_ne_zero {X H : Scheme.{u}} [IsIntegral H] (ι : H ⟶ X)
    (U : X.Opens) (U' : H.Opens) [Nonempty U'] (e : U' ≤ ι ⁻¹ᵁ U) (s : Γ(X, U))
    (hs : H.germToFunctionField U' (ι.appLE U U' e s) ≠ 0) (hη : ι (genericPoint H) ∈ U) :
    IsUnit (X.presheaf.germ U (ι (genericPoint H)) hη s) := by
  by_contra hnu
  apply hs
  have h1 : ¬ IsUnit (ι.stalkMap (genericPoint H) (X.presheaf.germ U (ι (genericPoint H)) hη s)) :=
    fun hu => hnu ((isUnit_map_iff (ι.stalkMap (genericPoint H)).hom _).mp hu)
  have h2 : ι.stalkMap (genericPoint H) (X.presheaf.germ U (ι (genericPoint H)) hη s) = 0 := by
    by_contra h0
    exact h1 (isUnit_iff_ne_zero.mpr h0)
  change H.presheaf.germ U' (genericPoint H) _ (ι.appLE U U' e s) = 0
  rw [appLE_germ_eq_stalkMap_germ]
  exact h2

end Units

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- Two members of an SNC family through a point are the first two coordinates of an SNC chart,
in any dimension at least two. -/
theorem exists_snc_chart_two_members_at_of_two_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {r : ℕ}
    (ξ : Fin r → X) (hsnc : IsSNCFamily K N ξ) (t : X) (i j : Fin r) (hij : i ≠ j)
    (hi : t ∈ closure ({ξ i} : Set X)) (hj : t ∈ closure ({ξ j} : Set X)) :
    ∃ (c : EtaleChart K X N) (σ : Fin r → Option (Fin N)), t ∈ c.U ∧
      IsSNCChart c ξ σ ∧ σ i = some 0 ∧ σ j = some 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact exists_snc_chart_two_members_at ξ hsnc t i j hij hi hj

end Charts

section Divisibility

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {N : ℕ}

attribute [local instance] cartierGlobalStalkFunctionFieldTower

set_option maxHeartbeats 1600000 in
/-- **Divisibility by a member of a principalized SNC divisor**: if every prime coefficient of an
effective divisor G supported on an SNC family is at most the order of a function F of a chart c,
then near a point t' of c on y_0 = 0, the class of F modulo y_0 is divisible by y_1^{G_j} for the
member ξ_j given by y_1 = 0, up to a factor which is a unit at t'. -/
theorem exists_quotient_divisibility_of_principalized
    [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (c : EtaleChart K T (N + 1)) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (σ : Fin r → Option (Fin (N + 1)))
    (hc : IsSNCChart c ξ σ) (G : CartierDivisor T)
    (hGsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient G (z : T) = 0)
    (hGnn : ∀ z : T, 0 ≤ cartierCoefficient G z) (t' : T) (ht' : t' ∈ c.U)
    (h0 : c.coords (MvPolynomial.X 0) ∈ (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal)
    (j : Fin r) (hσj : σ j = some 1) (F : Γ(T, c.U))
    (hF : F ≠ 0 → ∀ z : CodimensionOnePoint T,
      cartierCoefficient G (z : T) ≤ T.ord (T.germToFunctionField c.U F) (z : T)) :
    ∃ q Vk : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)},
      Vk ∉ (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal.map (Ideal.Quotient.mk _) ∧
      Ideal.Quotient.mk _ F * Vk =
        Ideal.Quotient.mk _ (c.coords (MvPolynomial.X 1)) ^ (cartierCoefficient G (ξ j)).toNat * q := by
  classical
  have : Nonempty c.U := c.nonempty
  have hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)}) f ∈
      (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal.map (Ideal.Quotient.mk _) ↔
        f ∈ (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal :=
    mem_map_primeIdealOf_quotient_iff c.isAffine t' ht' _ h0
  by_cases hF0 : F = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · rw [← map_one (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})), hmem]
      exact (c.isAffine.primeIdealOf ⟨t', ht'⟩).isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).mpr
    · rw [hF0, map_zero, zero_mul, mul_zero]
  -- the local product of G at t'
  obtain ⟨lamG, hlamG, v, hv⟩ := normal_isSNCChart_boundary_local_product hnorm G c ξ hinj hξ σ hc
    hGsupp t' ht'
  obtain ⟨W, htW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hlamG
  haveI : Nonempty W := ⟨⟨t', htW⟩⟩
  have hlocW : ∀ z ∈ W, G.IsLocalEquationAt z lamG := fun z hz =>
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hW hz
  -- F / lamG is regular at t'
  have hFne : T.germToFunctionField c.U F ≠ 0 := fun h =>
    hF0 (T.germToFunctionField_injective c.U (h.trans (map_zero _).symm))
  let uF : T.functionFieldˣ := Units.mk0 _ hFne
  have hreg : ((uF * lamG⁻¹ : T.functionFieldˣ) : T.functionField) ∈
      (algebraMap (T.presheaf.stalk t') T.functionField).range := by
    apply mem_range_stalk_of_codimOne hnorm t' W htW
    intro z hzW hz1
    apply mem_range_stalk_of_ord_nonneg hnorm z hz1
    have h1 := Scheme.ord_mul (x := z) (Units.ne_zero (uF * lamG⁻¹)) (Units.ne_zero lamG)
    rw [← Units.val_mul, inv_mul_cancel_right] at h1
    have h2 := hF hF0 ⟨z, hz1⟩
    rw [cartierCoefficient_eq_ord (hlocW z hzW)] at h2
    change T.ord ((uF : T.functionField)) z = _ at h1
    change _ ≤ T.ord (uF : T.functionField) z at h2
    linarith
  obtain ⟨Q, hQ⟩ := hreg
  -- the germ of F is y_1^{G_j} times a germ
  let zc : Fin r → T.presheaf.stalk t' := fun i => (σ i).elim 1 fun a =>
    T.presheaf.germ c.U t' ht' (c.coords (MvPolynomial.X a))
  have hzc : ∀ i, (sncChartComponentEquation c σ i : T.functionField) =
      algebraMap (T.presheaf.stalk t') T.functionField (zc i) := by
    intro i
    cases hi : σ i with
    | none => simp [sncChartComponentEquation, zc, hi]
    | some a =>
      simp only [sncChartComponentEquation, zc, hi, Option.elim_some,
        etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
      rw [T.algebraMap_germ_eq_germToFunctionField ht']
  have hprod : ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient G (ξ i) :
      T.functionFieldˣ) : T.functionField) = algebraMap (T.presheaf.stalk t') T.functionField
        (∏ i, zc i ^ (cartierCoefficient G (ξ i)).toNat) := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Int.toNat_of_nonneg (hGnn (ξ i)), zpow_natCast, Units.val_pow_eq_pow_val, hzc, map_pow,
      Int.toNat_natCast]
  have hgermF : T.presheaf.germ c.U t' ht' F = zc j ^ (cartierCoefficient G (ξ j)).toNat *
      (Q * (v : T.presheaf.stalk t') *
        ∏ i ∈ Finset.univ.erase j, zc i ^ (cartierCoefficient G (ξ i)).toNat) := by
    apply IsFractionRing.injective (T.presheaf.stalk t') T.functionField
    rw [T.algebraMap_germ_eq_germToFunctionField ht']
    have h1 : T.germToFunctionField c.U F = ((uF * lamG⁻¹ : T.functionFieldˣ) : T.functionField) *
        (lamG : T.functionField) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
      rfl
    rw [h1, ← hQ, hv, hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [map_mul]
    ring
  have hzcj : zc j = T.presheaf.germ c.U t' ht' (c.coords (MvPolynomial.X 1)) := by
    simp only [zc, hσj, Option.elim_some]
  rw [hzcj] at hgermF
  -- clear the denominators in Γ(T, c.U)
  letI := TopCat.Presheaf.algebra_section_stalk T.presheaf (⟨t', ht'⟩ : c.U)
  haveI := c.isAffine.isLocalization_stalk ⟨t', ht'⟩
  obtain ⟨⟨r', s'⟩, hrs⟩ := IsLocalization.mk'_surjective
    (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal.primeCompl
    (Q * (v : T.presheaf.stalk t') *
      ∏ i ∈ Finset.univ.erase j, zc i ^ (cartierCoefficient G (ξ i)).toNat)
  have heq : algebraMap Γ(T, c.U) (T.presheaf.stalk t') (F * s') =
      algebraMap Γ(T, c.U) (T.presheaf.stalk t')
        (c.coords (MvPolynomial.X 1) ^ (cartierCoefficient G (ξ j)).toNat * r') := by
    rw [map_mul, map_mul, map_pow]
    change T.presheaf.germ c.U t' ht' F * _ = T.presheaf.germ c.U t' ht' _ ^ _ * _
    rw [hgermF, ← hrs, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨⟨c', hc'⟩, hc'eq⟩ := (IsLocalization.eq_iff_exists
    (c.isAffine.primeIdealOf ⟨t', ht'⟩).asIdeal.primeCompl (T.presheaf.stalk t')).mp heq
  refine ⟨Ideal.Quotient.mk _ (c' * r'), Ideal.Quotient.mk _ (c' * s'), ?_, ?_⟩
  · rw [hmem]
    intro hcs
    rcases (c.isAffine.primeIdealOf ⟨t', ht'⟩).isPrime.mem_or_mem hcs with h | h
    · exact hc' h
    · exact s'.2 h
  · have h2 := congrArg (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})) hc'eq
    simp only [map_mul, map_pow] at h2 ⊢
    linear_combination h2

end Divisibility

section Step

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {B : Type u} [CommRing B]
  [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower specFibreProduct_isIntegral
  specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant specFibreProductSnd_isOver
  specFibreProduct_isLocallyNoetherian specFibreProductFst_isOver hyperplaneTestInclusion_isOver

set_option maxHeartbeats 3200000 in
/-- **The hypersurface step of the klt restriction theorem**: weak badness of a family on
P = Spec B ×_K Y at (w, y), with w on u_0 = 0, gives weak badness of its restriction to
H = Spec(B/(u_0)) ×_K Y at (w, y), when the restriction is not zero. -/
theorem klt_hypersurface_step_weakBad (hn : 1 ≤ n)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (hcovY : CodimOneChartCovered n K Y)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D₀)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (δ : Y.functionFieldˣ)
    (hδ : ∀ y ∈ V, D₀.IsLocalEquationAt y δ)
    (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    {J : Type} [Finite J] (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V))
    (hg : ∃ k, (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
        (specFibreProductSnd K _ Y ⁻¹ᵁ V)
        ((specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
          (specFibreProductSnd K B Y ⁻¹ᵁ V) (specFibreProductSnd K _ Y ⁻¹ᵁ V) (fun x hx => by
            change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
              specFibreProductSnd K B Y) x ∈ V
            rw [specFibreProductMap_snd]
            exact hx) (g k)) ≠ 0)
    (M : ℕ) (hM : 1 ≤ M) (w : B →ₐ[K] K)
    (hw0 : ∀ b ∈ Ideal.span {φ (MvPolynomial.X 0)}, w b = 0) (y : Y) (hyV : y ∈ V)
    (hyc : IsClosed ({y} : Set Y))
    (hbad : ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ)
      (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀)
      (specFibreProductFibre (V := Y) w y)
      (fun k => (specFibreProduct K B Y).germToFunctionField _ (g k)) M) :
    ModelThresholdWeakBadAt
      (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ))
      (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) D₀)
      (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w hw0) y)
      (fun k => (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
        (specFibreProductSnd K _ Y ⁻¹ᵁ V)
        ((specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
          (specFibreProductSnd K B Y ⁻¹ᵁ V) (specFibreProductSnd K _ Y ⁻¹ᵁ V) (fun x hx => by
            change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
              specFibreProductSnd K B Y) x ∈ V
            rw [specFibreProductMap_snd]
            exact hx) (g k))) M := by
  classical
  -- the product and its affine piece over V
  have hnormP := specFibreProduct_stalk_isIntegrallyClosed (Y := Y) φ hφ hnormY
  have hcovP := specFibreProduct_codimOneChartCovered cY φ hφ hnormY
  have heffP := fibreProductPair_logPairBoundaryEffective cY fY d D₀ heff hcovY hnormY φ hφ
  have : LocallyOfFiniteType (specFibreProduct K B Y ↘ Spec (CommRingCat.of K)) :=
    specFibreProduct_locallyOfFiniteType
  have : IsAffineHom (specFibreProductSnd K B Y) := MorphismProperty.pullback_snd _ _ inferInstance
  have hPV : IsAffineOpen (specFibreProductSnd K B Y ⁻¹ᵁ V) := hV.preimage _
  have : Nonempty (specFibreProductSnd K B Y ⁻¹ᵁ V) := inferInstance
  have hfinA := sectionsBaseOpen_finiteType (K := K) hPV
  let jA : Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) ⟶
    specFibreProduct K B Y := hPV.fromSpec
  haveI : jA.IsOver (Spec (CommRingCat.of K)) := ⟨affineOpen_fromSpec_over_eq_specMap hPV⟩
  haveI : IsDominant jA := ⟨jA.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hjA : Function.Bijective (dominantFunctionFieldAlgHom (K := K) jA) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion jA
  have hrangeA : Set.range jA = specFibreProductSnd K B Y ⁻¹ᵁ V := hPV.range_fromSpec
  -- the pair on the affine piece
  obtain ⟨cA⟩ := exists_etaleChart_on_integral_open_immersion jA (fibreProductEtaleChart cY φ hφ)
  let cP := fibreProductEtaleChart cY φ hφ
  let fA := crepantPullbackFormUnit jA hjA cP (fibreProductPairUnit (K := K) fY) cA
  let uA : (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).functionFieldˣ :=
    Units.map (dominantFunctionFieldMap (jA ≫ specFibreProductSnd K B Y)).hom.toMonoidHom δ
  have hjAV : ∀ a, specFibreProductSnd K B Y (jA a) ∈ V := by
    intro a
    have : jA a ∈ Set.range jA := ⟨a, rfl⟩
    rw [hrangeA] at this
    exact this
  have hDA : cartierPullback jA (fibreProductPairDivisor (K := K) (B := B) D₀) =
      principalCartierDivisor _ uA := by
    apply cartierDivisor_eq_of_isLocalEquationAt
    intro a
    refine ⟨uA, ?_, CartierDivisor.isLocalEquationAt_principalCartierDivisor a uA⟩
    have h1 := cartierPullback_isLocalEquationAt (jA ≫ specFibreProductSnd K B Y) D₀ a
      (hδ _ (hjAV a))
    rw [cartierPullback_comp (specFibreProductSnd K B Y) jA] at h1
    exact h1
  -- the hyperplane function on the affine piece
  let tA : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) :=
    algebraMap B _ (φ (MvPolynomial.X 0))
  -- it is the coordinate u_0 of the product chart
  have hcoordt : cP.coords (MvPolynomial.X (Fin.natAdd n 0)) =
      algebraMap B Γ(specFibreProduct K B Y, cP.U) (φ (MvPolynomial.X 0)) := by
    change fibreProductCoords cY φ (MvPolynomial.X (Fin.natAdd n 0)) = _
    rw [fibreProductCoords_X_natAdd, specFibreProductSectionsEquiv_tmul, map_one, mul_one]
    rfl
  have : Nonempty cP.U := cP.nonempty
  have hgermt : (specFibreProduct K B Y).germToFunctionField (specFibreProductSnd K B Y ⁻¹ᵁ V) tA =
      (etaleChartCoordinateRationalUnit cP (Fin.natAdd n 0) :
        (specFibreProduct K B Y).functionField) := by
    simp only [etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
    rw [hcoordt]
    change (specFibreProduct K B Y).germToFunctionField _
        (algebraMap B Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)
          (φ (MvPolynomial.X 0))) =
      (specFibreProduct K B Y).germToFunctionField (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)
        (algebraMap B Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ cY.U)
          (φ (MvPolynomial.X 0)))
    rw [specFibreProduct_algebraMap_eq_appLE, specFibreProduct_algebraMap_eq_appLE]
    exact germToFunctionField_appLE_eq _ ⊤ _ _ le_top le_top _
  have htA : tA ≠ 0 := by
    intro h0
    have h1 := hgermt
    rw [h0, map_zero] at h1
    exact (Units.ne_zero _) h1.symm
  -- the family on the affine piece
  have hgA : ∃ k, g k ≠ 0 := by
    obtain ⟨k, hk⟩ := hg
    refine ⟨k, fun h0 => hk ?_⟩
    rw [h0, map_zero, map_zero]
  -- the compactified principalizing model
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hρd, hρo, hρp, hρ, cT, r, ξ, Gc, hGc, hinj, hξ, hsnc, hcrep,
      hHsupp, hgsupp, hGsupp, hGI, hmin, hcomp⟩ :=
    exists_klt_compactified_principalizing_model (K := K)
      Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) (n + (e + 1)) (by omega) cA fA uA
      d tA htA g hgA
  -- the point of the affine piece over (w, y)
  have hxP : specFibreProductFibre (V := Y) w y ∈ Set.range jA := by
    rw [hrangeA]
    change specFibreProductSnd K B Y (specFibreProductFibre (V := Y) w y) ∈ V
    rw [← Scheme.Hom.comp_apply, specFibreProductFibre_snd]
    exact hyV
  obtain ⟨xA, hxA⟩ := hxP
  have hxAc : IsClosed ({xA} : Set (Spec Γ(specFibreProduct K B Y,
      specFibreProductSnd K B Y ⁻¹ᵁ V))) := by
    have h1 := (specFibreProductFibre_isClosed_point w y hyc).preimage jA.continuous
    have h2 : jA ⁻¹' {specFibreProductFibre (V := Y) w y} = {xA} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [← hxA]
      exact jA.isOpenEmbedding.injective.eq_iff
    rwa [h2] at h1
  haveI : Nonempty (⊤ : (Spec Γ(specFibreProduct K B Y,
      specFibreProductSnd K B Y ⁻¹ᵁ V)).Opens) := ⟨⟨xA, trivial⟩⟩
  -- weak badness on the affine piece
  let gP : J → (specFibreProduct K B Y).functionField := fun k =>
    (specFibreProduct K B Y).germToFunctionField _ (g k)
  let gA : J → (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).functionField :=
    fun k => (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).germToFunctionField
      ⊤ ((Scheme.ΓSpecIso Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).inv (g k))
  have e1 : (⊤ : (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).Opens) ≤
      jA ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V) := by
    rw [hPV.fromSpec_preimage_self]
  have hgPA : ∀ k, (dominantFunctionFieldMap jA).hom (gP k) = gA k := by
    intro k
    change (dominantFunctionFieldMap jA).hom ((specFibreProduct K B Y).germToFunctionField _ (g k)) = _
    rw [dominantFunctionFieldMap_germ jA _ ⊤ e1, affineOpen_fromSpec_appLE_self hPV e1]
  have hbadA := modelThresholdWeakBadAt_openImmersion_pullback jA hjA cP
    (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cA xA gP gA
    hgPA M (by rw [hxA]; exact hbad)
  rw [hDA] at hbadA
  -- the bad member of the model
  have hgAne : ∀ k, g k ≠ 0 ↔ gA k ≠ 0 := by
    intro k
    constructor
    · intro h h0
      apply h
      have h1 := Scheme.germToFunctionField_injective
        (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) ⊤
        (h0.trans (map_zero _).symm)
      exact (Scheme.ΓSpecIso Γ(specFibreProduct K B Y,
        specFibreProductSnd K B Y ⁻¹ᵁ V)).commRingCatIsoToRingEquiv.symm.injective
        (h1.trans (map_zero _).symm)
    · intro h h0
      apply h
      change (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).germToFunctionField
        ⊤ ((Scheme.ΓSpecIso Γ(specFibreProduct K B Y,
          specFibreProductSnd K B Y ⁻¹ᵁ V)).inv (g k)) = 0
      rw [h0, map_zero, map_zero]
  have hunit : ∀ (k : J) (hk : g k ≠ 0) (hk' : gA k ≠ 0),
      Units.mk0 (gA k) hk' = specFunctionRationalUnit (g k) hk := fun k hk hk' => Units.ext rfl
  haveI : Nonempty {j : J // gA j ≠ 0} := by
    obtain ⟨k, hk⟩ := hgA
    exact ⟨⟨k, (hgAne k).mp hk⟩⟩
  have hAeff : ∀ k : {j : J // gA j ≠ 0}, (principalCartierDivisor _
      (Units.mk0 (gA k.1) k.2)).IsEffective := fun k => by
    rw [hunit k.1 ((hgAne k.1).mpr k.2) k.2]
    exact specFunctionRationalUnit_effective _ _
  have hIcongr : ∀ (D D' : CartierDivisor (Spec Γ(specFibreProduct K B Y,
      specFibreProductSnd K B Y ⁻¹ᵁ V))) (_ : D = D') (hD : D.IsEffective)
      (hD' : D'.IsEffective), effectiveCartierIdealSheaf D hD = effectiveCartierIdealSheaf D' hD' := by
    rintro D D' rfl hD hD'
    rfl
  have hGI' : effectiveCartierIdealSheaf Gc hGc = (⨆ k : {j : J // gA j ≠ 0},
      effectiveCartierIdealSheaf (principalCartierDivisor _ (Units.mk0 (gA k.1) k.2))
        (hAeff k)).comap ρ := by
    rw [hGI]
    congr 1
    apply Equiv.iSup_congr (Equiv.subtypeEquivRight hgAne)
    intro k
    exact hIcongr _ _ (congrArg _ (Units.ext rfl)) _ _
  obtain ⟨s₁, hs₁, hx₁⟩ := exists_bad_snc_member_of_modelThresholdWeakBadAt ρ hρ cA fA d hd
    (principalCartierDivisor _ uA) cT ξ hinj hξ hsnc hcrep gA hAeff Gc hGc hGsupp hGI' M hM xA hbadA
  -- the model of the product
  let fT : T ⟶ specFibreProduct K B Y := ρ ≫ jA
  have hfT : Function.Bijective (dominantFunctionFieldAlgHom (K := K) fT) :=
    dominantFunctionFieldAlgHom_comp_bijective jA ρ hjA hρ
  have hlogcomp : logDiscrepancyDivisor (n + (e + 1)) fT hfT cP (fibreProductPairUnit (K := K) fY)
      d (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover =
      logDiscrepancyDivisor (n + (e + 1)) ρ hρ cA fA d (principalCartierDivisor _ uA) cT
        etaleCharts_cover := by
    rw [← hDA]
    exact logDiscrepancyDivisor_comp jA ρ hjA hρ cP (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B) D₀) cA cT etaleCharts_cover
  have hcrepL : ∀ z : T, cartierCoefficient (crepantBoundaryCartier ρ hρ cA fA d
      (principalCartierDivisor _ uA) cT etaleCharts_cover) z =
      -cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT cP
        (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
        etaleCharts_cover) z := by
    intro z
    rw [hlogcomp, crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
  -- the generic point of the hyperplane and its point on the affine piece
  haveI hιH : IsClosedImmersion (specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))) :=
    specFibreProductMap_isClosedImmersion _ (Ideal.Quotient.mkₐ_surjective K _)
  have hgenY : ∀ W : Y.Opens, Nonempty W → genericPoint Y ∈ W := fun W hW =>
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  let pη : specFibreProduct K B Y := specFibreProductMap (Y := Y)
    (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))
      (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y))
  have hsndη : specFibreProductSnd K B Y pη = genericPoint Y := by
    change (specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
      specFibreProductSnd K B Y) _ = _
    rw [specFibreProductMap_snd]
    exact dominant_map_genericPoint _
  have hpηV : pη ∈ specFibreProductSnd K B Y ⁻¹ᵁ V := by
    change specFibreProductSnd K B Y pη ∈ V
    rw [hsndη]
    exact hgenY V inferInstance
  have hpηc : pη ∈ cP.U := by
    change specFibreProductSnd K B Y pη ∈ cY.U
    rw [hsndη]
    exact hgenY cY.U cY.nonempty
  obtain ⟨bA, hbA⟩ : pη ∈ Set.range jA := by
    rw [hrangeA]
    exact hpηV
  -- the composite to Spec B is the spectrum of the constants
  have hjfst : jA ≫ specFibreProductFst K B Y = Spec.map (CommRingCat.ofHom (algebraMap B
      Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V))) :=
    specFibreProduct_fromSpec_comp_fst hPV
  have hfstpt : ∀ a, specFibreProductFst K B Y (jA a) = PrimeSpectrum.comap (algebraMap B
      Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) a := by
    intro a
    have h := congrArg (fun f : Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) ⟶
      Spec (CommRingCat.of B) => f a) hjfst
    simp only [Scheme.Hom.comp_apply] at h
    exact h
  -- the zero locus of t_A lies over the hyperplane
  have hrangeH : ∀ p : specFibreProduct K B Y,
      φ (MvPolynomial.X 0) ∈ (specFibreProductFst K B Y p).asIdeal →
      p ∈ Set.range (specFibreProductMap (Y := Y)
        (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))) := by
    intro p hp
    have h : Set.range (specFibreProductMap (Y := Y)
        (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))) =
        pullback.fst (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))
          (Y ↘ Spec (CommRingCat.of K)) ⁻¹' Set.range (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom)) ∩
        pullback.snd (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))
          (Y ↘ Spec (CommRingCat.of K)) ⁻¹' Set.range (𝟙 Y) :=
      Scheme.Pullback.range_map
        (Spec (CommRingCat.of (B ⧸ Ideal.span {φ (MvPolynomial.X 0)})) ↘ Spec (CommRingCat.of K))
        (Y ↘ Spec (CommRingCat.of K)) (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))
        (Y ↘ Spec (CommRingCat.of K))
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom))
        (𝟙 Y) (𝟙 (Spec (CommRingCat.of K)))
        ((Category.comp_id _).trans (specMap_algHom_comp_over _))
        ((Category.comp_id _).trans (Category.id_comp _).symm)
    rw [h]
    refine ⟨?_, ⟨_, rfl⟩⟩
    have hr : Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom)) =
        PrimeSpectrum.zeroLocus (RingHom.ker
          (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom) :=
      _root_.range_comap_of_surjective _ _ (Ideal.Quotient.mkₐ_surjective K _)
    rw [Set.mem_preimage, hr, PrimeSpectrum.mem_zeroLocus]
    refine SetLike.coe_subset_coe.mpr ?_
    change RingHom.ker (Ideal.Quotient.mk (Ideal.span {φ (MvPolynomial.X 0)})) ≤ _
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  -- t_A vanishes at the point over the generic point of H
  have hfstη : φ (MvPolynomial.X 0) ∈ (specFibreProductFst K B Y pη).asIdeal := by
    have h := congrArg (fun f : specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⟶
      Spec (CommRingCat.of B) => f (genericPoint _))
      (specFibreProductMap_fst (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})))
    simp only [Scheme.Hom.comp_apply] at h
    change φ (MvPolynomial.X 0) ∈ (specFibreProductFst K B Y (specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) (genericPoint _))).asIdeal
    rw [h]
    have hz : (CommRingCat.ofHom (Ideal.Quotient.mkₐ K
        (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom).hom (φ (MvPolynomial.X 0)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    change (CommRingCat.ofHom (Ideal.Quotient.mkₐ K
        (Ideal.span {φ (MvPolynomial.X 0)})).toRingHom).hom (φ (MvPolynomial.X 0)) ∈
      (specFibreProductFst K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y))).asIdeal
    rw [hz]
    exact Ideal.zero_mem _
  have htAb : tA ∈ bA.asIdeal := by
    have h := hfstpt bA
    rw [hbA] at h
    rw [h] at hfstη
    exact hfstη
  -- every point of the zero locus of t_A is a specialization of b_A
  have hgener : ∀ a : Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V),
      tA ∈ a.asIdeal → bA ⤳ a := by
    intro a ha
    have h1 : φ (MvPolynomial.X 0) ∈ (specFibreProductFst K B Y (jA a)).asIdeal := by
      rw [hfstpt]
      exact ha
    obtain ⟨h', hh'⟩ := hrangeH (jA a) h1
    have h2 : pη ⤳ jA a := by
      rw [← hh']
      exact ((genericPoint_spec _).specializes (Set.mem_univ h')).map
        (specFibreProductMap (Y := Y)
          (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).continuous
    rw [← hbA] at h2
    exact jA.isOpenEmbedding.isInducing.specializes_iff.mp h2
  have : IsNoetherianRing Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) :=
    Algebra.FiniteType.isNoetherianRing K _
  have hminA : bA.asIdeal ∈ (Ideal.span {tA}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr htAb⟩, fun q hq _ => ?_⟩
    have := hq.1
    exact (PrimeSpectrum.le_iff_specializes bA ⟨q, hq.1⟩).mpr
      (hgener ⟨q, hq.1⟩ (hq.2 (Ideal.subset_span rfl)))
  have hcohA : Order.coheight bA = 1 := by
    rw [← idealHeight_eq_coheight]
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hminA
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro h0
      apply htA
      have h1 := htAb
      rw [h0] at h1
      exact (Submodule.mem_bot _).mp h1
  have hbijA : Function.Bijective (jA.stalkMap bA) := ConcreteCategory.bijective_of_isIso _
  have hcohP : Order.coheight pη = 1 := by
    rw [← hbA, ← coheight_eq_of_stalkMap_bijective jA bA hbijA]
    exact hcohA
  -- the local rings at the generic point of H are discrete valuation rings
  have hnormA : ∀ a : Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V),
      IsIntegrallyClosed ((Spec Γ(specFibreProduct K B Y,
        specFibreProductSnd K B Y ⁻¹ᵁ V)).presheaf.stalk a) :=
    integrallyClosed_stalk_of_openImmersion jA hnormP
  haveI hDVRη : IsDiscreteValuationRing ((specFibreProduct K B Y).presheaf.stalk pη) := by
    letI := hnormP pη
    exact normal_codimensionOne_stalk_DVR ⟨pη, hcohP⟩
  haveI hDVRA : IsDiscreteValuationRing ((Spec Γ(specFibreProduct K B Y,
      specFibreProductSnd K B Y ⁻¹ᵁ V)).presheaf.stalk bA) := by
    letI := hnormA bA
    exact normal_codimensionOne_stalk_DVR ⟨bA, hcohA⟩
  -- the coordinate u_0 has order one along H
  have hu0 : ¬ IsUnit ((specFibreProduct K B Y).presheaf.germ cP.U pη hpηc
      (cP.coords (MvPolynomial.X (Fin.natAdd n 0)))) := by
    intro hu
    have hV' : specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ cY.U ≤
        specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ⁻¹ᵁ
          cP.U := fun x hx => by
      change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
        specFibreProductSnd K B Y) x ∈ cY.U
      rw [specFibreProductMap_snd]
      exact hx
    have hηH : genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y) ∈
        specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ cY.U := by
      change specFibreProductSnd K _ Y _ ∈ cY.U
      rw [dominant_map_genericPoint]
      exact hgenY cY.U cY.nonempty
    have h1 := appLE_germ_eq_stalkMap_germ (specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))) cP.U _ hV' _ hηH
      (cP.coords (MvPolynomial.X (Fin.natAdd n 0)))
    have h2 : (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) (φ (MvPolynomial.X 0)) =
        0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hcoordt, specFibreProductMap_appLE_algebraMap, h2, map_zero, map_zero] at h1
    have h3 := hu.map ((specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).stalkMap
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y))).hom
    rw [hcoordt] at h3
    have h4 : IsUnit (0 : (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).presheaf.stalk
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y))) := by
      rw [h1]
      exact h3
    exact not_isUnit_zero h4
  have hordu0 : (specFibreProduct K B Y).ord (etaleChartCoordinateRationalUnit cP (Fin.natAdd n 0) :
      (specFibreProduct K B Y).functionField) pη = 1 :=
    etaleChart_coordinate_ord_one cP (Fin.natAdd n 0) ⟨pη, hcohP⟩ hpηc hu0
  -- the A-side units are pulled back from P
  have hunitA : ∀ (s : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (hs : s ≠ 0)
      (u : (specFibreProduct K B Y).functionFieldˣ)
      (hu : (u : (specFibreProduct K B Y).functionField) =
        (specFibreProduct K B Y).germToFunctionField _ s),
      specFunctionRationalUnit s hs = Units.map (dominantFunctionFieldMap jA).hom.toMonoidHom u := by
    intro s hs u hu
    apply Units.ext
    rw [specFunctionRationalUnit_val, Units.coe_map]
    change _ = (dominantFunctionFieldMap jA).hom (u : (specFibreProduct K B Y).functionField)
    rw [hu, dominantFunctionFieldMap_germ jA _ ⊤ e1, affineOpen_fromSpec_appLE_self hPV e1]
    rfl
  have hordA : ∀ (s : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (hs : s ≠ 0)
      (u : (specFibreProduct K B Y).functionFieldˣ)
      (hu : (u : (specFibreProduct K B Y).functionField) =
        (specFibreProduct K B Y).germToFunctionField _ s),
      cartierCoefficient (principalCartierDivisor _ (specFunctionRationalUnit s hs)) bA =
        (specFibreProduct K B Y).ord (u : (specFibreProduct K B Y).functionField) pη := by
    intro s hs u hu
    haveI : IsDiscreteValuationRing ((specFibreProduct K B Y).presheaf.stalk (jA bA)) := by
      rw [hbA]
      exact hDVRη
    have h := cartierCoefficient_pullback_of_stalkMap_bijective jA ⟨bA, hcohA⟩
      (by rw [hbA]; exact hcohP) hbijA (principalCartierDivisor _ u)
    rw [cartierPullback_principal, ← hunitA s hs u hu] at h
    refine h.trans ?_
    rw [cartierCoefficient_principal]
    change (specFibreProduct K B Y).ord _ (jA bA) = _
    rw [hbA]
  -- the strict transform member
  have hρ' : Function.Bijective (dominantFunctionFieldMap ρ).hom := hρ
  obtain ⟨t₀, ht₀, hbij₀⟩ := proper_birational_exists_normal_prime_lift hnormA ρ hρ' ⟨bA, hcohA⟩
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + (e + 1)) _
  haveI hDVRT : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have hcohρ₀ : Order.coheight (ρ (t₀ : T)) = 1 := by rw [ht₀]; exact hcohA
  have hh₀A : cartierCoefficient (cartierPullback ρ (principalCartierDivisor _
      (specFunctionRationalUnit tA htA))) (t₀ : T) = 1 := by
    haveI : IsDiscreteValuationRing ((Spec Γ(specFibreProduct K B Y,
        specFibreProductSnd K B Y ⁻¹ᵁ V)).presheaf.stalk (ρ (t₀ : T))) := by
      rw [ht₀]
      exact hDVRA
    rw [cartierCoefficient_pullback_of_stalkMap_bijective ρ t₀ hcohρ₀ hbij₀, ht₀,
      hordA tA htA (etaleChartCoordinateRationalUnit cP (Fin.natAdd n 0)) hgermt.symm]
    exact hordu0
  have hmemξ : (t₀ : T) ∈ Set.range ξ := by
    by_contra hnot
    have h := hHsupp t₀ hnot
    rw [hh₀A] at h
    exact one_ne_zero h
  obtain ⟨s₀, hs₀⟩ := hmemξ
  have hfTs₀ : fT (ξ s₀) = pη := by
    change jA (ρ (ξ s₀)) = pη
    rw [hs₀, ht₀, hbA]
  have hbijT : Function.Bijective (fT.stalkMap (ξ s₀)) := by
    have hfun : ∀ a, fT.stalkMap (ξ s₀) a =
        ρ.stalkMap (ξ s₀) (jA.stalkMap (ρ (ξ s₀)) a) := by
      intro a
      change (ρ ≫ jA).stalkMap (ξ s₀) a = _
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    have hρs : Function.Bijective (ρ.stalkMap (ξ s₀)) := by
      rw [hs₀]
      exact hbij₀
    have hjs : Function.Bijective (jA.stalkMap (ρ (ξ s₀))) := ConcreteCategory.bijective_of_isIso _
    have h1 : ⇑(fT.stalkMap (ξ s₀)) = ⇑(ρ.stalkMap (ξ s₀)) ∘ ⇑(jA.stalkMap (ρ (ξ s₀))) :=
      funext hfun
    rw [h1]
    exact hρs.comp hjs
  -- the discrepancy of the product pair vanishes along the strict transform
  have hcohfT : Order.coheight (fT (ξ s₀)) = 1 := by rw [hfTs₀]; exact hcohP
  haveI : IsDiscreteValuationRing ((specFibreProduct K B Y).presheaf.stalk (fT (ξ s₀))) := by
    rw [hfTs₀]
    exact hDVRη
  have hfTc : fT (ξ s₀) ∈ cP.U := by rw [hfTs₀]; exact hpηc
  have hsndfT : specFibreProductSnd K B Y (fT (ξ s₀)) = genericPoint Y := by
    rw [hfTs₀]
    exact hsndη
  have hcrepP := crepantBoundaryCartier_coefficient_of_stalkMap_bijective fT hfT cP
    (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
    ⟨ξ s₀, hξ s₀⟩ hcohfT hbijT cP hfTc
  have hDP0 : cartierCoefficient (fibreProductPairDivisor (K := K) (B := B) D₀) (fT (ξ s₀)) = 0 := by
    have hloc := cartierPullback_isLocalEquationAt (specFibreProductSnd K B Y) D₀ (fT (ξ s₀))
      (hδ _ (by rw [hsndfT]; exact hgenY V inferInstance))
    change cartierCoefficient (cartierPullback (specFibreProductSnd K B Y) D₀) (fT (ξ s₀)) = 0
    rw [cartierCoefficient_eq_ord hloc]
    exact scheme_ord_pullback_eq_zero_of_genericPoint (K := K) (specFibreProductSnd K B Y) _ hsndfT δ
  have hfP0 : (specFibreProduct K B Y).ord ((fibreProductPairUnit (K := K) fY *
      etaleChartCanonicalEquation cP cP : (specFibreProduct K B Y).functionFieldˣ) :
        (specFibreProduct K B Y).functionField) (fT (ξ s₀)) = 0 := by
    have hcan : (etaleChartCanonicalEquation cP cP : (specFibreProduct K B Y).functionField) = 1 := by
      rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
    rw [Units.val_mul, hcan, mul_one]
    exact scheme_ord_pullback_eq_zero_of_genericPoint (K := K) (specFibreProductSnd K B Y) _ hsndfT fY
  have hL₀ : cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT cP
      (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
      etaleCharts_cover) (ξ s₀) = 0 := by
    have h := congrArg (fun D => cartierCoefficient D (ξ s₀))
      (crepantBoundaryCartier_eq_neg_discrepancy fT hfT cP (fibreProductPairUnit (K := K) fY) d
        (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover)
    simp only [cartierCoefficient_neg] at h
    change cartierCoefficient _ (ξ s₀) = _ at hcrepP
    rw [hcrepP, hDP0, hfP0] at h
    linarith
  -- the principalized divisor vanishes along the strict transform
  obtain ⟨k₀, hk₀⟩ := hg
  have hgk₀ : g k₀ ≠ 0 := fun h0 => hk₀ (by rw [h0, map_zero, map_zero])
  have hunit₀ := germ_isUnit_of_restriction_ne_zero (specFibreProductMap (Y := Y)
    (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))) _ _ _ (g k₀) hk₀ hpηV
  have hordg : (specFibreProduct K B Y).ord
      ((specFibreProduct K B Y).germToFunctionField _ (g k₀)) pη = 0 := by
    have h := scheme_ord_stalk_unit pη hunit₀.unit
    rwa [IsUnit.unit_spec, Scheme.algebraMap_germ_eq_germToFunctionField] at h
  have hgk₀P : (specFibreProduct K B Y).germToFunctionField (specFibreProductSnd K B Y ⁻¹ᵁ V)
      (g k₀) ≠ 0 := by
    have h := (hunit₀.map (algebraMap ((specFibreProduct K B Y).presheaf.stalk pη)
      (specFibreProduct K B Y).functionField)).ne_zero
    rwa [Scheme.algebraMap_germ_eq_germToFunctionField] at h
  have hG₀ : cartierCoefficient Gc (ξ s₀) = 0 := by
    apply le_antisymm
    · have h1 := (hmin (ξ s₀)).1 ⟨k₀, hgk₀⟩
      haveI : IsDiscreteValuationRing ((Spec Γ(specFibreProduct K B Y,
          specFibreProductSnd K B Y ⁻¹ᵁ V)).presheaf.stalk (ρ (t₀ : T))) := by
        rw [ht₀]
        exact hDVRA
      rw [hs₀, cartierCoefficient_pullback_of_stalkMap_bijective ρ t₀ hcohρ₀ hbij₀, ht₀,
        hordA (g k₀) hgk₀ (Units.mk0 _ hgk₀P) rfl, Units.val_mk0, hordg] at h1
      rw [hs₀]
      exact h1
    · exact cartierCoefficient_nonneg_of_isEffective Gc hGc _
  -- the boundary of the connectedness argument and its roundup
  let H_T : CartierDivisor T :=
    cartierPullback ρ (principalCartierDivisor _ (specFunctionRationalUnit tA htA))
  have hHeff : H_T.IsEffective :=
    cartierPullback_effective_of_effective ρ _ (specFunctionRationalUnit_effective tA htA)
  have hsupp𝔅 := kltConnectednessBoundary_supported ρ hρ cA fA d (principalCartierDivisor _ uA) cT
    H_T Gc M ξ hHsupp hcrep hGsupp
  have hcovA : CodimOneChartCovered (n + (e + 1)) K
      (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) :=
    codimOneChartCovered_open_immersion jA hcovP
  have heffA : LogPairBoundaryEffective cA fA d (principalCartierDivisor _ uA) := by
    have h := logPairBoundaryEffective_open_crepant_pullback jA hjA hnormP hcovP cP
      (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) heffP cA
    rwa [hDA] at h
  have : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨E, S, hE, hS, hround, hSc, hdisj, -, hiso⟩ :=
    exists_kltConnectedness_roundup_exceptional_pushforward ρ hρ cA fA d
      (principalCartierDivisor _ uA) cT hnormA hcovA heffA hd H_T Gc hHeff hGc M hM ξ hinj hξ hsnc
      hsupp𝔅
  haveI := hiso
  let vT : T.functionFieldˣ :=
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (specFunctionRationalUnit tA htA)
  have hHv : H_T = principalCartierDivisor T vT := cartierPullback_principal ρ _
  have hvan : Subsingleton (Scheme.Modules.Cohomology (E - S).sheaf 1) := by
    refine klt_roundup_H1_vanishing_of_kltCompactification K
      (kawamataViehwegVanishingSNCProjective_of_charZero K (n + (e + 1))) (by omega) d M hd hM _ Gc
      hcomp vT (E - S) fun t => ?_
    rw [hround t]
    congr 1
    rw [kltConnectednessBoundary_coefficient, hHv, cartierCoefficient_principal]
    push_cast
    ring
  -- connectedness of the non-klt members over the point
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdM : 1 ≤ d * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hconn := threshold_member_union_fibre_preconnected_of_H1 ρ hnormT
    (kltConnectednessBoundary ρ hρ cA fA d (principalCartierDivisor _ uA) cT H_T Gc M) E S hE hS
    (d * M) hdM ξ hξ hsupp𝔅 hSc (fun t ht => (hdisj t).resolve_right (ne_of_gt ht)) hvan xA
  let hcoef : Fin r → ℤ := fun s => cartierCoefficient H_T (ξ s)
  let acoef : Fin r → ℤ := fun s => (M : ℤ) * cartierCoefficient (crepantBoundaryCartier ρ hρ cA fA
    d (principalCartierDivisor _ uA) cT etaleCharts_cover) (ξ s) +
      (d : ℤ) * cartierCoefficient Gc (ξ s)
  have hsets : {s : Fin r | ((d * M : ℕ) : ℤ) ≤ ((d * M : ℕ) : ℤ) * (hcoef s - (fun _ => (0 : ℤ)) s) +
      acoef s} = {i | ((d * M : ℕ) : ℤ) ≤ cartierCoefficient (kltConnectednessBoundary ρ hρ cA fA d
        (principalCartierDivisor _ uA) cT H_T Gc M) (ξ i)} := by
    ext s
    simp only [Set.mem_ofPred_eq, kltConnectednessBoundary_coefficient, hcoef, acoef]
    push_cast
    constructor <;> intro h <;> linarith
  have hconn' : _root_.IsPreconnected (⋃ s ∈ {s : Fin r | ((d * M : ℕ) : ℤ) ≤
      ((d * M : ℕ) : ℤ) * (hcoef s - (fun _ => (0 : ℤ)) s) + acoef s},
        closure ({ξ s} : Set T) ∩ ρ ⁻¹' {xA}) := by
    rw [hsets]
    exact hconn
  -- the point lies on the strict transform
  have htAx : tA ∈ xA.asIdeal := by
    have h1 := hfstpt xA
    rw [hxA] at h1
    have h2 : φ (MvPolynomial.X 0) ∈
        (specFibreProductFst K B Y (specFibreProductFibre (V := Y) w y)).asIdeal := by
      have h3 := congrArg (fun f : Y ⟶ Spec (CommRingCat.of B) => f y)
        (specFibreProductFibre_fst (Y := Y) w)
      simp only [Scheme.Hom.comp_apply] at h3
      rw [h3]
      have hz : (CommRingCat.ofHom w.toRingHom).hom (φ (MvPolynomial.X 0)) = 0 :=
        hw0 _ (Ideal.subset_span rfl)
      change (CommRingCat.ofHom w.toRingHom).hom (φ (MvPolynomial.X 0)) ∈
        ((Y ↘ Spec (CommRingCat.of K)) y).asIdeal
      rw [hz]
      exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  have hx₀ : xA ∈ ρ '' closure ({ξ s₀} : Set T) := by
    have hsp : ρ (ξ s₀) ⤳ xA := by
      rw [hs₀, ht₀]
      exact hgener xA htAx
    have hsub : ({ρ (ξ s₀)} : Set (Spec Γ(specFibreProduct K B Y,
        specFibreProductSnd K B Y ⁻¹ᵁ V))) ⊆ ρ '' closure ({ξ s₀} : Set T) :=
      Set.singleton_subset_iff.mpr ⟨ξ s₀, subset_closure (Set.mem_singleton _), rfl⟩
    exact closure_minimal hsub ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure)
      (specializes_iff_mem_closure.mp hsp)
  -- a non-klt member meets the strict transform over the point
  have hh₀' : hcoef s₀ = 1 := by
    change cartierCoefficient H_T (ξ s₀) = 1
    rw [hs₀]
    exact hh₀A
  have ha₀' : acoef s₀ = 0 := by
    change (M : ℤ) * cartierCoefficient _ (ξ s₀) + (d : ℤ) * cartierCoefficient Gc (ξ s₀) = 0
    rw [hcrepL, hL₀, hG₀]
    ring
  have hbad₁ : ((d * M : ℕ) : ℤ) * (1 + (fun _ => (0 : ℤ)) s₁) ≤ acoef s₁ := by
    change ((d * M : ℕ) : ℤ) * (1 + 0) ≤ (M : ℤ) * cartierCoefficient _ (ξ s₁) +
      (d : ℤ) * cartierCoefficient Gc (ξ s₁)
    push_cast
    linarith
  obtain ⟨j, hj, hineqj, t', ht'j, ht'0, ht'x⟩ := exists_adjacent_nonklt_member ρ ρ.continuous ξ xA
    hxAc ((d * M : ℕ) : ℤ) (by positivity) hcoef (fun _ => 0) acoef hconn' s₀ s₁ hh₀' rfl ha₀'
    (cartierCoefficient_nonneg_of_isEffective H_T hHeff _) le_rfl hbad₁ hx₀ hx₁
  obtain ⟨c, σc, ht'c, hc, hσ₀, hσj⟩ := exists_snc_chart_two_members_at_of_two_le (by omega) ξ hsnc t' s₀ j
    (Ne.symm hj) ht'0 ht'j
  have hξ₀c : ξ s₀ ∈ c.U := (specializes_iff_mem_closure.mpr ht'0).mem_open c.U.isOpen ht'c
  -- the strict transform factor of the hyperplane function in the chart
  have hy0 : ρ.appLE ⊤ c.U le_top ((Scheme.ΓSpecIso _).inv tA) ∈
      Ideal.span {c.coords (MvPolynomial.X 0)} :=
    (appLE_mem_span_coordinate_iff ρ c ξ σc hc s₀ 0 hσ₀ hξ₀c tA).mpr (by rw [hs₀, ht₀]; exact htAb)
  obtain ⟨w₀, hw₀A⟩ := Ideal.mem_span_singleton.mp hy0
  have hmodel : modelChartAlgHom (K := K) (fT ≫ specFibreProductFst K B Y) c.U
      (φ (MvPolynomial.X 0)) = ρ.appLE ⊤ c.U le_top ((Scheme.ΓSpecIso _).inv tA) := by
    rw [modelChartAlgHom_apply]
    have h1 : fT ≫ specFibreProductFst K B Y = ρ ≫ Spec.map (CommRingCat.ofHom (algebraMap B
        Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V))) := by
      change (ρ ≫ jA) ≫ _ = _
      rw [Category.assoc, hjfst]
    have h2 : (Spec.map (CommRingCat.ofHom (algebraMap B
        Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ (MvPolynomial.X 0))) =
        (Scheme.ΓSpecIso Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).inv tA := by
      have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (algebraMap B Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V))))
        (φ (MvPolynomial.X 0))
      simp only [CategoryTheory.comp_apply] at h
      exact h.symm
    rw [h1, Scheme.Hom.comp_appLE, CategoryTheory.comp_apply]
    change ρ.appLE _ c.U _ ((Spec.map (CommRingCat.ofHom (algebraMap B
      Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ (MvPolynomial.X 0)))) = _
    rw [h2]
  have hw₀ : modelChartAlgHom (K := K) (fT ≫ specFibreProductFst K B Y) c.U
      (φ (MvPolynomial.X 0)) = c.coords (MvPolynomial.X 0) * w₀ := hmodel.trans hw₀A
  -- the strict transform equation and the divisors of the model
  have htT : (vT : T.functionField) =
      T.germToFunctionField c.U (c.coords (MvPolynomial.X 0) * w₀) := by
    rw [← hw₀A]
    change (dominantFunctionFieldMap ρ).hom (specFunctionRationalUnit tA htA :
      (Spec Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)).functionField) = _
    rw [specFunctionRationalUnit_val, dominantFunctionFieldMap_germ ρ ⊤ c.U le_top]
  have hHsupp' : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (principalCartierDivisor T vT) (z : T) = 0 := by
    intro z hz
    rw [← hHv]
    exact hHsupp z hz
  have hh₀ : cartierCoefficient (principalCartierDivisor T vT) (ξ s₀) = 1 := by
    rw [← hHv, hs₀]
    exact hh₀A
  have hLsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT cP
        (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
        etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    have h := hcrep z hz
    rw [hcrepL] at h
    linarith
  have hcV : c.U ≤ fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V) := fun x _ => hjAV (ρ x)
  have hx : fT t' = specFibreProductFibre (V := Y) w y := by
    change jA (ρ t') = _
    rw [ht'x, hxA]
  have hgen : fT (ξ s₀) ⤳ specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y)) :=
    specializes_of_eq hfTs₀
  -- the inequality at the meeting member
  have hGj : 0 ≤ cartierCoefficient Gc (ξ j) := cartierCoefficient_nonneg_of_isEffective Gc hGc _
  have hineq : (M : ℤ) * ((d : ℤ) + cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
      cP (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
      etaleCharts_cover) (ξ j) - (d : ℤ) * cartierCoefficient (principalCartierDivisor T vT) (ξ j)) ≤
      (d : ℤ) * ((cartierCoefficient Gc (ξ j)).toNat : ℕ) := by
    rw [Int.toNat_of_nonneg hGj, ← hHv]
    have h1 := hineqj
    change ((d * M : ℕ) : ℤ) * (1 + 0 - cartierCoefficient H_T (ξ j)) ≤
      (M : ℤ) * cartierCoefficient (crepantBoundaryCartier ρ hρ cA fA d
        (principalCartierDivisor _ uA) cT etaleCharts_cover) (ξ j) +
        (d : ℤ) * cartierCoefficient Gc (ξ j) at h1
    rw [hcrepL] at h1
    push_cast at h1
    linarith
  -- the divisibility of the family at the meeting point
  have hz0Q : c.coords (MvPolynomial.X 0) ∈ (c.isAffine.primeIdealOf ⟨t', ht'c⟩).asIdeal :=
    sncChart_coordinate_mem_point_prime c ξ σc hc s₀ 0 hσ₀ t' ht'c ht'0
  have hga : ∀ k, ∃ q Vk : hyperplaneTestRing c,
      Vk ∉ (c.isAffine.primeIdealOf ⟨t', ht'c⟩).asIdeal.map (Ideal.Quotient.mk _) ∧
      Ideal.Quotient.mk _ (fT.appLE _ c.U hcV (g k)) * Vk =
        Ideal.Quotient.mk _ (c.coords (MvPolynomial.X 1)) ^ (cartierCoefficient Gc (ξ j)).toNat *
          q := by
    intro k
    refine exists_quotient_divisibility_of_principalized hnormT c ξ hinj hξ σc hc Gc hGsupp
      (fun z => cartierCoefficient_nonneg_of_isEffective Gc hGc z) t' ht'c hz0Q j hσj _
      (fun hF z => ?_)
    have hgk : g k ≠ 0 := fun h0 => hF (by rw [h0, map_zero])
    have h1 := (hmin (z : T)).1 ⟨k, hgk⟩
    rw [cartierPullback_principal, cartierCoefficient_principal] at h1
    have e1 : (dominantFunctionFieldMap fT).hom (gP k) =
        T.germToFunctionField c.U (fT.appLE _ c.U hcV (g k)) :=
      dominantFunctionFieldMap_germ fT _ c.U hcV (g k)
    have e2 : (dominantFunctionFieldMap fT).hom (gP k) =
        (dominantFunctionFieldMap ρ).hom ((dominantFunctionFieldMap jA).hom (gP k)) := by
      change (dominantFunctionFieldMap (ρ ≫ jA)).hom _ = _
      rw [dominantFunctionFieldMap_comp]
      rfl
    rw [hgPA] at e2
    rw [← e1, e2]
    convert h1 using 3
    rw [Units.coe_map, specFunctionRationalUnit_val]
    rfl
  -- adjunction along the strict transform
  exact klt_hyperplane_adjunction_weakBad hn cY fY d hd D₀ V δ hδ φ hφ fT hfT cT ξ hinj hξ hLsupp
    c σc hc s₀ j hσ₀ hσj hξ₀c w₀ hw₀ vT htT hHsupp' hL₀ hh₀ hbijT hgen t' ht'c ht'0 ht'j w hw0 y
    hx hcV g _ hga M hineq

end Step

end MixedFujita
