/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltFibreProductLocalization
public import MixedFujita.KltFibreRestrictionBase
public import TauCeti.RingTheory.Smooth.Regular
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
The klt restriction theorem on Y × W (step 15): restriction to the fibres of products.

For a klt pair (Y, D₀) with effective boundary on a normal variety whose codimension-one points
lie in étale charts, a domain B of finite type with formally étale coordinates u_1, …, u_e and a
family g on the inverse image of an affine open V of Y in P = Spec B ×_K Y, weak badness of g at
a point (w, y) of P with y closed gives badness of the restriction of g to the fibre over w at y
(`kltProductFibreRestrictionStatement_holds`). The proof is an induction on e
(`kltFibreRestriction_of_localEquation`, after shrinking V so that D₀ = div δ on V):

* e = 0: B = K and P = Y (`modelThresholdBadAt_fibre_of_fin_zero`);
* the coordinates are translated to vanish at w (`mvPolynomialTranslate`), and B is localized
  away from an f with w(f) ≠ 0 so that B_f/(u_0) is a domain
  (`exists_away_hyperplane_isPrime`: B/(u_0) is smooth, hence regular, so its local ring at w is
  a domain, and the kernel of B → (B/(u_0))_w generates (u_0) on some basic open,
  `exists_away_map_isPrime`); weak badness moves to the open sub-product with the new coordinates
  (`modelThresholdWeakBadAt_fibreProduct_shift`);
* if the family vanishes on the hyperplane H = Spec(B_f/(u_0)) ×_K Y, its restriction to the fibre
  vanishes and every closed point of a klt variety is bad for the zero family
  (`modelThresholdBadAt_zero_of_klt`); otherwise the hypersurface step
  (`klt_hypersurface_step_weakBad`) gives weak badness on H, whose coordinates u_1, …, u_e are
  formally étale, and the induction hypothesis applies to H.

Hence Kawamata's numerical freeness holds without further hypotheses
(`kawamataNumericalFreeness_proved`), and F2 follows from the base point free theorem for klt pairs
and Ambro's canonical bundle formula (`linearEffectiveFreeness_of_basePointFree_of_ambro`).
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

section Primes

variable {B : Type*} [CommRing B]

/-- **A principal ideal becomes prime on a basic open**: if a prime 𝔭 between I and a prime 𝔪 is
carried into I by elements outside 𝔪, then I generates a prime ideal of B_f for some f ∉ 𝔪. -/
theorem exists_away_map_isPrime [IsNoetherianRing B] (I 𝔪 𝔭 : Ideal B) [𝔪.IsPrime]
    [h𝔭p : 𝔭.IsPrime] (hI𝔭 : I ≤ 𝔭) (h𝔭𝔪 : 𝔭 ≤ 𝔪)
    (h𝔭 : ∀ x ∈ 𝔭, ∃ s, s ∉ 𝔪 ∧ s * x ∈ I) :
    ∃ f : B, f ∉ 𝔪 ∧ (I.map (algebraMap B (Localization.Away f))).IsPrime := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian 𝔭 : 𝔭.FG)
  have hS' : Ideal.span (S : Set B) = 𝔭 := hS
  have hS𝔭 : ∀ x ∈ S, x ∈ 𝔭 := fun x hx => hS' ▸ Ideal.subset_span hx
  choose! s hs𝔪 hsI using fun x (hx : x ∈ S) => h𝔭 x (hS𝔭 x hx)
  have hf : (∏ x ∈ S, s x) ∉ 𝔪 := Ideal.mem_primeCompl_iff.mp
    (prod_mem fun x hx => Ideal.mem_primeCompl_iff.mpr (hs𝔪 x hx))
  refine ⟨∏ x ∈ S, s x, hf, ?_⟩
  have hfu : IsUnit (algebraMap B (Localization.Away (∏ x ∈ S, s x)) (∏ x ∈ S, s x)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have key : I.map (algebraMap B (Localization.Away (∏ x ∈ S, s x))) =
      𝔭.map (algebraMap B (Localization.Away (∏ x ∈ S, s x))) := by
    refine le_antisymm (Ideal.map_mono hI𝔭) ?_
    rw [← hS', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hfx : (∏ y ∈ S, s y) * x ∈ I := by
      rw [← Finset.mul_prod_erase S s hx, mul_comm (s x), mul_assoc]
      exact I.mul_mem_left _ (hsI x hx)
    have h2 : algebraMap B (Localization.Away (∏ x ∈ S, s x)) (∏ y ∈ S, s y) *
        algebraMap B (Localization.Away (∏ x ∈ S, s x)) x ∈
          I.map (algebraMap B (Localization.Away (∏ x ∈ S, s x))) := by
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ hfx
    exact (Ideal.unit_mul_mem_iff_mem _ hfu).mp h2
  rw [key]
  refine IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (∏ x ∈ S, s x)) _ 𝔭 h𝔭p ?_
  rw [Set.disjoint_left]
  intro z hz hk
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
  exact hf (h𝔭𝔪 (h𝔭p.mem_of_pow_mem k hk))

/-- **The component through a point of a regular quotient**: for a prime 𝔪 containing I with B/I
regular, the kernel of B → (B/I)_𝔪 is a prime between I and 𝔪 carried into I by elements
outside 𝔪 (a regular local ring is a domain). -/
theorem exists_prime_of_isRegularRing_quotient (I 𝔪 : Ideal B) [h𝔪 : 𝔪.IsPrime] (hI : I ≤ 𝔪)
    [IsRegularRing (B ⧸ I)] :
    ∃ 𝔭 : Ideal B, 𝔭.IsPrime ∧ I ≤ 𝔭 ∧ 𝔭 ≤ 𝔪 ∧ ∀ x ∈ 𝔭, ∃ s, s ∉ 𝔪 ∧ s * x ∈ I := by
  classical
  haveI h𝔪' : (𝔪.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)
  haveI : IsRegularLocalRing (Localization.AtPrime (𝔪.map (Ideal.Quotient.mk I))) :=
    IsRegularRing.isRegularLocalRing_localization _
  haveI : IsDomain (Localization.AtPrime (𝔪.map (Ideal.Quotient.mk I))) :=
    TauCeti.IsRegularLocalRing.isDomain
  let ψ : B →+* Localization.AtPrime (𝔪.map (Ideal.Quotient.mk I)) :=
    (algebraMap (B ⧸ I) _).comp (Ideal.Quotient.mk I)
  have hker : ∀ x, ψ x = 0 → ∃ s, s ∉ 𝔪 ∧ s * x ∈ I := by
    intro x hx
    obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff
      (𝔪.map (Ideal.Quotient.mk I)).primeCompl
      (Localization.AtPrime (𝔪.map (Ideal.Quotient.mk I))) (Ideal.Quotient.mk I x)).mp hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
    refine ⟨s, fun hs => (Ideal.mem_primeCompl_iff.mp hm) (Ideal.mem_map_of_mem _ hs), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hmx
  refine ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ, fun x hx => ?_, fun x hx => ?_,
    fun x hx => hker x (RingHom.mem_ker.mp hx)⟩
  · rw [RingHom.mem_ker]
    change algebraMap (B ⧸ I) _ (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · obtain ⟨s, hs, hsx⟩ := hker x (RingHom.mem_ker.mp hx)
    exact (h𝔪.mem_or_mem (hI hsx)).resolve_left hs

end Primes

section Coordinates

variable {K : Type u} [Field K]

/-- The translation X_i ↦ X_i − c_i of the polynomial ring. -/
noncomputable def mvPolynomialTranslate {σ : Type*} (c : σ → K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (c i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (c i))
    (MvPolynomial.algHom_ext fun i => by simp)
    (MvPolynomial.algHom_ext fun i => by simp)

theorem mvPolynomialTranslate_X {σ : Type*} (c : σ → K) (i : σ) :
    mvPolynomialTranslate c (MvPolynomial.X i) = MvPolynomial.X i - MvPolynomial.C (c i) := by
  simp [mvPolynomialTranslate]

/-- Translated étale coordinates are étale. -/
theorem translate_formallyEtale {B : Type*} [CommRing B] [Algebra K B] {m : ℕ}
    (φ : MvPolynomial (Fin m) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) (c : Fin m → K) :
    (φ.comp (mvPolynomialTranslate c).toAlgHom).toRingHom.FormallyEtale :=
  RingHom.FormallyEtale.comp (formallyEtale_of_ringEquiv (mvPolynomialTranslate c).toRingEquiv) hφ

theorem translate_X {B : Type*} [CommRing B] [Algebra K B] {m : ℕ}
    (φ : MvPolynomial (Fin m) K →ₐ[K] B) (c : Fin m → K) (i : Fin m) :
    φ.comp (mvPolynomialTranslate c).toAlgHom (MvPolynomial.X i) =
      φ (MvPolynomial.X i) - algebraMap K B (c i) := by
  change φ (mvPolynomialTranslate c (MvPolynomial.X i)) = _
  rw [mvPolynomialTranslate_X, map_sub]
  congr 1
  exact φ.commutes (c i)

/-- **The hyperplane through a K-point becomes integral on a basic open**: for formally étale
coordinates u_0, …, u_e of B with w(u_0) = 0 there is f with w(f) ≠ 0 such that u_0 generates a
prime ideal of B_f. -/
theorem exists_away_hyperplane_isPrime {B : Type u} [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] {e : ℕ} (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B)
    (hφ : φ.toRingHom.FormallyEtale) (w : B →ₐ[K] K) (hw : w (φ (MvPolynomial.X 0)) = 0) :
    ∃ f : B, w f ≠ 0 ∧
      (Ideal.span {algebraMap B (Localization.Away f) (φ (MvPolynomial.X 0))}).IsPrime := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI h𝔪 : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  have hI : Ideal.span {φ (MvPolynomial.X 0)} ≤ RingHom.ker w := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr hw
  haveI : Algebra.FinitePresentation K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have het := etale_of_formallyEtale_of_finitePresentation _ (hyperplaneCoords_formallyEtale φ hφ)
  haveI : Algebra.Smooth K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) := by
    let _ : Algebra (MvPolynomial (Fin e) K) (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) :=
      (hyperplaneCoords φ).toRingHom.toAlgebra
    have : IsScalarTower K (MvPolynomial (Fin e) K) (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) :=
      IsScalarTower.of_algebraMap_eq fun k => ((hyperplaneCoords φ).commutes k).symm
    have : Algebra.Etale (MvPolynomial (Fin e) K) (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) := het
    have : Algebra.Smooth K (MvPolynomial (Fin e) K) := {}
    exact Algebra.Smooth.comp K (MvPolynomial (Fin e) K) _
  haveI : IsRegularRing (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) :=
    TauCeti.IsRegularRing.of_smooth (R := K)
  obtain ⟨𝔭, h𝔭, hI𝔭, h𝔭𝔪, h𝔭I⟩ := exists_prime_of_isRegularRing_quotient _ _ hI
  haveI := h𝔭
  obtain ⟨f, hf, hprime⟩ := exists_away_map_isPrime _ _ 𝔭 hI𝔭 h𝔭𝔪 h𝔭I
  refine ⟨f, fun h => hf (RingHom.mem_ker.mpr h), ?_⟩
  have h := Ideal.map_span (algebraMap B (Localization.Away f)) {φ (MvPolynomial.X 0)}
  rw [Set.image_singleton] at h
  rw [← h]
  exact hprime

/-- Localizations of domains of finite type away from nonzero elements are domains of finite
type. -/
theorem away_isDomain_finiteType {B : Type u} [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (f : B) (hf : f ≠ 0) :
    IsDomain (Localization.Away f) ∧ Algebra.FiniteType K (Localization.Away f) := by
  refine ⟨IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf), ?_⟩
  have : Algebra.FinitePresentation B (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  exact Algebra.FiniteType.trans (S := B) inferInstance inferInstance

end Coordinates

section Induction

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower specFibreProduct_isIntegral
  specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant specFibreProductSnd_isOver

set_option maxHeartbeats 3200000 in
/-- **Restriction to the fibres of products, on an open with a local equation**: the induction on
the number of coordinates of B, for an affine open V of Y on which D₀ = div δ. -/
theorem kltFibreRestriction_of_localEquation {n : ℕ} (hn : 1 ≤ n)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (hcovY : CodimOneChartCovered n K Y)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D₀) (hklt : LogPairIsKlt cY fY d D₀)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (δ : Y.functionFieldˣ)
    (hδ : ∀ y ∈ V, D₀.IsLocalEquationAt y δ) {J : Type} [Finite J] (M : ℕ) (hM : 1 ≤ M)
    (y : Y) (hyV : y ∈ V) (hyc : IsClosed ({y} : Set Y)) (e : ℕ) :
    ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
      (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (w : B →ₐ[K] K),
      ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit fY) d
        (fibreProductPairDivisor D₀) (specFibreProductFibre w y)
        (fun j => (specFibreProduct K B Y).germToFunctionField _ (g j)) M →
      ModelThresholdBadAt cY fY d D₀ y
        (fun j => Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
          (specFibreProductFibre_le_preimage w V) (g j))) M := by
  induction e with
  | zero =>
    intro B _ _ _ _ φ hφ g w h
    exact modelThresholdBadAt_fibre_of_fin_zero cY fY hd D₀ hklt φ hφ V g M w y h
  | succ e ih =>
    intro B _ _ _ _ φ hφ g w h
    classical
    -- translate the coordinates to vanish at w
    let c : Fin (e + 1) → K := fun l => w (φ (MvPolynomial.X l))
    let φs : MvPolynomial (Fin (e + 1)) K →ₐ[K] B := φ.comp (mvPolynomialTranslate c).toAlgHom
    have hφs : φs.toRingHom.FormallyEtale := translate_formallyEtale φ hφ c
    have hφsX : ∀ l, φs (MvPolynomial.X l) = φ (MvPolynomial.X l) - algebraMap K B (c l) :=
      translate_X φ c
    have hws : w (φs (MvPolynomial.X 0)) = 0 := by
      rw [hφsX, map_sub, AlgHom.commutes]
      exact sub_self _
    -- localize B so that the hyperplane through w is integral
    obtain ⟨f, hwf, hprime⟩ := exists_away_hyperplane_isPrime φs hφs w hws
    have hf0 : f ≠ 0 := fun h0 => hwf (by rw [h0, map_zero])
    obtain ⟨hdom, hft⟩ := away_isDomain_finiteType (K := K) f hf0
    haveI := hdom
    haveI := hft
    let θ : B →ₐ[K] Localization.Away f := IsScalarTower.toAlgHom K B (Localization.Away f)
    let φ' : MvPolynomial (Fin (e + 1)) K →ₐ[K] Localization.Away f := θ.comp φs
    have hφ' : φ'.toRingHom.FormallyEtale :=
      RingHom.FormallyEtale.comp hφs (RingHom.formallyEtale_algebraMap.mpr
        (Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.Away f) (Submonoid.powers f)))
    have hθ : ∀ l, θ (φ (MvPolynomial.X l)) =
        φ' (MvPolynomial.X l) + algebraMap K (Localization.Away f) (c l) := by
      intro l
      change θ (φ (MvPolynomial.X l)) = θ (φs (MvPolynomial.X l)) + _
      rw [hφsX, map_sub, AlgHom.commutes, sub_add_cancel]
    haveI : (Ideal.span {φ' (MvPolynomial.X 0)}).IsPrime := hprime
    -- the K-point of B_f over w
    have hwu : ∀ s : Submonoid.powers f, IsUnit (w (s : B)) := by
      rintro ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
      change IsUnit (w (f ^ k))
      rw [map_pow]
      exact (isUnit_iff_ne_zero.mpr hwf).pow k
    let w' : Localization.Away f →ₐ[K] K :=
      IsLocalization.liftAlgHom (M := Submonoid.powers f) (S := Localization.Away f) (f := w) hwu
    have hw'θ : w'.comp θ = w := AlgHom.ext fun b => by
      change IsLocalization.lift hwu (algebraMap B (Localization.Away f) b) = w b
      exact IsLocalization.lift_eq hwu b
    have hw'0 : w' (φ' (MvPolynomial.X 0)) = 0 := by
      change (w'.comp θ) (φs (MvPolynomial.X 0)) = 0
      rw [hw'θ]
      exact hws
    have hw0 : ∀ b ∈ Ideal.span {φ' (MvPolynomial.X 0)}, w' b = 0 := by
      intro b hb
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      rw [map_mul, hw'0, mul_zero]
    -- the open sub-product
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap B (Localization.Away f)))))
    haveI : IsOpenImmersion (specFibreProductMap (Y := Y) θ) :=
      specFibreProductMap_isOpenImmersion θ
    haveI : IsDominant (specFibreProductMap (Y := Y) θ) :=
      ⟨(specFibreProductMap (Y := Y) θ).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    rw [← hw'θ] at h
    have h1 := modelThresholdWeakBadAt_fibreProduct_shift θ cY fY d D₀ φ hφ φ' hφ' c hθ w' y _ M h
    have hVθ : specFibreProductSnd K (Localization.Away f) Y ⁻¹ᵁ V ≤
        specFibreProductMap (Y := Y) θ ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V) := fun x hx => by
      change (specFibreProductMap θ ≫ specFibreProductSnd K B Y) x ∈ V
      rw [specFibreProductMap_snd]
      exact hx
    let g' : J → Γ(specFibreProduct K (Localization.Away f) Y,
        specFibreProductSnd K (Localization.Away f) Y ⁻¹ᵁ V) :=
      fun k => (specFibreProductMap (Y := Y) θ).appLE _ _ hVθ (g k)
    have h2 : ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ' hφ')
        (fibreProductPairUnit (K := K) fY) d
        (fibreProductPairDivisor (K := K) (B := Localization.Away f) D₀)
        (specFibreProductFibre (V := Y) w' y)
        (fun k => (specFibreProduct K (Localization.Away f) Y).germToFunctionField _ (g' k)) M := by
      have hfun : (fun k => (specFibreProduct K (Localization.Away f) Y).germToFunctionField _
          (g' k)) = fun k => (dominantFunctionFieldMap (specFibreProductMap (Y := Y) θ)).hom
            ((specFibreProduct K B Y).germToFunctionField _ (g k)) :=
        funext fun k => (dominantFunctionFieldMap_germ _ _ _ hVθ (g k)).symm
      rw [hfun]
      exact h1
    -- the restriction to the hyperplane H = Spec(B_f/(u_0)) ×_K Y
    have hVH : specFibreProductSnd K (Localization.Away f ⧸ Ideal.span {φ' (MvPolynomial.X 0)}) Y
        ⁻¹ᵁ V ≤ specFibreProductMap (Y := Y)
          (Ideal.Quotient.mkₐ K (Ideal.span {φ' (MvPolynomial.X 0)})) ⁻¹ᵁ
          (specFibreProductSnd K (Localization.Away f) Y ⁻¹ᵁ V) := fun x hx => by
      change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ' (MvPolynomial.X 0)})) ≫
        specFibreProductSnd K (Localization.Away f) Y) x ∈ V
      rw [specFibreProductMap_snd]
      exact hx
    let g'' : J → Γ(specFibreProduct K (Localization.Away f ⧸ Ideal.span {φ' (MvPolynomial.X 0)})
        Y, specFibreProductSnd K (Localization.Away f ⧸ Ideal.span {φ' (MvPolynomial.X 0)}) Y ⁻¹ᵁ
          V) :=
      fun k => (specFibreProductMap (Y := Y)
        (Ideal.Quotient.mkₐ K (Ideal.span {φ' (MvPolynomial.X 0)}))).appLE _ _ hVH (g' k)
    -- the restriction to the fibre factors through H
    have hcomp : (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w' hw0) ≫
        specFibreProductMap (Y := Y)
          (Ideal.Quotient.mkₐ K (Ideal.span {φ' (MvPolynomial.X 0)}))) ≫
        specFibreProductMap (Y := Y) θ = specFibreProductFibre (V := Y) w := by
      rw [specFibreProductFibre_comp_map, Ideal.Quotient.liftₐ_comp, specFibreProductFibre_comp_map,
        hw'θ]
    have hfam : ∀ j, (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w' hw0)).appLE _ V
        (specFibreProductFibre_le_preimage _ V) (g'' j) =
        (specFibreProductFibre (V := Y) w).appLE _ V (specFibreProductFibre_le_preimage w V)
          (g j) := by
      intro j
      change (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w' hw0)).appLE _ V _
        ((specFibreProductMap (Y := Y)
          (Ideal.Quotient.mkₐ K (Ideal.span {φ' (MvPolynomial.X 0)}))).appLE _ _ hVH
            ((specFibreProductMap (Y := Y) θ).appLE _ _ hVθ (g j))) = _
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hcomp]
    by_cases hg : ∃ k, (specFibreProduct K (Localization.Away f ⧸
        Ideal.span {φ' (MvPolynomial.X 0)}) Y).germToFunctionField
          (specFibreProductSnd K _ Y ⁻¹ᵁ V) (g'' k) ≠ 0
    · -- the family does not vanish on H: the hypersurface step and the induction hypothesis
      have h3 := klt_hypersurface_step_weakBad hn hnormY hcovY cY fY d hd D₀ heff V hV δ hδ φ' hφ'
        g' hg M hM w' hw0 y hyV hyc h2
      have h4 := ih (Localization.Away f ⧸ Ideal.span {φ' (MvPolynomial.X 0)}) (hyperplaneCoords φ')
        (hyperplaneCoords_formallyEtale φ' hφ') g'' (Ideal.Quotient.liftₐ _ w' hw0) h3
      have hfun : (fun j => Y.germToFunctionField V ((specFibreProductFibre (V := Y) w).appLE _ V
          (specFibreProductFibre_le_preimage w V) (g j))) = fun j => Y.germToFunctionField V
            ((specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w' hw0)).appLE _ V
              (specFibreProductFibre_le_preimage _ V) (g'' j)) :=
        funext fun j => by rw [hfam j]
      rw [hfun]
      exact h4
    · -- the family vanishes on H, hence on the fibre
      simp only [not_exists, ne_eq, not_not] at hg
      have hfun : (fun j => Y.germToFunctionField V ((specFibreProductFibre (V := Y) w).appLE _ V
          (specFibreProductFibre_le_preimage w V) (g j))) = fun _ => 0 := by
        funext j
        rw [← hfam j]
        have h0 : g'' j = 0 := (Scheme.germToFunctionField_injective _ _) (by rw [hg j, map_zero])
        rw [h0, map_zero, map_zero]
      rw [hfun]
      exact modelThresholdBadAt_zero_of_klt hn cY fY hd D₀ hklt y hyc M

end Induction

section Statement

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower specFibreProduct_isIntegral
  specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant specFibreProductSnd_isOver

set_option maxHeartbeats 1600000 in
/-- **The klt restriction theorem on Y × W**: restriction to the fibres of products holds. -/
theorem kltProductFibreRestrictionStatement_holds : KltProductFibreRestrictionStatement K := by
  intro Y _ _ _ _ _ _ n hn hnormY hcovY cY fY d hd D₀ heff hklt B _ _ _ _ e φ hφ V hV _ J _ g M hM
    w y hyV hyc hbad
  classical
  -- an affine neighbourhood of y in V on which D₀ has a local equation
  obtain ⟨δ, hδy⟩ := D₀.exists_isLocalEquationAt y
  obtain ⟨W, hyW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hδy
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  obtain ⟨_, ⟨V', hV', rfl⟩, hyV', hV'le⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ V ⊓ W from ⟨hyV, hyW⟩)
      (V ⊓ W).isOpen
  change IsAffineOpen V' at hV'
  haveI : Nonempty V' := ⟨⟨y, hyV'⟩⟩
  have hV'V : V' ≤ V := fun z hz => (hV'le hz).1
  have hδ : ∀ z ∈ V', D₀.IsLocalEquationAt z δ := fun z hz =>
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hW (hV'le hz).2
  -- the family restricted to V'
  have hpre : specFibreProductSnd K B Y ⁻¹ᵁ V' ≤ specFibreProductSnd K B Y ⁻¹ᵁ V :=
    fun x hx => hV'V hx
  let g' : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V') :=
    fun j => (specFibreProduct K B Y).presheaf.map (homOfLE hpre).op (g j)
  have hgerm : (fun j => (specFibreProduct K B Y).germToFunctionField _ (g' j)) =
      fun j => (specFibreProduct K B Y).germToFunctionField _ (g j) :=
    funext fun j => germToFunctionField_restrict _ hpre (g j)
  have h1 := kltFibreRestriction_of_localEquation hn hnormY hcovY cY fY hd D₀ heff hklt V' hV' δ
    hδ M hM y hyV' hyc e B φ hφ g' w (by rw [hgerm]; exact hbad)
  have hfun : (fun j => Y.germToFunctionField V' ((specFibreProductFibre w).appLE _ V'
      (specFibreProductFibre_le_preimage w V') (g' j))) =
      fun j => Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
        (specFibreProductFibre_le_preimage w V) (g j)) := by
    funext j
    have hres : (specFibreProductFibre w).appLE _ V' (specFibreProductFibre_le_preimage w V')
        ((specFibreProduct K B Y).presheaf.map (homOfLE hpre).op (g j)) =
        (specFibreProductFibre w).appLE _ V'
          (fun z hz => specFibreProductFibre_le_preimage w V (hV'V hz)) (g j) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    change Y.germToFunctionField V' ((specFibreProductFibre w).appLE _ V' _
      ((specFibreProduct K B Y).presheaf.map (homOfLE hpre).op (g j))) = _
    rw [hres]
    exact germToFunctionField_appLE_eq _ _ _ _ _ _ (g j)
  rw [← hfun]
  exact h1

end Statement

/-- **Kawamata's numerical freeness** holds without further hypotheses. -/
theorem kawamataNumericalFreeness_proved : KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_productFibreRestriction fun K _ _ _ =>
    kltProductFibreRestrictionStatement_holds K

/-- **F2 from the base point free theorem for klt pairs and Ambro's canonical bundle formula** for
contractions to lower-dimensional bases. -/
theorem linearEffectiveFreeness_of_basePointFree_of_ambro (hbpf : KltBasePointFreeStatement.{u})
    (hamb : AmbroStrictDimensionStatement.{u}) : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_productFibreRestriction_of_basePointFree_of_ambro
    (fun K _ _ _ => kltProductFibreRestrictionStatement_holds K) hbpf hamb

end MixedFujita
