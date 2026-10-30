/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationGeneration

/-!
Section 6 of the manuscript with the centre in a closed set (step 17R-1).

In section 6 the members of S are assumed to map to one closed point x of V, and the only use of
this is that the support Z of S lies in the preimage of an open set on which a local equation of P
is defined: the pulled back equation then trivializes ρ*P near Z. Here the point x is replaced by a
closed subset Φ of V contained in an open set V₀ on which one rational function f is a local
equation of P. The conclusion is that P has a global section generating it at some point of Φ,
with the given local equation f. For relative K-NF, V is the normal variety X of the klt pair,
P = f*P_Y is the pullback of a Cartier divisor of the base, Φ is the fibre over a closed point y
of the base and V₀ the preimage of an open neighbourhood of y on which P_Y has a local equation.

* `exists_section_generating_of_lifting_of_open`: the lifting and descent of section 6.3;
* `exists_section_generating_of_floor_vanishing_of_open`: the same in terms of the round-down;
* `isolation_model_exists_section_generating_of_open`: on the isolation model;
* `isolation_model_exists_section_generating_of_vanishing_of_open`: with the vanishing in the form
  produced by the numerical statement (27);
* `exists_section_generating_of_minimizer_data_of_vanishing_of_open`: from the data of the
  minimizer over Φ.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

section Descent

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian T]

/-- Lifting and descent (section 6.3) with a given local equation. Let ρ : T → Y be a proper
birational morphism of normal schemes, P a Cartier divisor of Y with a local equation f on an open
set Y₀, C a Cartier divisor of T and S an effective Cartier divisor of T with
H¹(T, O(ρ*P + C − S)) = 0. Let Z be a closed subset of T mapping into Y₀, outside of which S has
coefficient zero, with C ≥ 0 at the codimension-one points of an open neighbourhood of Z, C ≤ 0
at the codimension-one points of T which are not exceptional, and let ξ be a codimension-one point
of Z at which S has positive coefficient and C coefficient zero. Then P has a global section
generating it at the image of ξ, with the local equation f. -/
theorem exists_section_generating_of_lifting_of_open
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ Y) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (P : CartierDivisor Y) (C Sd : CartierDivisor T) (hSd : Sd.IsEffective)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (cartierPullback ρ P + C - Sd).sheaf 1))
    (Z : Set T) (hZ : IsClosed Z)
    (hSdZ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Z → cartierCoefficient Sd (z : T) = 0)
    (W₀ : T.Opens) (hZW₀ : Z ⊆ W₀)
    (hCW₀ : ∀ z : CodimensionOnePoint T, (z : T) ∈ W₀ → 0 ≤ cartierCoefficient C (z : T))
    (hCexc : ∀ z : CodimensionOnePoint T, Order.coheight (ρ (z : T)) = 1 →
      cartierCoefficient C (z : T) ≤ 0)
    (ξ : CodimensionOnePoint T) (hξZ : (ξ : T) ∈ Z) (hSdξ : 1 ≤ cartierCoefficient Sd (ξ : T))
    (hCξ : cartierCoefficient C (ξ : T) = 0)
    (f : Y.functionFieldˣ) (Y₀ : Y.Opens) (hY₀ : ∀ y ∈ Y₀, P.IsLocalEquationAt y f)
    (hZY₀ : ∀ t ∈ Z, ρ t ∈ Y₀) :
    ∃ (g : Y.functionField) (u : (Y.presheaf.stalk (ρ (ξ : T)))ˣ),
      (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (Y.presheaf.stalk (ρ (ξ : T))) Y.functionField u = f * g := by
  have hxY₀ : ρ (ξ : T) ∈ Y₀ := hZY₀ _ hξZ
  have hf : P.IsLocalEquationAt (ρ (ξ : T)) f := hY₀ _ hxY₀
  have : Nonempty Y₀ := ⟨⟨ρ (ξ : T), hxY₀⟩⟩
  have hφf0 : (dominantFunctionFieldMap ρ).hom (f : Y.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero f)
  have hZW : Z ⊆ ((ρ ⁻¹ᵁ Y₀) ⊓ W₀ : T.Opens) := fun t ht => ⟨hZY₀ t ht, hZW₀ ht⟩
  -- the coefficient of ρ*P over Y₀ is the order of the pulled back equation
  have hcoefP : ∀ t : T, ρ t ∈ Y₀ → cartierCoefficient (cartierPullback ρ P) t =
      T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField)) t := fun t ht => by
    rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ P t (hY₀ (ρ t) ht))]
    rfl
  have hgW : ∀ z : CodimensionOnePoint T, (z : T) ∈ ((ρ ⁻¹ᵁ Y₀) ⊓ W₀ : T.Opens) →
      0 ≤ T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField))⁻¹ (z : T) +
        cartierCoefficient (cartierPullback ρ P + C) (z : T) := by
    intro z hz
    rw [Scheme.ord_inv, cartierCoefficient_add, hcoefP (z : T) hz.1]
    have h1 := hCW₀ z hz.2
    linarith
  have hgen : T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField))⁻¹ (ξ : T) +
      cartierCoefficient (cartierPullback ρ P + C) (ξ : T) = 0 := by
    rw [Scheme.ord_inv, cartierCoefficient_add, hcoefP (ξ : T) hxY₀, hCξ]
    ring
  obtain ⟨gT, hgT0, hgT, hgTξ⟩ := exists_global_section_ord_eq_of_vanishing hnormT
    (cartierPullback ρ P + C) Sd hSd hvan Z hZ hSdZ _ hZW _ (inv_ne_zero hφf0) hgW ξ hξZ hSdξ
    hgen
  obtain ⟨g, rfl⟩ := hρ.2 gT
  have hg0 : g ≠ 0 := fun h => hgT0 (by rw [h, map_zero])
  have hneT : Nonempty (⊤ : T.Opens) := ⟨⟨(ξ : T), trivial⟩⟩
  have hneY : Nonempty (⊤ : Y.Opens) := ⟨⟨ρ (ξ : T), trivial⟩⟩
  -- descent: g is a section of P
  have hgP : (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ := by
    apply cartier_mem_sections_of_forall_ord hnormY P ⊤ g
    intro y _
    obtain ⟨t, ht, hb⟩ := proper_birational_exists_normal_prime_lift hnormY ρ hρ y
    have hcoh : Order.coheight (ρ (t : T)) = 1 := by rw [ht]; exact y.property
    let := hnormY (ρ (t : T))
    let := hnormT (t : T)
    have : IsDiscreteValuationRing (Y.presheaf.stalk (ρ (t : T))) :=
      normal_codimensionOne_stalk_DVR (⟨ρ (t : T), hcoh⟩ : CodimensionOnePoint Y)
    have : IsDiscreteValuationRing (T.presheaf.stalk (t : T)) := normal_codimensionOne_stalk_DVR t
    have h1 := scheme_ord_pullback_of_stalkMap_bijective ρ t hcoh hb g
    have h2 := cartierCoefficient_pullback_of_stalkMap_bijective ρ t hcoh hb P
    have h3 := cartier_ord_add_coefficient_nonneg_of_mem_sections (cartierPullback ρ P + C) ⊤
      ((dominantFunctionFieldMap ρ).hom g) hgT hgT0 (t : T) trivial
    rw [cartierCoefficient_add] at h3
    have h4 := hCexc t hcoh
    rw [← ht, ← h1, ← h2]
    linarith
  -- generation at the image of ξ
  obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hgP) (ρ (ξ : T)) trivial f hf
  rw [LinearEquiv.apply_symm_apply] at ha
  let := hnormT (ξ : T)
  have : IsDiscreteValuationRing (T.presheaf.stalk (ξ : T)) := normal_codimensionOne_stalk_DVR ξ
  have hpull : (dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g) =
      algebraMap (T.presheaf.stalk (ξ : T)) T.functionField (ρ.stalkMap (ξ : T) a) := by
    rw [← ha, dominantFunctionFieldMap_algebraMap]
  have hne : (dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g) ≠ 0 :=
    (map_ne_zero _).mpr (mul_ne_zero (Units.ne_zero f) hg0)
  have hord0 : T.ord ((dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g)) (ξ : T) =
      0 := by
    rw [map_mul, T.ord_mul hφf0 hgT0, ← hcoefP (ξ : T) hxY₀]
    rw [cartierCoefficient_add, hCξ] at hgTξ
    linarith
  obtain ⟨v, hv⟩ := scheme_ord_zero_exists_stalk_unit ξ (Units.mk0 _ hne) hord0
  have hva : ρ.stalkMap (ξ : T) a = (v : T.presheaf.stalk (ξ : T)) := by
    apply IsFractionRing.injective (T.presheaf.stalk (ξ : T)) T.functionField
    rw [← hpull, hv]
    rfl
  have hunit : IsUnit a := by
    have hv' : IsUnit (ρ.stalkMap (ξ : T) a) := by rw [hva]; exact v.isUnit
    exact isUnit_of_map_unit (ρ.stalkMap (ξ : T)).hom a hv'
  exact ⟨g, hunit.unit, hgP, by rw [IsUnit.unit_spec]; exact ha⟩

end Descent

section Lifting

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian T]

/-- The lifting of section 6.3 in terms of the round-down, with the centre in a closed set. Let
ρ : T → Y be a proper birational morphism of normal schemes, P a Cartier divisor of Y with a local
equation f on an open set Y₀ containing the closed set Φ, ξ_k distinct prime divisors of T with
member divisors E_k, and Γ_k real numbers. Let S be a nonempty set of indices whose members map
into Φ, with Γ_k = 1 on S, Γ_k < 1 for the other members meeting a member of S and Γ_k ≥ 0 for the
members not exceptional over Y. If H¹(T, O(ρ*P − Σ ⌊Γ_k⌋ E_k)) = 0, then P has a global section
generating it, with the local equation f, at some point of Φ. -/
theorem exists_section_generating_of_floor_vanishing_of_open
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ Y) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (P : CartierDivisor Y) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (E : Fin r → CartierDivisor T)
    (hE : ∀ i, (E i).IsEffective)
    (hEc : ∀ (i : Fin r) (z : CodimensionOnePoint T),
      cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0)
    (Γ : Fin r → ℝ) (S : Set (Fin r)) (hS : S.Nonempty) (Φ : Set Y) (hΦ : IsClosed Φ)
    (hSΦ : ∀ k ∈ S, ρ (ξ k) ∈ Φ) (f : Y.functionFieldˣ) (Y₀ : Y.Opens)
    (hΦY₀ : Φ ⊆ (Y₀ : Set Y)) (hY₀ : ∀ y ∈ Y₀, P.IsLocalEquationAt y f)
    (hSΓ : ∀ k ∈ S, Γ k = 1)
    (hmeet : ∀ k, k ∉ S →
      (∃ k' ∈ S, (closure ({ξ k} : Set T) ∩ closure ({ξ k'} : Set T)).Nonempty) → Γ k < 1)
    (hexc : ∀ k, Order.coheight (ρ (ξ k)) = 1 → 0 ≤ Γ k)
    (hvan : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ P - ∑ k, ⌊Γ k⌋ • E k).sheaf 1)) :
    ∃ v ∈ Φ, ∃ (g : Y.functionField) (u : (Y.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (Y.presheaf.stalk v) Y.functionField u = f * g := by
  obtain ⟨k₀, hk₀⟩ := hS
  -- the indicator of S, the divisors S and C
  let σ : Fin r → ℤ := fun k => if k ∈ S then 1 else 0
  have hσS : ∀ k, k ∈ S → σ k = 1 := fun k hk => ite_eq_left hk
  have hσN : ∀ k, k ∉ S → σ k = 0 := fun k hk => ite_eq_right hk
  have hfloorS : ∀ k, k ∈ S → ⌊Γ k⌋ = 1 := fun k hk => by
    rw [hSΓ k hk]
    exact Int.floor_one
  let Sd : CartierDivisor T := ∑ k, σ k • E k
  let C : CartierDivisor T := ∑ k, (σ k - ⌊Γ k⌋) • E k
  have hSd : Sd.IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro k _
    by_cases hk : k ∈ S
    · rw [hσS k hk, one_zsmul]
      exact hE k
    · rw [hσN k hk, zero_zsmul]
      exact CartierDivisor.isEffective_zero
  have hQ : cartierPullback ρ P + C - Sd = cartierPullback ρ P - ∑ k, ⌊Γ k⌋ • E k := by
    have hC : C = Sd - ∑ k, ⌊Γ k⌋ • E k := by
      change ∑ k, (σ k - ⌊Γ k⌋) • E k = ∑ k, σ k • E k - ∑ k, ⌊Γ k⌋ • E k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_zsmul, sub_eq_add_neg]
    rw [hC]
    abel
  have hvan' : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ P + C - Sd).sheaf 1) := by
    rw [hQ]
    exact hvan
  have hcoefSd := cartierCoefficient_member_combination ξ hinj E hEc σ
  have hcoefC := cartierCoefficient_member_combination ξ hinj E hEc fun k => σ k - ⌊Γ k⌋
  -- the support of S and the neighbourhood on which C is effective
  let Z : Set T := ⋃ k ∈ S, closure ({ξ k} : Set T)
  have hZ : IsClosed Z := (Set.toFinite S).isClosed_biUnion fun k _ => isClosed_closure
  let N : Set (Fin r) := {k | σ k - ⌊Γ k⌋ < 0}
  have hNclosed : IsClosed (⋃ k ∈ N, closure ({ξ k} : Set T)) :=
    (Set.toFinite N).isClosed_biUnion fun k _ => isClosed_closure
  let W₀ : T.Opens := ⟨(⋃ k ∈ N, closure ({ξ k} : Set T))ᶜ, hNclosed.isOpen_compl⟩
  have hSdZ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Z → cartierCoefficient Sd (z : T) = 0 := by
    intro z hz
    rcases hcoefSd z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      apply hσN
      intro hk
      exact hz (Set.mem_biUnion hk (by rw [hzk]; exact subset_closure rfl))
    · exact hco
  have hZW₀ : Z ⊆ W₀ := by
    intro t ht
    obtain ⟨k', hk', htk'⟩ := Set.mem_iUnion₂.mp ht
    change t ∉ ⋃ k ∈ N, closure ({ξ k} : Set T)
    intro htN
    obtain ⟨k, hkN, htk⟩ := Set.mem_iUnion₂.mp htN
    have hneg : σ k - ⌊Γ k⌋ < 0 := hkN
    by_cases hk : k ∈ S
    · rw [hσS k hk, hfloorS k hk] at hneg
      exact lt_irrefl _ hneg
    · have hlt : Γ k < 1 := hmeet k hk ⟨k', hk', t, htk, htk'⟩
      have hfl : ⌊Γ k⌋ < 1 := Int.floor_lt.mpr (by exact_mod_cast hlt)
      rw [hσN k hk] at hneg
      omega
  have hCW₀ : ∀ z : CodimensionOnePoint T, (z : T) ∈ W₀ → 0 ≤ cartierCoefficient C (z : T) := by
    intro z hz
    rcases hcoefC z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      by_contra hneg
      apply hz
      exact Set.mem_biUnion (show k ∈ N from not_le.mp hneg)
        (by rw [hzk]; exact subset_closure rfl)
    · exact hco.ge
  have hCexc : ∀ z : CodimensionOnePoint T, Order.coheight (ρ (z : T)) = 1 →
      cartierCoefficient C (z : T) ≤ 0 := by
    intro z hzρ
    rcases hcoefC z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      rw [hzk] at hzρ
      have hfl : 0 ≤ ⌊Γ k⌋ := Int.floor_nonneg.mpr (hexc k hzρ)
      by_cases hk : k ∈ S
      · rw [hσS k hk, hfloorS k hk]
        exact le_of_eq (sub_self _)
      · rw [hσN k hk]
        omega
    · exact hco.le
  have hξZ : ξ k₀ ∈ Z := Set.mem_biUnion hk₀ (subset_closure rfl)
  have hSdξ : 1 ≤ cartierCoefficient Sd (ξ k₀) := by
    rcases hcoefSd ⟨ξ k₀, hξ k₀⟩ with ⟨k, hzk, hco⟩ | ⟨hz, -⟩
    · have hkk : k₀ = k := hinj hzk
      rw [hco, ← hkk, hσS k₀ hk₀]
    · exact absurd ⟨k₀, rfl⟩ hz
  have hCξ : cartierCoefficient C (ξ k₀) = 0 := by
    rcases hcoefC ⟨ξ k₀, hξ k₀⟩ with ⟨k, hzk, hco⟩ | ⟨hz, -⟩
    · have hkk : k₀ = k := hinj hzk
      rw [hco, ← hkk, hσS k₀ hk₀, hfloorS k₀ hk₀]
      exact sub_self _
    · exact absurd ⟨k₀, rfl⟩ hz
  -- the support of S maps into Φ, hence into Y₀
  have hZY₀ : ∀ t ∈ Z, ρ t ∈ Y₀ := by
    intro t ht
    obtain ⟨k, hk, htk⟩ := Set.mem_iUnion₂.mp ht
    have h1 : ρ t ∈ closure ({ρ (ξ k)} : Set Y) := by
      have h := image_closure_subset_closure_image ρ.continuous (Set.mem_image_of_mem ρ htk)
      rwa [Set.image_singleton] at h
    have h2 : closure ({ρ (ξ k)} : Set Y) ⊆ Φ :=
      hΦ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (hSΦ k hk))
    exact hΦY₀ (h2 h1)
  obtain ⟨g, u, hg, hu⟩ := exists_section_generating_of_lifting_of_open hnormY hnormT ρ hρ P C
    Sd hSd hvan' Z hZ hSdZ W₀ hZW₀ hCW₀ hCexc ⟨ξ k₀, hξ k₀⟩ hξZ hSdξ hCξ f Y₀ hY₀ hZY₀
  exact ⟨ρ (ξ k₀), hSΦ k₀ hk₀, g, u, hg, hu⟩

end Lifting

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

variable {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsProper ρ]

/-- The lifting of section 6.3 on the isolation model, with the centre in a closed set Φ of V
contained in an open set V₀ on which f is a local equation of P: as
`isolation_model_exists_section_generating`, with the members of S mapping into Φ; the
conclusion is a global section of P generating it, with the local equation f, at a point of Φ. -/
theorem isolation_model_exists_section_generating_of_open
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (Φ : Set V) (hΦ : IsClosed Φ) (fP : V.functionFieldˣ) (V₀ : V.Opens)
    (hΦV₀ : Φ ⊆ (V₀ : Set V)) (hV₀ : ∀ v ∈ V₀, P.IsLocalEquationAt v fP)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1) (E : Fin r' → CartierDivisor T)
    (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective) (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i)
    (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (S : Set (Fin r')) (hS : S.Nonempty)
    (hSΦ : ∀ k ∈ S, π (ρ (ξT k)) ∈ Φ)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (hvan : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ (cartierPullback π P) -
        ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
          etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k).sheaf
      1)) :
    ∃ v ∈ Φ, ∃ (g : V.functionField) (u : (V.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (V.presheaf.stalk v) V.functionField u = fP * g := by
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  have hρ' : Function.Bijective (dominantFunctionFieldMap ρ).hom := hρ
  have hτ : Function.Bijective (dominantFunctionFieldMap (ρ ≫ π)).hom := by
    rw [dominantFunctionFieldMap_comp π ρ]
    exact hρ'.comp hπ
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  -- Γ = 1 − (log discrepancy) + Ψ
  have hΓ : ∀ t : T, isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT etaleCharts_cover)
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc t =
      1 - ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) t) / d +
        ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) t : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc t : ℝ)) := by
    intro t
    unfold isolationGammaCoefficient
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, Int.cast_neg]
    field_simp
    ring
  refine exists_section_generating_of_floor_vanishing_of_open hnormV hnormT (ρ ≫ π) hτ P ξT
    hinjT hξT E hE hEc _ S hS Φ hΦ hSΦ fP V₀ hΦV₀ hV₀ ?_ ?_ ?_
    (by rw [cartierPullback_comp π ρ P]; exact hvan)
  · intro k hk
    rw [hΓ (ξT k), hSeq k hk]
    ring
  · intro k hk hex
    obtain ⟨hle, heq⟩ := hSmeet ⟨ξT k, hξT k⟩ hex
    have hlt := lt_of_le_of_ne hle fun h => by
      obtain ⟨k', hk', hkk'⟩ := heq h
      have hkk : k = k' := hinjT hkk'
      exact hk (hkk ▸ hk')
    rw [hΓ (ξT k)]
    linarith
  · intro k hcoh
    have hcoh' : Order.coheight (π (ρ (ξT k))) = 1 := hcoh
    have hbπ := stalkMap_bijective_of_birational_over_normal_prime hnormV π hπ (ρ (ξT k)) hcoh'
    have hcohX : Order.coheight (ρ (ξT k)) = 1 :=
      (coheight_eq_of_stalkMap_bijective π (ρ (ξT k)) hbπ).trans hcoh'
    have hBT := crepantBoundaryCartier_coefficient_of_coheight_eq_one ρ hρ c₀ f₀ d B cT
      ⟨ξT k, hξT k⟩ hcohX
    have hB0 : (0 : ℝ) ≤ (cartierCoefficient B (ρ (ξT k)) : ℝ) := by
      exact_mod_cast hBexc ⟨ρ (ξT k), hcohX⟩ hcoh'
    have hD0 : ∀ i, (0 : ℝ) ≤ (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) :=
      fun i => by
        exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
          (cartierPullback_isEffective ρ (Dv i) (hDeff i)) (ξT k)
    have hG0 : (0 : ℝ) ≤ (cartierCoefficient Gc (ξT k) : ℝ) := by
      exact_mod_cast cartierCoefficient_nonneg_of_isEffective Gc hGc (ξT k)
    unfold isolationGammaCoefficient
    rw [hBT]
    have h1 : (0 : ℝ) ≤ (cartierCoefficient B (ρ (ξT k)) : ℝ) / d := div_nonneg hB0 hdpos.le
    have h2 : (0 : ℝ) ≤ (1 - η) * ∑ i, c₁ i *
        (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) :=
      mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => mul_nonneg (hc₁ i) (hD0 i))
    have h3 : (0 : ℝ) ≤ η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) :=
      mul_nonneg (div_nonneg hη0 (Nat.cast_nonneg Mn)) hG0
    linarith

/-- Sections 6.1 to 6.3 on a given isolation model with the centre in a closed set, with the
vanishing as a hypothesis in the form produced by the numerical statement (27). -/
theorem isolation_model_exists_section_generating_of_vanishing_of_open
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (Φ : Set V) (hΦ : IsClosed Φ) (fP : V.functionFieldˣ) (V₀ : V.Opens)
    (hΦV₀ : Φ ⊆ (V₀ : Set V)) (hV₀ : ∀ v ∈ V₀, P.IsLocalEquationAt v fP)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1)
    (E : Fin r' → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (S : Set (Fin r')) (hS : S.Nonempty) (hSΦ : ∀ k ∈ S, π (ρ (ξT k)) ∈ Φ)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') (he₁pos : 1 ≤ e₁)
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hLbig : CartierIsBig K (cartierPullback ρ LX))
    (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc))
    (hvan : ∀ a : Fin r' → ℕ, (∀ k, a k < m' * d) → ∀ D₁ : CartierDivisor T,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + m' • cartierPullback ρ NX →
      CartierIsNef K D₁ → CartierIsBig K D₁ →
      Subsingleton (Scheme.Modules.Cohomology
        (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k).sheaf 1)) :
    ∃ v ∈ Φ, ∃ (g : V.functionField) (u' : (V.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (V.presheaf.stalk v) V.functionField u' = fP * g := by
  obtain ⟨a, halt, D₁, hdec, hnef, hbig⟩ := isolation_model_floor_divisor_nef_big ρ hρ π P c₀ f₀ d
    hd B Dv cT ξT hinjT E hEc hTB hTD Gc hGc hTG c₁ Mn η LX NX hLN j hDlin m' hm' p w u e₁ hp hw
    he₁ he₁pos hLnef hLbig hLfin hGG
  exact isolation_model_exists_section_generating_of_open ρ hρ hnormV π hπ P Φ hΦ fP V₀ hΦV₀ hV₀
    c₀ f₀ d hd B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc Gc hGc c₁ hc₁ Mn η hη0 hη1 S hS hSΦ hSeq
    hSmeet (hvan a halt D₁ hdec hnef hbig)

end Model

section Generation

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X V : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral V] [IsLocallyNoetherian V]

/-- Section 6 as one statement with the centre in a closed set: as
`exists_section_generating_of_minimizer_data_of_vanishing`, with the data of the minimizer over the
closed set Φ of V (the polytope membership at a point over Φ, the inequality (24) over Φ and the
centre property for π⁻¹(Φ)), where Φ lies in an open set V₀ on which fP is a local equation of P.
The conclusion is a global section of P generating it, with the local equation fP, at a point of
Φ. -/
theorem exists_section_generating_of_minimizer_data_of_vanishing_of_open
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (Φ : Set V) (hΦ : IsClosed Φ) (fP : V.functionFieldˣ) (V₀ : V.Opens)
    (hΦV₀ : Φ ⊆ (V₀ : Set V)) (hV₀ : ∀ v ∈ V₀, P.IsLocalEquationAt v fP)
    {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hjm₀ : m₀ ∣ j)
    (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • LX))
    (hLbig : CartierIsBig K LX) (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • LX).sheaf, ⊤))
    (y : X) (hy : π y ∈ Φ) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' Φ, InSNCProfilePolytope ξ d B Dv q p →
      ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' Φ).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ π ⁻¹' Φ)
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1)
    (hvan : ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
      [T.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
      [IsProper (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
      [ρ.IsOver (Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r' : ℕ) (ξT : Fin r' → T),
      Function.Injective ξT → (∀ k, Order.coheight (ξT k) = 1) → IsSNCFamily K n ξT →
      ∀ E : Fin r' → CartierDivisor T,
        (∀ (k : Fin r') (z : CodimensionOnePoint T),
          cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0) →
      ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r' → ℕ, (∀ k, a k < m) →
      ∀ (D₁ : CartierDivisor T) (m' : ℕ),
        m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + m' • cartierPullback ρ NX →
        CartierIsNef K D₁ → CartierIsBig K D₁ →
        Subsingleton (Scheme.Modules.Cohomology Q.sheaf 1)) :
    ∃ v ∈ Φ, ∃ (g : V.functionField) (u : (V.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (V.presheaf.stalk v) V.functionField u = fP * g := by
  have hΦX : IsClosed (π ⁻¹' Φ) := hΦ.preimage π.continuous
  obtain ⟨c₁, q₀, Mn, nn, hc₁, hc₁rat, hq₀, hq₀rat, hc₁q₀, hbud₁, hMn, hI, hnn, hAeff, T, hTi, hTo,
    hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r', ξT, Gc, hGc, hinjT, hξT, hsncT, hTB, hTD, hTG,
    hGcI, hgg, hS⟩ := exists_isolation_model ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hDeff hD
      (π ⁻¹' Φ) hΦX y hy hc hcq hqy hpolyΦ hcentre (Nat.cast_nonneg (d * j)) hbudget
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hpropT : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  -- the member divisors of the family of T
  obtain ⟨E, hE, -, hEc⟩ := exists_snc_component_cartier ξT hξT hsncT
  -- the multiple u of A_X
  obtain ⟨j', rfl⟩ := hjm₀
  let U : ℕ := ∑ i, nn i * j'
  have hGG : CartierIsGloballyGenerated (cartierPullback ρ ((m₀ * U) • LX) - Gc) := by
    refine (hgg ((m₀ * U) • LX) fun k => ?_).1
    obtain ⟨h, hh⟩ := hDlin k.1
    have hle : nn k.1 * j' ≤ U :=
      Finset.single_le_sum (f := fun i => nn i * j') (fun i _ => Nat.zero_le _)
        (Finset.mem_univ k.1)
    obtain ⟨V', hV'⟩ : ∃ V', V' + nn k.1 * j' = U := ⟨U - nn k.1 * j', Nat.sub_add_cancel hle⟩
    have heq : (m₀ * U) • LX - nn k.1 • Dv k.1 =
        (V' * m₀) • LX + principalCartierDivisor X (h⁻¹ ^ nn k.1) := by
      rw [hh, principalCartierDivisor_power, principalCartierDivisor_inv, ← hV']
      module
    rw [heq]
    exact cartierIsGloballyGenerated_principal_shift _ _ (hLgg V')
  -- the integers of section 6.3
  obtain ⟨η, m', p, w, e₁, hη0, hη1, hm', he₁pos, hp, hw, he₁⟩ :=
    exists_isolation_integers c₁ hc₁ hc₁rat Mn hMn d hd (m₀ * j') (m₀ * U) hbud₁
  obtain ⟨S, hSne, hSprop, hSmeet⟩ := hS η hη0 hη1
  -- positivity of ρ*L_X
  have hLnef : CartierIsNef K (cartierPullback ρ LX) :=
    cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul ρ LX m₀ hm₀
      (by simpa using hLgg 1)
  have hdim : topologicalKrullDim T = topologicalKrullDim X :=
    (etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim c₀).symm
  have hLbigT : CartierIsBig K (cartierPullback ρ LX) :=
    cartierIsBig_cartierPullback hnormX hnormT ρ hρ hdim hLbig
  have hLfinT : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤) :=
    fun k => by
      rw [← cartierPullback_nsmul]
      exact finiteDimensional_sections_cartierPullback hnormX ρ hρ (k • LX) (hLfin k)
  exact isolation_model_exists_section_generating_of_vanishing_of_open ρ hρ hnormV π hπ P Φ hΦ fP
    V₀ hΦV₀ hV₀ c₀ f₀ d hd B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc hTB hTD Gc hGc hTG c₁
    (fun i => (hc₁ i).le) Mn η hη0.le hη1.le S hSne (fun k hk => (hSprop k hk).1)
    (fun k hk => (hSprop k hk).2) hSmeet LX NX hLN (m₀ * j') hDlin m' hm' p w (m₀ * U) e₁ hp hw
    he₁ he₁pos hLnef hLbigT hLfinT hGG
    (fun a halt D₁ hdec hnef hbig => hvan T ρ cT r' ξT hinjT hξT hsncT E hEc _ (m' * d)
      (Nat.mul_pos hm' hd) a halt D₁ m' hdec hnef hbig)

end Generation

end MixedFujita
