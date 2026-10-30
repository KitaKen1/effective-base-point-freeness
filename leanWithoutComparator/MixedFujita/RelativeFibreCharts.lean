/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericFibreCharts

/-!
Generic fibre charts on one chart (step 17R-2, section 7 of the manuscript relative to f).

`exists_generic_fibreCharts` needs a morphism from the whole smooth scheme to an affine base. For
relative K-NF the source X is projective and singular, and the base Y is projective: the fibre
charts are needed on one étale chart c of X mapping into an affine open of Y. The proof is that of
`exists_generic_fibreCharts` for the single chart c: for B → Γ(c.U) from a finitely generated
domain there is h ≠ 0 in B such that at every point t₀ of c.U where h is a unit and for every
system u of étale coordinates of B near the image of t₀, some simple normal crossing chart at t₀
inside c.U has the pullbacks of the u_l as its last d coordinates and all its members among the
first n coordinates (`exists_generic_fibreCharts_on_chart`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

section Chart

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- Generic fibre charts on one chart: over a nonempty basic open of the base, every point of the
chart has a simple normal crossing chart inside it whose last coordinates are the pullbacks of
given étale coordinates of the base. -/
theorem exists_generic_fibreCharts_on_chart [CharZero K]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {n d r : ℕ}
    (c : EtaleChart K T (n + d)) (ξ : Fin r → T) (σ : Fin r → Option (Fin (n + d)))
    (hcsnc : IsSNCChart c ξ σ)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (φ : B →ₐ[K] Γ(T, c.U)) :
    ∃ h : B, h ≠ 0 ∧ ∀ (t₀ : T) (ht₀c : t₀ ∈ c.U), IsUnit (T.presheaf.germ c.U t₀ ht₀c (φ h)) →
      ∀ (u : Fin d → B) (b : B), IsUnit (T.presheaf.germ c.U t₀ ht₀c (φ b)) →
        (MvPolynomial.aeval (R := K)
          (fun l => algebraMap B (Localization.Away b) (u l))).toRingHom.FormallyEtale →
        ∃ (Fc : EtaleChart K T (n + d)) (hFc : t₀ ∈ Fc.U) (σF : Fin r → Option (Fin (n + d))),
          Fc.U ≤ c.U ∧ IsSNCChart Fc ξ σF ∧ (∀ k a, σF k = some a → (a : ℕ) < n) ∧
          ∀ l, etaleChartStalkCoords Fc t₀ hFc (MvPolynomial.X (Fin.natAdd n l)) =
            T.presheaf.germ c.U t₀ ht₀c (φ (u l)) := by
  classical
  -- generic smoothness of all the strata of the chart
  have hstr := fun (S : Finset (Fin (n + d))) =>
    exists_generic_formallySmooth_stratum c (↑S) B φ
  choose hS hS0 hSsm using hstr
  refine ⟨∏ S : Finset (Fin (n + d)), hS S, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro S _
    exact hS0 S
  intro t₀ ht₀c ht₀ u b hb hu
  -- the coordinates of the members through t₀
  let S : Finset (Fin (n + d)) :=
    Finset.univ.filter (fun a => ∃ k, σ k = some a ∧ t₀ ∈ closure ({ξ k} : Set T))
  have hunit : IsUnit (T.presheaf.germ c.U t₀ ht₀c (φ (hS S))) := by
    refine isUnit_of_dvd_unit (map_dvd _ (map_dvd _ ?_)) ht₀
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ S)
  -- the prime of t₀ on the chart and the stratum through t₀
  let 𝔮 : Ideal Γ(T, c.U) := (c.isAffine.primeIdealOf ⟨t₀, ht₀c⟩).asIdeal
  let I := etaleChartStratumIdeal c (↑S : Set (Fin (n + d)))
  have hI𝔮 : I ≤ 𝔮 := by
    change etaleChartStratumIdeal c (↑S : Set (Fin (n + d))) ≤ 𝔮
    rw [etaleChartStratumIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, hk, ht₀k⟩ := (Finset.mem_filter.mp ha).2
    have hset := hcsnc.2 k
    rw [hk, Option.elim_some] at hset
    have hm : t₀ ∈ closure ({ξ k} : Set T) ∩ c.U := ⟨ht₀k, ht₀c⟩
    rw [hset, Scheme.zeroLocus_singleton] at hm
    by_contra hnot
    exact hm.1 ((mem_basicOpen_iff_notMem_primeIdealOf c.isAffine t₀ ht₀c _).mpr hnot)
  let p : Ideal (Γ(T, c.U) ⧸ I) := 𝔮.map (Ideal.Quotient.mk I)
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔮 := by rwa [Ideal.mk_ker]
  haveI hp : p.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hpcomap : p.comap (Ideal.Quotient.mk I) = 𝔮 :=
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective 𝔮 |>.trans
      (sup_eq_left.mpr hker)
  have hhp : hS S ∉ p.comap ((Ideal.Quotient.mk I).comp φ.toRingHom) := by
    rw [← Ideal.comap_comap, hpcomap]
    intro hmem'
    have h1 : φ (hS S) ∈ 𝔮 := hmem'
    have h2 := (mem_basicOpen_iff_notMem_primeIdealOf c.isAffine t₀ ht₀c _).mp
      (show t₀ ∈ T.basicOpen (φ (hS S)) from by
        rw [Scheme.mem_basicOpen _ _ _ ht₀c]
        exact hunit)
    exact h2 h1
  have hFS := hSsm S p hhp
  -- the local rings and the field
  letI : Algebra Γ(T, c.U) (T.presheaf.stalk t₀) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf ⟨t₀, ht₀c⟩
  haveI := cartierBaseOpenLocalScalarTower (K := K) t₀ ht₀c
  haveI : IsLocalization.AtPrime (T.presheaf.stalk t₀) 𝔮 :=
    c.isAffine.isLocalization_stalk ⟨t₀, ht₀c⟩
  let gC : Γ(T, c.U) →+* Localization.AtPrime p :=
    (algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p)).comp (Ideal.Quotient.mk I)
  have hgC : ∀ y : 𝔮.primeCompl, IsUnit (gC y) := by
    intro y
    apply IsLocalization.map_units (Localization.AtPrime p) (⟨Ideal.Quotient.mk I y, ?_⟩ :
      p.primeCompl)
    intro hy
    apply y.2
    have h' : (y : Γ(T, c.U)) ∈ p.comap (Ideal.Quotient.mk I) := hy
    rwa [hpcomap] at h'
  let π : T.presheaf.stalk t₀ →+* Localization.AtPrime p :=
    IsLocalization.lift (M := 𝔮.primeCompl) hgC
  have hπ : ∀ γ : Γ(T, c.U), π (algebraMap Γ(T, c.U) (T.presheaf.stalk t₀) γ) = gC γ :=
    fun γ => IsLocalization.lift_eq hgC γ
  have hgerm : ∀ γ : Γ(T, c.U), T.presheaf.germ c.U t₀ ht₀c γ =
      algebraMap Γ(T, c.U) (T.presheaf.stalk t₀) γ := fun γ => rfl
  letI : Algebra B (T.presheaf.stalk t₀) := ((T.presheaf.germ c.U t₀ ht₀c).hom.comp φ).toAlgebra
  letI : Algebra B (Localization.AtPrime p) :=
    ((algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p)).comp
      ((Ideal.Quotient.mk I).comp φ.toRingHom)).toAlgebra
  letI : Algebra (T.presheaf.stalk t₀) (Localization.AtPrime p) := π.toAlgebra
  letI : Algebra (T.presheaf.stalk t₀) (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    ((algebraMap (Localization.AtPrime p) (IsLocalRing.ResidueField (Localization.AtPrime p))).comp
      π).toAlgebra
  letI : Algebra B (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    ((algebraMap (Localization.AtPrime p) (IsLocalRing.ResidueField (Localization.AtPrime p))).comp
      (algebraMap B (Localization.AtPrime p))).toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (T.presheaf.stalk t₀) (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B (T.presheaf.stalk t₀) (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun b' => ?_
    change _ = π (T.presheaf.germ c.U t₀ ht₀c (φ b'))
    rw [hgerm, hπ]
    rfl
  haveI : IsScalarTower K B (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change _ = algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I (φ (algebraMap K B k)))
    rw [AlgHom.commutes, ← Ideal.Quotient.mkₐ_eq_mk K, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower K (T.presheaf.stalk t₀) (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change _ = π (algebraMap K (T.presheaf.stalk t₀) k)
    rw [IsScalarTower.algebraMap_apply K Γ(T, c.U) (T.presheaf.stalk t₀), hπ]
    change _ = algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I (algebraMap K Γ(T, c.U) k))
    rw [← Ideal.Quotient.mkₐ_eq_mk K, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FormallySmooth B (Localization.AtPrime p) := hFS
  -- the base coordinates are independent on the residue field
  have hbF : IsUnit (algebraMap B (IsLocalRing.ResidueField (Localization.AtPrime p)) b) := by
    have h1 : IsUnit (algebraMap B (T.presheaf.stalk t₀) b) := hb
    have h2 := h1.map π
    change IsUnit (algebraMap (T.presheaf.stalk t₀) (Localization.AtPrime p)
      (algebraMap B (T.presheaf.stalk t₀) b)) at h2
    rw [← IsScalarTower.algebraMap_apply] at h2
    exact h2.map (algebraMap (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)))
  letI : Algebra (Localization.Away b) (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    (IsLocalization.Away.lift (S := Localization.Away b) b hbF).toAlgebra
  haveI : IsScalarTower B (Localization.Away b)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := by
    refine IsScalarTower.of_algebraMap_eq fun b' => ?_
    exact (IsLocalization.Away.lift_eq b hbF b').symm
  have hu' : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime p))
      (fun l => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[B]
        KaehlerDifferential.D K B (u l)) := by
    have h1 : (residueKaehlerMap K (R := B) (O' := Localization.Away b)
        (IsLocalRing.ResidueField (Localization.AtPrime p))) ∘
        (fun l => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[B]
          KaehlerDifferential.D K B (u l)) =
        ⇑((etaleCoordinateBasis _ hu).baseChange
          (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
      funext l
      rw [Function.comp_apply, residueKaehlerMap_tmul, Module.Basis.baseChange_apply,
        etaleCoordinateBasis_apply, MvPolynomial.aeval_X]
    exact LinearIndependent.of_comp _ (h1 ▸ ((etaleCoordinateBasis _ hu).baseChange
      (IsLocalRing.ResidueField (Localization.AtPrime p))).linearIndependent)
  -- the member coordinates are independent on the residue field
  let S' := {a : Fin (n + d) // ∃ k, σ k = some a ∧ t₀ ∈ closure ({ξ k} : Set T)}
  let z : S' → T.presheaf.stalk t₀ := fun a =>
    etaleChartStalkCoords c t₀ ht₀c (MvPolynomial.X a.1)
  have hz : ∀ a, algebraMap (T.presheaf.stalk t₀) (Localization.AtPrime p) (z a) = 0 := by
    intro a
    change π (algebraMap Γ(T, c.U) (T.presheaf.stalk t₀)
      (c.coords (MvPolynomial.X a.1))) = 0
    rw [hπ]
    change algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I (c.coords (MvPolynomial.X a.1))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
    change c.coords (MvPolynomial.X a.1) ∈
      etaleChartStratumIdeal c (↑S : Set (Fin (n + d)))
    rw [etaleChartStratumIdeal_eq_span]
    exact Ideal.subset_span ⟨a.1, Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, a.2⟩), rfl⟩
  have hzind : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime p))
      (fun a => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[T.presheaf.stalk t₀]
        KaehlerDifferential.D K (T.presheaf.stalk t₀) (z a)) := by
    have h1 : (fun a : S' => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[
        T.presheaf.stalk t₀] KaehlerDifferential.D K (T.presheaf.stalk t₀) (z a)) =
        ⇑((etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale c t₀
          ht₀c)).baseChange (IsLocalRing.ResidueField (Localization.AtPrime p))) ∘
          Subtype.val := by
      funext a
      rw [Function.comp_apply, Module.Basis.baseChange_apply, etaleCoordinateBasis_apply]
    rw [h1]
    exact ((etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale c t₀
      ht₀c)).baseChange (IsLocalRing.ResidueField (Localization.AtPrime p))).linearIndependent.comp
      _ Subtype.val_injective
  have hind := linearIndependent_kaehler_of_formallySmooth_quotient K (R := B)
    (O := T.presheaf.stalk t₀) (O' := Localization.AtPrime p)
    (F := IsLocalRing.ResidueField (Localization.AtPrime p)) z hz u hu' hzind
  -- the residue field kills the maximal ideal of the stalk
  have hF : ∀ x ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk t₀),
      algebraMap (T.presheaf.stalk t₀) (IsLocalRing.ResidueField (Localization.AtPrime p)) x = 0 := by
    intro x hx
    obtain ⟨⟨γ, y⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    have hγ : γ ∈ 𝔮 := (IsLocalization.AtPrime.mk'_mem_maximal_iff _ 𝔮 γ y).mp hx
    change IsLocalRing.residue _ (π (IsLocalization.mk' (T.presheaf.stalk t₀) γ y)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalization.lift_mk']
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap (Γ(T, c.U) ⧸ I) (Localization.AtPrime p) (Ideal.Quotient.mk I γ) ∈ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ p]
    exact Ideal.mem_map_of_mem _ hγ
  obtain ⟨Fc, hFc, σF, hFle, hFsnc, hFlt, hFcoord⟩ :=
    exists_fibreChart ξ σ t₀ c ht₀c hcsnc
      (fun l => algebraMap B (T.presheaf.stalk t₀) (u l))
      (IsLocalRing.ResidueField (Localization.AtPrime p)) hF hind
  exact ⟨Fc, hFc, σF, hFle, hFsnc, hFlt, hFcoord⟩

end Chart

end MixedFujita
