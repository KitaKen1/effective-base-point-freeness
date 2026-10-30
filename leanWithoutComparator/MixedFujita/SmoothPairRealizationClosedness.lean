/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothPairBoundaryAbsorption
public import MixedFujita.ZeroNormalizedProfile
public import MixedFujita.ClosedPointRealizationFromLemmaThree

/-!
The closedness on closed points of the realization sets of a klt pair with effective boundary on a
smooth variety (step 15).

For the zero pair this is check 305 (from Lemma 3 in the model form on affine opens, check 559).
For a pair (c_Y, f_Y, d, D₀) with effective boundary E₀ = d B, the boundary is absorbed into the
polynomial family on an affine open on which E₀ has a regular local equation h
(`exists_affine_localEquation_regular_pair`): a tuple realizes a profile at a closed point of the
open exactly when the zero pair has threshold at most 1/(d M) for the family
((Σ_k c_ik r_k)^(e_i))^d h^M (`exists_ideal_realization_on_affine_pair`, check 560). The rest of
the argument of check 305 applies verbatim: the flag closedness under lower triangular changes
(`exists_closed_realizedSet_on_affine_pair`, `isClosedOnClosedPoints_realized_pair`), the
normalized profiles as a countable intersection (`isClosedOnClosedPoints_normalizedProfiles_pair`),
and the zero profile realized at every closed point by a toric extraction, now with the klt pair
(`zero_mem_sncWeightNormalizedProfiles_pair`). The form used by K-NF is
`closedPointRealization_pair`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Chart

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- Around a point, a Cartier divisor has a local equation f on an affine open on which given
sections are f times regular functions, and an effective Cartier divisor has a local equation
which is a regular function there. -/
theorem exists_affine_localEquation_regular_pair (E : CartierDivisor Y) (hE : E.IsEffective)
    (D : CartierDivisor Y) (x₀ : Y) {m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤)) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : x₀ ∈ V) (f : Y.functionFieldˣ)
      (r : Fin m → Γ(Y, V)) (e₀ : Y.functionFieldˣ) (h : Γ(Y, V)),
      (∀ y ∈ V, D.IsLocalEquationAt y f) ∧ (∀ y ∈ V, E.IsLocalEquationAt y e₀) ∧
        ∀ (_ : Nonempty V), (∀ k, Y.germToFunctionField V (r k) =
          (f : Y.functionField) * cartierSectionRational D (b k)) ∧
          Y.germToFunctionField V h = (e₀ : Y.functionField) := by
  classical
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x₀
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have hWloc : ∀ y ∈ W, D.IsLocalEquationAt y f := fun y hy =>
    CartierDivisor.isLocalEquationAt_iff.mpr ⟨W, hy, hW⟩
  obtain ⟨e₀, he₀, a, ha⟩ : ∃ e₀ : Y.functionFieldˣ, E.IsLocalEquationAt x₀ e₀ ∧
      ∃ a : Y.presheaf.stalk x₀, algebraMap (Y.presheaf.stalk x₀) Y.functionField a =
        (e₀ : Y.functionField) := by
    obtain ⟨e₀, he₀, ⟨a, ha⟩⟩ := CartierDivisor.isEffective_iff_exists.mp hE x₀
    exact ⟨e₀, he₀, a, ha⟩
  obtain ⟨W₀, hxW₀, hW₀⟩ := CartierDivisor.isLocalEquationAt_iff.mp he₀
  have hW₀loc : ∀ y ∈ W₀, E.IsLocalEquationAt y e₀ := fun y hy =>
    CartierDivisor.isLocalEquationAt_iff.mpr ⟨W₀, hy, hW₀⟩
  obtain ⟨W₁, hxW₁, s₀, hs₀⟩ := Y.presheaf.exists_germ_eq a
  choose W' hxW' s hs using fun k => Y.presheaf.exists_germ_eq
    (cartierLocalCoefficient D x₀ f hf (b k))
  set O : Y.Opens := W ⊓ W₀ ⊓ W₁ ⊓ ⨅ k, W' k with hO
  have hxO : x₀ ∈ O := ⟨⟨⟨hxW, hxW₀⟩, hxW₁⟩, by
    simp only [Opens.coe_iInf, Set.mem_iInter, SetLike.mem_coe]
    exact fun k => hxW' k⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxO O.isOpen
  have hVW : V ≤ W := fun y hy => (hVO hy).1.1.1
  have hVW₀ : V ≤ W₀ := fun y hy => (hVO hy).1.1.2
  have hVW₁ : V ≤ W₁ := fun y hy => (hVO hy).1.2
  have hVW' : ∀ k, V ≤ W' k := fun k y hy => by
    have h := (hVO hy).2
    simp only [Opens.coe_iInf, Set.mem_iInter, SetLike.mem_coe] at h
    exact h k
  refine ⟨V, hV, hxV, f, fun k => Y.presheaf.map (homOfLE (hVW' k)).op (s k), e₀,
    Y.presheaf.map (homOfLE hVW₁).op s₀, fun y hy => hWloc y (hVW hy),
    fun y hy => hW₀loc y (hVW₀ hy), fun _ => ⟨fun k => ?_, ?_⟩⟩
  · show Y.germToFunctionField V (Y.presheaf.map (homOfLE (hVW' k)).op (s k)) = _
    rw [← Y.algebraMap_germ_eq_germToFunctionField hxV, TopCat.Presheaf.germ_res_apply, hs k,
      cartierLocalCoefficient_image]
  · rw [← Y.algebraMap_germ_eq_germToFunctionField hxV, TopCat.Presheaf.germ_res_apply, hs₀, ha]

end Chart

section Realization

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- On an affine open where a Cartier divisor has a local equation f with regular f b_k and the
boundary of a klt pair has a regular local equation, the pairs (y, c) of a closed point and a
coefficient matrix at which the tuple Σ_k c_ik b_k realizes a nonnegative rational profile for the
pair are the zero set of an ideal of Γ(V)[c]. -/
theorem exists_ideal_realization_on_affine_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (D : CartierDivisor Y) {N m : ℕ}
    (b : Fin m → Γ(D.sheaf, ⊤)) (β : Fin N → ℚ) (hβ0 : ∀ i, 0 ≤ β i) (V : Y.Opens)
    (hV : IsAffineOpen V) [Nonempty V] (f : Y.functionFieldˣ) (r : Fin m → Γ(Y, V))
    (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b k))
    (e₀ : Y.functionFieldˣ) (h : Γ(Y, V))
    (he₀ : ∀ y ∈ V, (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt y e₀)
    (hh : Y.germToFunctionField V h = (e₀ : Y.functionField)) :
    ∃ I : Ideal (MvPolynomial (Fin N × Fin m) Γ(Y, V)),
      ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) → ∀ c : Fin N × Fin m → K,
        (IsRealizedProfile cY fY d D₀ D y (fun i => ∑ k, c (i, k) • b k)
            (fun i => (β i : ℝ)) ↔
          ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
            (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨M, ex, hM2, hex1, hexM⟩ := exists_common_exponents β hβ0
  let G : {i : Fin N // 0 < β i} → MvPolynomial (Fin N × Fin m) Γ(Y, V) := fun j =>
    ((∑ k, MvPolynomial.X (j.1, k) * MvPolynomial.C (r k)) ^ (ex j.1)) ^ d *
      MvPolynomial.C h ^ M
  obtain ⟨I, hI⟩ := smoothAffineLemmaThreeStatement_of_charZero K Y n cY V hV G (d * M)
    (by nlinarith)
  have hc : ∀ a : K, Y.germToFunctionField V (algebraMap K Γ(Y, V) a) =
      algebraMap K Y.functionField a := fun a => (sectionGermAlgHom (K := K) V).commutes a
  refine ⟨I, fun y hy hyc c => ?_⟩
  rw [isRealizedProfile_iff_modelThresholdBadAt cY fY d D₀ D y f (hloc y hy) b β hβ0 hex1 hexM c,
    modelThresholdBadAt_pair_iff cY fY hd D₀ hklt hE y V hy e₀ he₀]
  have hfun : (fun j : {i : Fin N // 0 < β i} =>
      ((∑ k, algebraMap K Y.functionField (c (j.1, k)) *
        ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1)) ^ d *
          (e₀ : Y.functionField) ^ M) =
      fun j => Y.germToFunctionField V
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j)) := by
    funext j
    simp only [G, map_pow, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, hc, hr, hh]
  rw [hfun]
  exact hI y hy hyc c

/-- On an affine open as above, the points at which some basis realizes a decreasing nonnegative
rational profile for the pair are the closed points of a closed set. -/
theorem exists_closed_realizedSet_on_affine_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (D : CartierDivisor Y) {N : ℕ}
    (hN : 0 < N) (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (β : Fin N → ℚ)
    (hβ0 : ∀ i, 0 ≤ β i) (hβanti : Antitone β) (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (f : Y.functionFieldˣ) (r : Fin N → Γ(Y, V)) (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b₀ k))
    (e₀ : Y.functionFieldˣ) (h : Γ(Y, V))
    (he₀ : ∀ y ∈ V, (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt y e₀)
    (hh : Y.germToFunctionField V h = (e₀ : Y.functionField)) :
    ∃ C : Set Y, IsClosed C ∧ ∀ y ∈ V, IsClosed ({y} : Set Y) →
      ((∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY fY d D₀ D y B (fun i => (β i : ℝ))) ↔ y ∈ C) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
  have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
    (Module.finrank_eq_card_basis b₀).symm
  obtain ⟨I, hreal⟩ := exists_ideal_realization_on_affine_pair cY fY hd D₀ hklt hE D b₀ β hβ0 V
    hV f r hloc hr e₀ h he₀ hh
  have hFT : Algebra.FiniteType K Γ(Y, V) := smooth_affineOpen_finiteType (n := n) hV
  -- the invariance under lower triangular changes
  have htup : ∀ (L c : Matrix (Fin N) (Fin N) K) (i : Fin N),
      ∑ l, L i l • ∑ k, c l k • b₀ k = ∑ k, (L * c) i k • b₀ k := by
    intro L c i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hinv : ∀ (ψ : Γ(Y, V) →ₐ[K] K) (c : Matrix (Fin N) (Fin N) K),
      (∀ g ∈ I, ψ (MvPolynomial.eval (fun ij => algebraMap K Γ(Y, V) (c ij.1 ij.2)) g) = 0) →
      c.det ≠ 0 → ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        ∀ g ∈ I, ψ (MvPolynomial.eval
          (fun ij => algebraMap K Γ(Y, V) ((L * c) ij.1 ij.2)) g) = 0 := by
    intro ψ c hψc _ L hL _
    obtain ⟨y, hy, hyc, hψ⟩ := exists_closedPoint_of_algHom hV ψ
    have h1 := (hreal y hy hyc (fun ij => c ij.1 ij.2)).mpr fun g hg => (hψ _).mp (hψc g hg)
    have hL' : ∀ i l, L i l ≠ 0 → (β i : ℝ) ≤ (β l : ℝ) := by
      intro i l hil
      have hli : l ≤ i := by
        by_contra hlt
        exact hil (hL (show OrderDual.toDual l < OrderDual.toDual i from not_le.mp hlt))
      exact_mod_cast hβanti hli
    have h2 := isRealizedProfile_triangular cY fY d D₀ D y _ _ L hL' h1
    have h3 : (fun i => ∑ l, L i l • ∑ k, (fun ij : Fin N × Fin N => c ij.1 ij.2) (l, k) • b₀ k) =
        fun i => ∑ k, (fun ij : Fin N × Fin N => (L * c) ij.1 ij.2) (i, k) • b₀ k :=
      funext fun i => htup L c i
    rw [h3] at h2
    intro g hg
    exact (hψ _).mpr ((hreal y hy hyc _).mp h2 g hg)
  obtain ⟨𝔟, h𝔟⟩ := exists_ideal_of_lowerTriangular_invariant I hinv
  refine ⟨Y.zeroLocus (U := V) (𝔟 : Set Γ(Y, V)), Y.zeroLocus_isClosed _, fun y hy hyc => ?_⟩
  have hmax : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  let ev : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have hev : ∀ a, ev a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := fun a =>
    closedPointEvaluation_eq_zero_iff (K := K) _ a
  have hzl : y ∈ Y.zeroLocus (U := V) (𝔟 : Set Γ(Y, V)) ↔ ∀ b ∈ 𝔟, ev b = 0 := by
    rw [Scheme.mem_zeroLocus_iff]
    refine forall₂_congr fun b _ => ?_
    rw [mem_basicOpen_iff_notMem_primeIdealOf hV y hy, not_not, hev]
  rw [hzl, ← h𝔟 ev]
  constructor
  · rintro ⟨B, hB⟩
    let c : Matrix (Fin N) (Fin N) K := Matrix.of fun i k => b₀.repr (B i) k
    have hBc : (fun i => ∑ k, (fun ij : Fin N × Fin N => c ij.1 ij.2) (i, k) • b₀ k) = ⇑B :=
      funext fun i => b₀.sum_repr (B i)
    refine ⟨c, ?_, fun g hg => (hev _).mpr ((hreal y hy hyc _).mp (by rw [hBc]; exact hB) g hg)⟩
    have hli : LinearIndependent K (fun i => ∑ k, c i k • b₀ k) := by
      have h := B.linearIndependent
      rw [← hBc] at h
      exact h
    exact (linearIndependent_sum_smul_iff_det_ne_zero b₀ c).mp hli
  · rintro ⟨c, hcdet, hcI⟩
    have hli := (linearIndependent_sum_smul_iff_det_ne_zero b₀ c).mpr hcdet
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hreal y hy hyc (fun ij => c ij.1 ij.2)).mpr fun g hg => (hev _).mp (hcI g hg)

/-- **The points at which some basis realizes a nonnegative rational profile for a klt pair with
effective boundary on a smooth variety are closed on closed points.** -/
theorem isClosedOnClosedPoints_realized_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (D : CartierDivisor Y) {N : ℕ}
    (hN : 0 < N) (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (β : Fin N → ℚ)
    (hβ0 : ∀ i, 0 ≤ β i) :
    IsClosedOnClosedPoints {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      IsRealizedProfile cY fY d D₀ D y B (fun i => (β i : ℝ))} := by
  classical
  set τ := Tuple.sort (fun i => -β i) with hτ
  have hanti : Antitone (β ∘ τ) := by
    intro a b hab
    have h := Tuple.monotone_sort (fun i => -β i) hab
    simp only [Function.comp_apply] at h ⊢
    linarith
  have hset : {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      IsRealizedProfile cY fY d D₀ D y B (fun i => (β i : ℝ))} =
      {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY fY d D₀ D y B (fun i => ((β ∘ τ) i : ℝ))} := by
    ext y
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B.reindex τ.symm, ?_⟩
      have h1 : ⇑(B.reindex τ.symm) = ⇑B ∘ τ := by
        funext i
        simp [Module.Basis.reindex_apply]
      rw [h1]
      exact (isRealizedProfile_comp_equiv cY fY d D₀ D y B (fun i => (β i : ℝ)) τ).mpr hB
    · rintro ⟨B, hB⟩
      refine ⟨B.reindex τ, ?_⟩
      have h1 : ⇑(B.reindex τ) = ⇑B ∘ τ.symm := by
        funext i
        simp [Module.Basis.reindex_apply]
      rw [h1]
      apply (isRealizedProfile_comp_equiv cY fY d D₀ D y (⇑B ∘ τ.symm) (fun i => (β i : ℝ))
        τ).mp
      have h2 : (⇑B ∘ τ.symm) ∘ τ = ⇑B := by
        funext i
        simp
      rw [h2]
      exact hB
  rw [hset]
  apply isClosedOnClosedPoints_of_local
  intro x _
  obtain ⟨V, hV, hxV, f, r, e₀, h, hloc, he₀, hr⟩ :=
    exists_affine_localEquation_regular_pair (pairBoundaryCartier cY fY d D₀) hE D x b₀
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨hr', hh⟩ := hr hne
  obtain ⟨C, hC, hrep⟩ := exists_closed_realizedSet_on_affine_pair cY fY hd D₀ hklt hE D hN b₀
    (β ∘ τ) (fun i => hβ0 _) hanti V hV f r hloc hr' e₀ h he₀ hh
  exact ⟨V, V.isOpen, hxV, C, hC, fun y hy hyc => hrep y hy hyc⟩

/-- **The zero profile is a normalized profile of a klt pair at every closed point** of a smooth
variety of dimension at least one, for every basis of the sections. -/
theorem zero_mem_sncWeightNormalizedProfiles_pair (hn : 1 ≤ n) (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N : ℕ}
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    (0 : Fin N → ℝ) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  classical
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) y hy
  obtain ⟨c, hyc⟩ : ∃ c : EtaleChart K Y n, y ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top y)
  set c' := etaleChartCentered c (rationalAffineGermPoint y hyc β) with hc'
  have hw : (fun _ : Fin n => 1) ≠ (0 : Fin n → ℕ) := fun h => by
    have h1 := congrFun h ⟨0, hn⟩
    simp at h1
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, he, hecU, hxe, hord,
    -⟩ := exists_toric_extraction_model c' y hyc (fun _ => 1) hw
      (fun a _ => etaleChartCentered_germ_not_isUnit c y hyc β a)
  set a₀ : Fin n := ⟨0, hn⟩
  have hw'1 : w' a₀ = 1 := Nat.dvd_one.mp ⟨g, (hgw a₀).trans (Nat.mul_comm _ _)⟩
  set u₀ : Y.functionFieldˣ := etaleChartCoordinateRationalUnit c' a₀ with hu₀
  set H : CartierDivisor Y := principalCartierDivisor Y u₀ with hH
  have hBne : ∀ i, B i ≠ 0 := B.ne_zero
  set G : Fin (N + 1) → CartierDivisor Y :=
    Fin.cons H fun i => cartierSectionZeroDivisor D (B i) (hBne i) with hG
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
    hGsupp⟩ := exists_proper_snc_model_with cY fY d D₀ G
  obtain ⟨w, hw0, hwΦ, hval, -⟩ := exists_sncWeight_data_of_test_prime π hπ cY
    fY d hd D₀ cX ξ hinj hξ hsnc hBsupp G hGsupp σ hσ cU ⟨e, he⟩ y hxe
  -- the value of the retraction on div u₀ is the order one of u₀ along e
  have hHe : cartierCoefficient (cartierPullback σ H) e = 1 := by
    have hloc := cartierPullback_isLocalEquationAt σ H e
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor (σ e) u₀)
    rw [cartierCoefficient_eq_ord hloc]
    have h1 := hord a₀
    rw [hw'1] at h1
    exact_mod_cast h1
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hno
    push Not at hno
    have h := hval 0
    have hG0 : G 0 = H := rfl
    rw [hG0, hHe] at h
    simp [hno] at h
  -- positivity of the log discrepancy of the weight (klt)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hApos : 0 < ∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / (d : ℝ)) := by
    have hpos : ∀ k, 0 < ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / (d : ℝ) := by
      intro k
      have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
      have h2 : ((cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX
          etaleCharts_cover) (ξ k) : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast h1
      exact div_pos (by linarith) hdR
    obtain ⟨k₀, hk₀⟩ := hwne
    have hk₀pos : 0 < w k₀ := lt_of_le_of_ne (hw0 k₀) (Ne.symm hk₀)
    calc (0 : ℝ) < w k₀ * (((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k₀)) / (d : ℝ)) :=
          mul_pos hk₀pos (hpos k₀)
      _ ≤ _ := Finset.single_le_sum (fun k _ => mul_nonneg (hw0 k) (hpos k).le)
          (Finset.mem_univ k₀)
  refine ⟨B, (∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / (d : ℝ)),
      fun i => ∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (hBne i))) (ξ k) : ℝ)),
    ⟨hBne, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, fun i => hGsupp i.succ, hw0, hwΦ, rfl, fun i => rfl⟩, hApos, fun i => ?_⟩
  rw [Pi.zero_apply, zero_mul]
  dsimp only
  refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) ?_
  exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
    (cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective D (B i) (hBne i)))
      (ξ k)

/-- **The normalized realization sets of every rational profile of a klt pair with effective
boundary on a smooth variety are closed on closed points**, in characteristic zero. -/
theorem isClosedOnClosedPoints_normalizedProfiles_pair (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (hE : (pairBoundaryCartier cY fY d D₀).IsEffective)
    (D : CartierDivisor Y) {N : ℕ} (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (α : Fin N → ℚ) :
    IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
      sncWeightNormalizedProfiles cY fY d D₀ D N y} := by
  classical
  set αp : Fin N → ℚ := fun i => max (α i) 0 with hαp
  have hset : {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} =
      {y : Y | (fun i => (αp i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [mem_sncWeightNormalizedProfiles_iff_max_zero]
    have h : (fun i => max ((α i : ℝ)) 0) = fun i => ((αp i : ℚ) : ℝ) := by
      funext i
      simp [hαp]
    rw [h]
  rw [hset]
  by_cases hpos : ∃ i, 0 < α i
  · obtain ⟨i₀, hi₀⟩ := hpos
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
    exact isClosedOnClosedPoints_normalizedProfiles_of_realized cY fY d hd D₀ hklt D
      (fun y hy => realizationSetsZariskiClosed_pair cY fY hd D₀ hklt hE y hy D) b₀
      (fun β hβ => isClosedOnClosedPoints_realized_pair cY fY hd D₀ hklt hE D hN b₀ β hβ)
      αp (fun i => le_max_right _ _) ⟨i₀, lt_max_of_lt_left hi₀⟩
  · push Not at hpos
    have hzero : αp = 0 := by
      funext i
      exact max_eq_right (hpos i)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hdim := etaleChart_topologicalKrullDim (K := K) cY
      have : Subsingleton Y := subsingleton_of_topologicalKrullDim_eq_zero (by simpa using hdim)
      exact isClosedOnClosedPoints_of_subsingleton _
    · refine ⟨Set.univ, isClosed_univ, fun y hy => ?_⟩
      simp only [Set.mem_univ, iff_true, Set.mem_ofPred_eq]
      have h0 : (fun i => ((αp i : ℚ) : ℝ)) = 0 := by
        funext i
        simp [hzero]
      rw [h0]
      exact zero_mem_sncWeightNormalizedProfiles_pair hn cY fY hd D₀ hklt D b₀ y hy

/-- **The closedness of the realization sets in the point**, in the form of the hypothesis of
K-NF, for a klt pair with effective boundary on a smooth variety in characteristic zero. -/
theorem closedPointRealization_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (A : CartierDivisor Y) :
    ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d
        D₀ (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y} := by
  refine Filter.Eventually.of_forall fun j α => ?_
  by_cases hfd : Module.Finite K Γ((j • A).sheaf, ⊤)
  · exact isClosedOnClosedPoints_normalizedProfiles_pair cY fY hd D₀ hklt hE (j • A)
      (Module.finBasis K Γ((j • A).sheaf, ⊤)) α
  · refine ⟨∅, isClosed_empty, fun y _ => ?_⟩
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
    rintro ⟨B, -⟩
    exact hfd (Module.Finite.of_basis B)

end Realization

end MixedFujita
