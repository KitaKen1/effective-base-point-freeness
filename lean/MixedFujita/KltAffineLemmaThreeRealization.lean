/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalKltRealizationClosedness
public import MixedFujita.SmoothPairRealizationClosedness
public import MixedFujita.LemmaThreeSlices
public import MixedFujita.EffectiveCartierSupportedUnion
public import MixedFujita.ProperBirationalSections
public import MixedFujita.EtaleChartDimension

/-!
Lemma 3 in the model form on the affine opens of a normal variety for a klt pair with effective
boundary, and the closedness inputs of K-NF from it (step 15).

`KltAffineLemmaThreeStatement` is the klt version of the statement proved for smooth varieties and
the zero boundary in check 559: on an affine open V of a normal variety whose codimension-one points
lie in étale charts, for a klt pair (c_Y, f_Y, d, D₀) with effective boundary and a polynomial
family G with coefficients in Γ(V), the pairs (y, c) of a closed point and a parameter at which
G(c) has threshold at most 1/M are the zero set of an ideal of Γ(V)[c]. From it, the arguments of
checks 305 and 560–561 give both closedness inputs of K-NF for the pair, now without absorbing the
boundary into the family:

* at a closed point, as the slice y = x (`idealThresholdZariskiClosed_of_kltAffineLemmaThree`,
  `realizationSetsZariskiClosed_of_kltAffineLemmaThree`);
* in the point, through the flag closedness under lower triangular changes
  (`exists_closed_realizedSet_on_affine_klt`, `isClosedOnClosedPoints_realized_klt`) and the
  normalized profiles (`isClosedOnClosedPoints_normalizedProfiles_klt`,
  `closedPointRealization_klt`).

The zero profile is realized at every closed point x, including the singular ones
(`zero_mem_sncWeightNormalizedProfiles_klt`): a projective simple normal crossing model that also
principalizes the ideal of x carries an effective divisor whose support is the fibre over x, so a
member of the family with positive coefficient in it lies over x, and its log discrepancy is
positive because the pair is klt. Hence the closedness for normal klt pairs, K-NF and F2 follow
from the klt Lemma 3 (`normalKltRealizationClosedness_of_kltAffineLemmaThree`,
`kawamataNumericalFreeness_of_kltAffineLemmaThree`,
`linearEffectiveFreeness_of_kltAffineLemmaThree_of_basePointFree_of_ambro`).
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

section Statement

/-- **Lemma 3 in the model form on the affine opens of a normal variety, for a klt pair with
effective boundary**: on an affine open V of a normal separated variety of finite type whose
codimension-one points lie in étale charts, for a klt pair with effective boundary and a
polynomial family with coefficients in Γ(V), the pairs of a closed point and a parameter at which
the family has threshold at most 1/M are the zero set of an ideal of Γ(V)[c]. -/
def KltAffineLemmaThreeStatement (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ), 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ D₀ : CartierDivisor Y, LogPairBoundaryEffective cY fY d D₀ → LogPairIsKlt cY fY d D₀ →
    ∀ (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] {ι J : Type} [Finite ι] [Finite J]
      (G : J → MvPolynomial ι Γ(Y, V)) (M : ℕ), 1 ≤ M →
      ∃ I : Ideal (MvPolynomial ι Γ(Y, V)), ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
        ∀ c : ι → K,
          (ModelThresholdBadAt cY fY d D₀ y (fun j => Y.germToFunctionField V
            (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j))) M ↔
            ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
              (hV.primeIdealOf ⟨y, hy⟩).asIdeal)

end Statement

section ClosedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- **Lemma 3 at a closed point for a klt pair with effective boundary**, for polynomial families
with coefficients in the local ring, as the slice y = x of the klt Lemma 3 on affine opens. -/
theorem idealThresholdZariskiClosed_of_kltAffineLemmaThree (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (x : Y) (hx : IsClosed ({x} : Set Y)) :
    IdealThresholdZariskiClosed cY fY d D₀ x := by
  classical
  intro ι J _ _ G M hM
  obtain ⟨V, hV, hxV, s, hs⟩ := exists_affine_sections_of_germs x
    (fun k : (Σ j : J, (G j).support) => (G k.1).coeff k.2)
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  let G' : J → MvPolynomial ι Γ(Y, V) := fun j =>
    ∑ m ∈ (G j).support.attach, MvPolynomial.monomial m.1 (s ⟨j, m⟩)
  have hmap : ∀ j, MvPolynomial.map (Y.presheaf.germ V x hxV).hom (G' j) = G j := by
    intro j
    simp only [G', map_sum, MvPolynomial.map_monomial]
    conv_rhs => rw [(G j).as_sum]
    rw [← Finset.sum_attach (G j).support]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hs ⟨j, m⟩]
  obtain ⟨I', hI'⟩ := hL3 Y n hn hnorm hcov cY fY d hd D₀ heff hklt V hV G' M (by omega)
  have hFT : Algebra.FiniteType K Γ(Y, V) := sectionsBaseOpen_finiteType hV
  have hmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  let ev : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hev : ∀ a, ev a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := fun a =>
    closedPointEvaluation_eq_zero_iff (K := K) _ a
  have hcomp : ∀ (c : ι → K) (g : MvPolynomial ι Γ(Y, V)),
      ev (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g) =
        MvPolynomial.eval c (MvPolynomial.map ev.toRingHom g) := by
    intro c g
    rw [MvPolynomial.eval_map]
    have h : ev.toRingHom.comp (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i))) =
        MvPolynomial.eval₂Hom ev.toRingHom c := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        simp
    exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* K => φ g) h
  have hgerm : ∀ (c : ι → K) (j : J),
      Y.germToFunctionField V (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G' j)) =
        algebraMap (Y.presheaf.stalk x) Y.functionField
          (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j)) := by
    intro c j
    rw [← Y.algebraMap_germ_eq_germToFunctionField hxV]
    congr 1
    rw [← hmap j, MvPolynomial.eval_map]
    have h : (Y.presheaf.germ V x hxV).hom.comp
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i))) =
        MvPolynomial.eval₂Hom (Y.presheaf.germ V x hxV).hom
          (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        have h1 := (sectionStalkAlgHom (K := K) V x hxV).commutes (c i)
        rw [sectionStalkAlgHom_apply] at h1
        simpa using h1
    exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* Y.presheaf.stalk x => φ (G' j)) h
  refine ⟨Ideal.map (MvPolynomial.map ev.toRingHom) I', ?_⟩
  ext c
  have hiff := hI' x hxV hx c
  simp only [hgerm] at hiff
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, hval⟩
    have hbad := hiff.mp ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx', hA,
      fun j hj => hval j (fun h0 => hj (by simp only [h0, map_zero]))⟩
    have hle : Ideal.map (MvPolynomial.map ev.toRingHom) I' ≤
        RingHom.ker (MvPolynomial.eval c) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomp]
      exact (hev _).mpr (hbad g hg)
    intro p hp
    exact hle hp
  · intro hc
    have h2 : ∀ g ∈ I', MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := fun g hg =>
      (hev _).mp (by rw [hcomp]; exact hc _ (Ideal.mem_map_of_mem _ hg))
    obtain ⟨U, h1, h2', h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, hval⟩ := hiff.mpr h2
    exact ⟨U, h1, h2', h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, fun j hj =>
      hval j ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hj)⟩

/-- **The realization sets in the tuple at a closed point are Zariski closed** for a klt pair with
effective boundary, from the klt Lemma 3 on affine opens. -/
theorem realizationSetsZariskiClosed_of_kltAffineLemmaThree (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (x : Y) (hx : IsClosed ({x} : Set Y))
    (D : CartierDivisor Y) : RealizationSetsZariskiClosed cY fY d D₀ D x :=
  realizationSetsZariskiClosed_of_idealThreshold cY fY d D₀ x
    (idealThresholdZariskiClosed_of_kltAffineLemmaThree hL3 hn hnorm hcov cY fY hd D₀ heff hklt x
      hx) D

end ClosedPoint

section Realization

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- On an affine open where a Cartier divisor has a local equation f with regular f b_k, the pairs
(y, c) of a closed point and a coefficient matrix at which the tuple Σ_k c_ik b_k realizes a
nonnegative rational profile for a klt pair with effective boundary are the zero set of an ideal of
Γ(V)[c]. -/
theorem exists_ideal_realization_on_affine_klt (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N m : ℕ}
    (b : Fin m → Γ(D.sheaf, ⊤)) (β : Fin N → ℚ) (hβ0 : ∀ i, 0 ≤ β i) (V : Y.Opens)
    (hV : IsAffineOpen V) [Nonempty V] (f : Y.functionFieldˣ) (r : Fin m → Γ(Y, V))
    (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b k)) :
    ∃ I : Ideal (MvPolynomial (Fin N × Fin m) Γ(Y, V)),
      ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) → ∀ c : Fin N × Fin m → K,
        (IsRealizedProfile cY fY d D₀ D y (fun i => ∑ k, c (i, k) • b k)
            (fun i => (β i : ℝ)) ↔
          ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
            (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨M, ex, hM2, hex1, hexM⟩ := exists_common_exponents β hβ0
  let G : {i : Fin N // 0 < β i} → MvPolynomial (Fin N × Fin m) Γ(Y, V) := fun j =>
    (∑ k, MvPolynomial.X (j.1, k) * MvPolynomial.C (r k)) ^ (ex j.1)
  obtain ⟨I, hI⟩ := hL3 Y n hn hnorm hcov cY fY d hd D₀ heff hklt V hV G M (by omega)
  have hc : ∀ a : K, Y.germToFunctionField V (algebraMap K Γ(Y, V) a) =
      algebraMap K Y.functionField a := fun a => (sectionGermAlgHom (K := K) V).commutes a
  refine ⟨I, fun y hy hyc c => ?_⟩
  rw [isRealizedProfile_iff_modelThresholdBadAt cY fY d D₀ D y f (hloc y hy) b β hβ0 hex1 hexM c]
  have hfun : (fun j : {i : Fin N // 0 < β i} =>
      (∑ k, algebraMap K Y.functionField (c (j.1, k)) *
        ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1)) =
      fun j => Y.germToFunctionField V
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j)) := by
    funext j
    simp only [G, map_pow, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, hc, hr]
  rw [hfun]
  exact hI y hy hyc c

/-- On an affine open as above, the points at which some basis realizes a decreasing nonnegative
rational profile for a klt pair with effective boundary are the closed points of a closed set. -/
theorem exists_closed_realizedSet_on_affine_klt (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N : ℕ}
    (hN : 0 < N) (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (β : Fin N → ℚ)
    (hβ0 : ∀ i, 0 ≤ β i) (hβanti : Antitone β) (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (f : Y.functionFieldˣ) (r : Fin N → Γ(Y, V)) (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b₀ k)) :
    ∃ C : Set Y, IsClosed C ∧ ∀ y ∈ V, IsClosed ({y} : Set Y) →
      ((∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY fY d D₀ D y B (fun i => (β i : ℝ))) ↔ y ∈ C) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
  have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
    (Module.finrank_eq_card_basis b₀).symm
  obtain ⟨I, hreal⟩ := exists_ideal_realization_on_affine_klt hL3 hn hnorm hcov cY fY hd D₀ heff
    hklt D b₀ β hβ0 V hV f r hloc hr
  have hFT : Algebra.FiniteType K Γ(Y, V) := sectionsBaseOpen_finiteType hV
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
effective boundary on a normal variety are closed on closed points**, from the klt Lemma 3. -/
theorem isClosedOnClosedPoints_realized_klt (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N : ℕ}
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
  obtain ⟨V, hV, hxV, f, r, e₀, h, hloc, -, hr⟩ :=
    exists_affine_localEquation_regular_pair (0 : CartierDivisor Y) CartierDivisor.isEffective_zero
      D x b₀
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨hr', -⟩ := hr hne
  obtain ⟨C, hC, hrep⟩ := exists_closed_realizedSet_on_affine_klt hL3 hn hnorm hcov cY fY hd D₀
    heff hklt D hN b₀ (β ∘ τ) (fun i => hβ0 _) hanti V hV f r hloc hr'
  exact ⟨V, V.isOpen, hxV, C, hC, fun y hy hyc => hrep y hy hyc⟩

omit [IsAlgClosed K] [IsLocallyNoetherian Y] in
/-- **The zero profile is a normalized profile of a klt pair at every closed point**, singular or
not, of a variety of dimension at least one, for every basis of the sections: a projective simple
normal crossing model principalizing the ideal of the point has a member of the family over the
point, whose log discrepancy is positive. -/
theorem zero_mem_sncWeightNormalizedProfiles_klt (hn : 1 ≤ n) (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N : ℕ}
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    (0 : Fin N → ℝ) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  classical
  have hBne : ∀ i, B i ≠ 0 := B.ne_zero
  -- the closed point is not the generic point
  have hgen : genericPoint Y ≠ y := by
    intro hgy
    have huniv : (Set.univ : Set Y) = {y} := by
      have h1 : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
      rw [← h1, hgy, hy.closure_eq]
    have : Subsingleton Y := ⟨fun a b => by
      have ha : a ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology Y
    rw [etaleChart_topologicalKrullDim (K := K) cY] at h0
    have h00 : (n : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h0
    have : n ≤ 0 := by exact_mod_cast h00
    omega
  -- the ideal sheaf of the point
  let Z : Closeds Y := ⟨{y}, hy⟩
  let 𝔟 : Unit → Y.IdealSheafData := fun _ => Scheme.IdealSheafData.vanishingIdeal Z
  have h𝔟 : ∀ j, genericPoint Y ∉ ((𝔟 j).support : Set Y) := by
    intro j hmem
    have hmem' : genericPoint Y ∈ (Z : Set Y) := by
      rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal Z]
      exact hmem
    exact hgen hmem'
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, hGsupp, -, -, h𝔟T, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n) cY fY d D₀
      (fun i => cartierSectionZeroDivisor D (B i) (hBne i))
      (fun _ : Unit => (0 : CartierDivisor Y)) (fun _ => CartierDivisor.isEffective_zero) 𝔟 h𝔟
  obtain ⟨-, -, E, hE, hEI, hEsupp⟩ := h𝔟T ()
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n) t
  -- the support of the principalized point is the fibre over the point
  have hsupE : (ρ ⁻¹' ({y} : Set Y) : Set T) =
      ⋃ k ∈ {k | 0 < cartierCoefficient E (ξ k)}, closure ({ξ k} : Set T) := by
    rw [← effectiveCartier_support_eq_positive_member_union hnormT E hE ξ hEsupp, hEI,
      Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant ρ y
  have htmem : t ∈ (ρ ⁻¹' ({y} : Set Y) : Set T) := ht
  rw [hsupE] at htmem
  obtain ⟨k, hk, -⟩ := Set.mem_iUnion₂.mp htmem
  have hξk : ρ (ξ k) = y := by
    have hmem : ξ k ∈ (⋃ k ∈ {k | 0 < cartierCoefficient E (ξ k)},
        closure ({ξ k} : Set T)) :=
      Set.mem_iUnion₂.mpr ⟨k, hk, subset_closure (Set.mem_singleton _)⟩
    rw [← hsupE] at hmem
    exact hmem
  -- the weight one on that member
  let w : Fin r → ℝ := fun k' => if k' = k then 1 else 0
  have hw0 : ∀ k', 0 ≤ w k' := fun k' => by
    simp only [w]
    split_ifs <;> norm_num
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbk : ((cartierCoefficient (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover)
      (ξ k) : ℤ) : ℝ) < d := by
    exact_mod_cast logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ cY fY d D₀ hklt cT
      ⟨ξ k, hcoh k⟩
  have hsum1 : ∑ k', w k' * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ k')) / (d : ℝ)) =
      ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ k)) / (d : ℝ) := by
    simp [w]
  refine ⟨B, (∑ k', w k' * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ k')) / (d : ℝ)),
      fun i => ∑ k', w k' * (cartierCoefficient (cartierPullback ρ
          (cartierSectionZeroDivisor D (B i) (hBne i))) (ξ k') : ℝ)),
    ⟨hBne, T, hTi, inferInstance, hTo, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, w, hinj, hcoh,
      hsnc, hsupp, fun i => hGsupp i, hw0, ⟨ξ k, hξk, fun k' hk' => ?_⟩, rfl, fun i => rfl⟩,
    ?_, fun i => ?_⟩
  · have hkk : k' = k := by
      by_contra hne
      exact hk' (by simp [w, hne])
    rw [hkk]
    exact subset_closure (Set.mem_singleton _)
  · rw [hsum1]
    exact div_pos (by linarith) hdR
  · rw [Pi.zero_apply, zero_mul]
    dsimp only
    refine Finset.sum_nonneg fun k' _ => mul_nonneg (hw0 k') ?_
    exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_isEffective ρ _ (cartierSectionZeroDivisor_isEffective D (B i) (hBne i)))
        (ξ k')

/-- **The normalized realization sets of every rational profile of a klt pair with effective
boundary on a normal variety are closed on closed points**, from the klt Lemma 3. -/
theorem isClosedOnClosedPoints_normalizedProfiles_klt (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y) {N : ℕ}
    (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (α : Fin N → ℚ) :
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
      (fun y hy => realizationSetsZariskiClosed_of_kltAffineLemmaThree hL3 hn hnorm hcov cY fY hd
        D₀ heff hklt y hy D) b₀
      (fun β hβ => isClosedOnClosedPoints_realized_klt hL3 hn hnorm hcov cY fY hd D₀ heff hklt D
        hN b₀ β hβ)
      αp (fun i => le_max_right _ _) ⟨i₀, lt_max_of_lt_left hi₀⟩
  · push Not at hpos
    have hzero : αp = 0 := by
      funext i
      exact max_eq_right (hpos i)
    refine ⟨Set.univ, isClosed_univ, fun y hy => ?_⟩
    simp only [Set.mem_univ, iff_true, Set.mem_ofPred_eq]
    have h0 : (fun i => ((αp i : ℚ) : ℝ)) = 0 := by
      funext i
      simp [hzero]
    rw [h0]
    exact zero_mem_sncWeightNormalizedProfiles_klt hn cY fY hd D₀ hklt D b₀ y hy

/-- **The closedness of the realization sets in the point**, in the form of the hypothesis of
K-NF, for a klt pair with effective boundary on a normal variety, from the klt Lemma 3. -/
theorem closedPointRealization_klt (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hcov : CodimOneChartCovered n K Y) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀)
    (hklt : LogPairIsKlt cY fY d D₀) (A : CartierDivisor Y) :
    ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d
        D₀ (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y} := by
  refine Filter.Eventually.of_forall fun j α => ?_
  by_cases hfd : Module.Finite K Γ((j • A).sheaf, ⊤)
  · exact isClosedOnClosedPoints_normalizedProfiles_klt hL3 hn hnorm hcov cY fY hd D₀ heff hklt
      (j • A) (Module.finBasis K Γ((j • A).sheaf, ⊤)) α
  · refine ⟨∅, isClosed_empty, fun y _ => ?_⟩
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
    rintro ⟨B, -⟩
    exact hfd (Module.Finite.of_basis B)

end Realization

/-- **The closedness for normal klt pairs with effective boundary from the klt Lemma 3** on affine
opens. -/
theorem normalKltRealizationClosedness_of_kltAffineLemmaThree
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], KltAffineLemmaThreeStatement K) :
    NormalKltRealizationClosedness.{u} := by
  intro K _ _ _ _ Y _ _ _ _ n _ hn hnorm hcov cY fY d hd D₀ A heff hklt hA x hx
  obtain ⟨m, hm, v, e, hcl, he, -⟩ := id hA
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  exact ⟨Filter.Eventually.of_forall fun j =>
      realizationSetsZariskiClosed_of_kltAffineLemmaThree (hL3 K) hn hnorm hcov cY fY hd D₀ heff
        hklt x hx (j • A),
    closedPointRealization_klt (hL3 K) hn hnorm hcov cY fY hd D₀ heff hklt A⟩

/-- **K-NF from the klt Lemma 3 on affine opens** (Kawamata–Viehweg vanishing is proved). -/
theorem kawamataNumericalFreeness_of_kltAffineLemmaThree
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], KltAffineLemmaThreeStatement K) :
    KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_normalKltRealizationClosedness
    (normalKltRealizationClosedness_of_kltAffineLemmaThree hL3)

/-- **F2 from the klt Lemma 3 on affine opens, the base point free theorem for klt pairs and
Ambro's canonical bundle formula for contractions to lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_kltAffineLemmaThree_of_basePointFree_of_ambro
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], KltAffineLemmaThreeStatement K)
    (hbpf : KltBasePointFreeStatement.{u}) (hamb : AmbroStrictDimensionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_normalKltRealizationClosedness_of_basePointFree_of_ambro
    (normalKltRealizationClosedness_of_kltAffineLemmaThree hL3) hbpf hamb

end MixedFujita
