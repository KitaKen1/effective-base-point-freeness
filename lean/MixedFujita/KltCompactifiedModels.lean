/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompactifiedPrincipalizingModels
public import MixedFujita.KltCompactifiedVanishing
public import MixedFujita.KltConnectednessBoundary
public import MixedFujita.WeakModelThresholdBad

/-!
Compactified principalizing models for a pair on a normal affine variety, and the roundup H¹
vanishing on them (step 15, restriction to the fibres of a product).

* `HasKltSNCCompactification K n T d B G`: T is the complement of an effective nef and big divisor
  D̄ in a smooth projective T̄, G is the restriction of an effective Ḡ with c D̄ − Ḡ nef, and B is the
  restriction of a divisor B̄ with d K_{T̄} + B̄ principal, both supported on an SNC family. On such a
  model the roundup of the boundary dM H + M B + d G of the connectedness argument has vanishing
  H¹ for a principal H (`klt_roundup_H1_vanishing_of_kltCompactification`).
* For a weakly bad point x of a pair on X and a principalizing SNC model of the family, some member
  through the fibre over x is a bad member: M (d − b_s) ≤ d G_s
  (`exists_bad_snc_member_of_modelThresholdWeakBadAt`), as in the weak Lemma 3. Weak badness
  restricts to an open subscheme with the transported pair
  (`modelThresholdWeakBadAt_of_isOpenImmersion`).
* For a domain A of finite type, a pair (c_X, f_X, d, div u) on Spec A, an element t generating a
  prime ideal and a family g, the open part over Spec A of the sum-principalizing model of the
  projective closure (for the pair transported to the closure) is such a model, with B the crepant
  boundary of the pair (`exists_klt_compactified_principalizing_model`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Compactification

/-- `T` is the complement of an effective nef and big divisor `D̄` in a smooth projective `T̄`, and
`B`, `G` are the restrictions of divisors `B̄`, `Ḡ` supported on an SNC family, with `Ḡ` effective,
`c D̄ − Ḡ` nef and `d K_{T̄} + B̄` principal. -/
def HasKltSNCCompactification (K : Type u) [Field K] (n : ℕ) (T : Scheme.{u}) [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))] (d : ℕ) (Bc Gc : CartierDivisor T) : Prop :=
  ∃ (Tb : Scheme.{u}) (_ : IsIntegral Tb) (_ : IsNoetherian Tb)
    (_ : Tb.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K)))
    (_ : IsProper (Tb ↘ Spec (CommRingCat.of K)))
    (_ : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Tb)))
    (_ : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H)
    (cTb : EtaleChart K Tb n) (r : ℕ) (ξ : Fin r → Tb) (Bb Gb Db : CartierDivisor Tb) (c : ℕ)
    (Fb : Tb.functionFieldˣ) (ι : T ⟶ Tb) (_ : IsOpenImmersion ι) (_ : IsDominant ι),
    Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
    (∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ → cartierCoefficient Bb (t : Tb) = 0) ∧
    (∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ → cartierCoefficient Gb (t : Tb) = 0) ∧
    d • smoothCanonicalDivisor cTb + Bb = principalCartierDivisor Tb Fb ∧
    Db.IsEffective ∧ CartierIsNef K Db ∧ CartierIsBig K Db ∧ CartierIsNef K (c • Db - Gb) ∧
    (∀ x : Tb, x ∈ ι.opensRange ↔ Db.IsLocalEquationAt x 1) ∧
    cartierPullback ι Bb = Bc ∧ cartierPullback ι Gb = Gc

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

/-- **The roundup H¹ vanishing of the klt connectedness argument** on a model with a klt SNC
compactification, for a principal H = div v: H¹(T, 𝒪(C)) = 0 when C has the coefficients
⌈−(dM h + M b + d g)/(dM)⌉. -/
theorem klt_roundup_H1_vanishing_of_kltCompactification
    (hKV : KawamataViehwegVanishingSNCProjective K n) (hn : 1 ≤ n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) (Bc Gc : CartierDivisor T)
    (hcomp : HasKltSNCCompactification K n T d Bc Gc) (v : T.functionFieldˣ) (C : CartierDivisor T)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-(((((d * M : ℕ) : ℤ) * T.ord (v : T.functionField) (t : T) +
        ((M : ℤ) * cartierCoefficient Bc (t : T) + (d : ℤ) * cartierCoefficient Gc (t : T)) : ℤ) :
          ℝ) / ((d * M : ℕ) : ℝ))⌉) :
    Subsingleton (Scheme.Modules.Cohomology C.sheaf 1) := by
  obtain ⟨Tb, _, _, _, _, _, _, hProj, cTb, r, ξ, Bb, Gb, Db, c, Fb, ι, _, _, hinj, hξ, hsnc,
    hBsupp, hGsupp, hF, hDeff, hDnef, hDbig, hGnef, hV, hBc, hGc⟩ := hcomp
  subst hBc hGc
  exact klt_open_model_roundup_H1_vanishing K hKV hn hProj cTb ξ hinj hξ hsnc Bb Gb Db d M hd hM
    hBsupp hGsupp Fb hF hDeff hDnef hDbig c hGnef ι hV v C hC

end Compactification

section BadMember

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- **A weakly bad point gives a bad member of a principalizing model**: for a pair on X, a
principalizing SNC model ρ : T → X of the nonzero members of a family gX and a point x at which
the family has threshold at most 1/M in the weak model form, some member ξ_s of the family has
M (d − b_s) ≤ d G_s, with b the crepant boundary and G the principalized divisor, and its closure
meets the fibre over x. -/
theorem exists_bad_snc_member_of_modelThresholdWeakBadAt (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    {J : Type} [Finite J] (gX : J → X.functionField) [Nonempty {j : J // gX j ≠ 0}]
    (hA : ∀ k : {j : J // gX j ≠ 0},
      (principalCartierDivisor X (Units.mk0 (gX k.1) k.2)).IsEffective)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hGsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient Gc (t : T) = 0)
    (hGI : effectiveCartierIdealSheaf Gc hGc =
      (⨆ k : {j : J // gX j ≠ 0}, effectiveCartierIdealSheaf
        (principalCartierDivisor X (Units.mk0 (gX k.1) k.2)) (hA k)).comap ρ)
    (M : ℕ) (hM : 1 ≤ M) (x : X) (hbad : ModelThresholdWeakBadAt c f d D x gX M) :
    ∃ s, (M : ℤ) * ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s)) ≤
        (d : ℤ) * cartierCoefficient Gc (ξ s) ∧
      x ∈ ρ '' closure ({ξ s} : Set T) := by
  classical
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hineq⟩ := hbad
  set logX : ℤ := cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU
    etaleCharts_cover) (e : U) with hlogX
  set crep : Fin r → ℤ := fun s =>
    cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s)
    with hcrep
  set G : Fin r → ℤ := fun s => cartierCoefficient Gc (ξ s) with hG
  obtain ⟨o, t₀, ht₀, ho, hosupp, -, ⟨-, j₀, hj₀⟩, hdisc, hzero⟩ :=
    exists_snc_orders_at_test_prime_sharp ρ hρ c f d D cT ξ hinj hξ hsnc hsupport
      (fun k : {j : J // gX j ≠ 0} => principalCartierDivisor X (Units.mk0 (gX k.1) k.2)) hA Gc
      hGc hGsupp hGI σ hσ cU e
  -- the orders of the members of the family along e
  have hord : ∀ k : {j : J // gX j ≠ 0}, cartierCoefficient (cartierPullback σ
      (principalCartierDivisor X (Units.mk0 (gX k.1) k.2))) (e : U) =
        U.ord ((dominantFunctionFieldMap σ).hom (gX k.1)) (e : U) := by
    intro k
    rw [cartierPullback_principal, cartierCoefficient_principal]
    rfl
  -- the weighted inequality
  have hb := hineq j₀.1 j₀.2
  rw [← hord j₀, ← hj₀] at hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbZ : (M : ℤ) * ((d : ℤ) + logX) ≤ (d : ℤ) * ∑ s, G s * o s := by
    have hb' : (M : ℝ) * (((d : ℝ) + (logX : ℝ)) / d) ≤ ((∑ s, G s * o s : ℤ) : ℝ) := hb
    have h1 : (M : ℝ) * (((d : ℝ) + (logX : ℝ)) / d) * d =
        (M : ℝ) * ((d : ℝ) + (logX : ℝ)) := by
      field_simp
    have h2 : (M : ℝ) * ((d : ℝ) + (logX : ℝ)) ≤ (d : ℝ) * ((∑ s, G s * o s : ℤ) : ℝ) := by
      rw [← h1]
      nlinarith
    exact_mod_cast h2
  have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
  by_cases hall : ∀ s, o s = 0
  · -- no member through the centre: A ≥ 1 against M A ≤ 0
    exfalso
    have hlog0 := hzero hall
    have hG0 : ∑ s, G s * o s = 0 := Finset.sum_eq_zero fun s _ => by rw [hall s, mul_zero]
    rw [hG0, mul_zero] at hbZ
    have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith
  push Not at hall
  obtain ⟨s₀, hs₀⟩ := hall
  have hsum : (M : ℤ) * ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s ≤
      ∑ s, ((d : ℤ) * G s) * o s := by
    have h1 : ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s =
        (d : ℤ) * ∑ s, o s - ∑ s, crep s * o s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h2 : ∑ s, ((d : ℤ) * G s) * o s = (d : ℤ) * ∑ s, G s * o s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [h1, h2]
    have hM0 : (0 : ℤ) ≤ M := by positivity
    exact (mul_le_mul_of_nonneg_left hdisc hM0).trans hbZ
  obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge_of_exists_pos ho hsum
    ⟨s₀, lt_of_le_of_ne (ho s₀) (Ne.symm hs₀)⟩
  refine ⟨s, by linarith [hs], ?_⟩
  -- the point lies in the image of the closure of the member
  rw [← ht₀] at hxe
  exact closure_minimal
    (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem ρ (hosupp s hos.ne')))
    ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure) hxe

end BadMember

section Model

variable {K : Type u} [Field K] [CharZero K]

attribute [local instance] specAlgebraOver

set_option maxHeartbeats 3200000 in
/-- **Compactified principalizing models for a pair on a normal affine variety.** For a domain A
of finite type over a field of characteristic zero, a pair (c_X, f_X, d, div u) on Spec A, a
nonzero t ∈ A and a family g with a nonzero member, the open part over Spec A of the
sum-principalizing model of the projective closure, for the pair transported to the closure, is a
principalizing SNC model of div t and the g_j whose SNC family supports the crepant boundary,
with a klt SNC compactification. -/
theorem exists_klt_compactified_principalizing_model (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (N : ℕ) (hN : 1 ≤ N)
    (cX : EtaleChart K (Spec (CommRingCat.of A)) N)
    (fX uX : (Spec (CommRingCat.of A)).functionFieldˣ) (d : ℕ) (t : A) (ht : t ≠ 0)
    {J : Type} [Finite J] (g : J → A) (hg : ∃ j, g j ≠ 0) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension N (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ Spec (CommRingCat.of A)) (_ : IsDominant ρ)
      (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T N) (r : ℕ) (ξ : Fin r → T)
      (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K N ξ ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d
          (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover)
          (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit t ht))) (z : T) = 0) ∧
      (∀ (j : {j : J // g j ≠ 0}) (z : CodimensionOnePoint T), (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2))) (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Gc (z : T) = 0) ∧
      effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
        effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2))
          (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ ∧
      (∀ t' : T,
        (∀ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t' ≤ cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t') ∧
        ∃ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t' = cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t') ∧
      HasKltSNCCompactification K N T d (crepantBoundaryCartier ρ hρ cX fX d
          (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover) Gc := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨k₀, hgk₀⟩ := hg
  haveI : Nonempty {j : J // g j ≠ 0} := ⟨⟨k₀, hgk₀⟩⟩
  -- generators of `A` through `t` and the nonzero `g_j`, and the projective closure
  obtain ⟨r, π, idx, hπ, hidx⟩ := exists_surjective_mvPolynomial_with_values (K := K)
    (fun o : Option {j : J // g j ≠ 0} => o.elim t (fun j => g j.1))
  have hiH : π (MvPolynomial.X (idx none)) ≠ 0 := by rw [hidx]; exact ht
  have hig : ∀ j : {j : J // g j ≠ 0}, π (MvPolynomial.X (idx (some j))) ≠ 0 := fun j => by
    rw [hidx]; exact j.2
  haveI := affineClosure_toImage_isOpenImmersion π hπ
  haveI := affineClosureToImage_isOver π
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (affineClosureToImage π)) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion _
  let cb : EtaleChart K (affineClosure π) N :=
    etaleChartImageOfOpenImmersion (affineClosureToImage π) cX
  -- the pair on the closure
  obtain ⟨fb, hfb⟩ := exists_units_map_eq_of_bijective
    (dominantFunctionFieldMap (affineClosureToImage π)).hom hj
    (fX * (isUnit_chartRelativeJacobianDet_of_bijective (affineClosureToImage π) hj cb cX).unit⁻¹)
  have hfb1 : crepantPullbackFormUnit (affineClosureToImage π) hj cb fb cX = fX := by
    rw [crepantPullbackFormUnit, hfb, inv_mul_cancel_right]
  obtain ⟨wb, hwb⟩ := exists_units_map_eq_of_bijective
    (dominantFunctionFieldMap (affineClosureToImage π)).hom hj uX
  let Db := principalCartierDivisor (affineClosure π) wb
  have hDb : cartierPullback (affineClosureToImage π) Db =
      principalCartierDivisor (Spec (CommRingCat.of A)) uX := by
    rw [cartierPullback_principal, hwb]
  -- the hyperplane sections
  let Hb := affineClosureHyperplane π (idx none) hiH
  let Ab : {j : J // g j ≠ 0} → CartierDivisor (affineClosure π) :=
    fun j => affineClosureHyperplane π (idx (some j)) (hig j)
  have hAb : ∀ j, (Ab j).IsEffective := fun j => affineClosureHyperplane_isEffective π _ (hig j)
  -- the sum-principalizing model of the closure
  obtain ⟨Tb, hTbi, hTbo, hTbN, hTbs, ρb, hdom, hover, hprop, -, hρb, cTb, rb, ξb, hinjb, hcohb,
      hsncb, hcrepb, hGb, hAsupp, hemb, -, -, Gb, hGbeff, hGbI, hGb0, -, hnefb⟩ :=
    exists_projective_snc_model_principalizing_sum (K := K) (n := N) cb fb d Db
      (fun _ : Unit => Hb) Ab hAb (Empty.elim : Empty → (affineClosure π).IdealSheafData)
      (fun e => e.elim)
  -- its open part over `Spec A`
  let U := affineClosureChartPart π
  haveI := affineClosureChartPart_nonempty π
  have hηU : ρb (genericPoint Tb) ∈ U := by
    rw [dominant_map_genericPoint]
    exact genericPoint_mem U
  let V : Tb.Opens := ρb ⁻¹ᵁ U
  haveI : Nonempty V := ⟨⟨genericPoint Tb, hηU⟩⟩
  letI instTo : V.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨V.ι ≫ (Tb ↘ Spec (CommRingCat.of K))⟩
  haveI : V.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  haveI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI hTs : SmoothOfRelativeDimension N (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + N) (V.ι ≫ (Tb ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  haveI hTN : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (V : Set Tb)) }
  haveI := affineClosureChartLift_isIso π hπ
  let ρ : V.toScheme ⟶ Spec (CommRingCat.of A) := (ρb ∣_ U) ≫ inv (affineClosureChartLift π)
  have hcomm : ρ ≫ affineClosureToImage π = V.ι ≫ ρb := by
    simp only [ρ, Category.assoc]
    rw [← affineClosureChartLift_fac π, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  haveI : IsDominant (ρ ≫ affineClosureToImage π) := by rw [hcomm]; infer_instance
  haveI hρdom : IsDominant ρ := IsDominant.of_comp_of_isOpenImmersion ρ (affineClosureToImage π)
  haveI hρover : ρ.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    rw [← HomIsOver.comp_over (f := affineClosureToImage π) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := ρb) (S := Spec (CommRingCat.of K))]
    rfl
  haveI hρprop : IsProper ρ := by
    have : IsProper (ρb ∣_ U) := IsZariskiLocalAtTarget.restrict hprop U
    infer_instance
  have hιb : Function.Bijective (dominantFunctionFieldAlgHom (K := K) V.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι
  have hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ) := by
    have h1 : Function.Bijective
        (dominantFunctionFieldAlgHom (K := K) (ρ ≫ affineClosureToImage π)) := by
      rw [dominantFunctionFieldAlgHom_congr_hom hcomm]
      exact dominantFunctionFieldAlgHom_comp_bijective ρb V.ι hρb hιb
    rw [dominantFunctionFieldAlgHom_comp] at h1
    exact (Function.Bijective.of_comp_iff _ hj).mp h1
  obtain ⟨cT⟩ := exists_etaleChart_on_integral_open_immersion V.ι cTb
  have : Smooth (V.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth N _
  have hnormT : ∀ z : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk z) :=
    fun z => smooth_stalk_isIntegrallyClosed (K := K) z
  -- the restricted SNC family
  obtain ⟨r', ξ, hinj, hcoh, hsnc, -, hξall⟩ :=
    exists_isSNCFamily_of_isOpenImmersion V.ι ξb hinjb hcohb hsncb
  have hout : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      V.ι (z : V.toScheme) ∉ Set.range ξb := fun z hz h => hz (hξall _ h)
  let zb : CodimensionOnePoint V.toScheme → CodimensionOnePoint Tb := fun z =>
    ⟨V.ι (z : V.toScheme), (coheight_eq_of_isOpenImmersion V.ι (z : V.toScheme)).trans z.2⟩
  have hcoef : ∀ (B : CartierDivisor Tb) (z : CodimensionOnePoint V.toScheme),
      cartierCoefficient (cartierPullback V.ι B) (z : V.toScheme) =
        cartierCoefficient B (V.ι (z : V.toScheme)) := fun B z =>
    cartierCoefficient_cartierPullback_of_isOpenImmersion (K := K) (n := N) V.ι B z
  have hpull : ∀ B : CartierDivisor (affineClosure π),
      cartierPullback ρ (cartierPullback (affineClosureToImage π) B) =
        cartierPullback V.ι (cartierPullback ρb B) := by
    intro B
    rw [← cartierPullback_comp, ← cartierPullback_comp]
    exact cartierPullback_congr_hom hcomm B
  -- the crepant boundary
  have h1 : crepantBoundaryCartier ρ hρ cX fX d
      (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover =
      crepantBoundaryCartier (V.ι ≫ ρb) (dominantFunctionFieldAlgHom_comp_bijective ρb V.ι hρb hιb)
        cb fb d Db cT etaleCharts_cover := by
    rw [← hDb, ← hfb1, ← crepantBoundaryCartier_comp (affineClosureToImage π) ρ hj hρ cb fb d Db cX
      cT etaleCharts_cover]
    exact crepantBoundaryCartier_congr_hom hcomm _ _ cb fb d Db cT etaleCharts_cover
  have hcrepc : ∀ z : CodimensionOnePoint V.toScheme,
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d
        (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover)
          (z : V.toScheme) =
        cartierCoefficient (crepantBoundaryCartier ρb hρb cb fb d Db cTb etaleCharts_cover)
          (V.ι (z : V.toScheme)) := by
    intro z
    rw [h1, crepantBoundaryCartier_coefficient_comp_of_stalkMap_bijective ρb V.ι hρb hιb _ cb fb d
      Db cTb cT z ((coheight_eq_of_isOpenImmersion V.ι (z : V.toScheme)).trans z.2)
      (ConcreteCategory.bijective_of_isIso _)]
  have hcrep : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d
        (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover)
          (z : V.toScheme) = 0 := by
    intro z hz
    rw [hcrepc z]
    exact hcrepb (zb z) (hout z hz)
  -- the hyperplane and the functions
  have hHeq : principalCartierDivisor (Spec (CommRingCat.of A)) (specFunctionRationalUnit t ht) =
      cartierPullback (affineClosureToImage π) Hb := by
    rw [cartierPullback_affineClosureHyperplane]
    congr 1
    exact specFunctionRationalUnit_congr (hidx none).symm _ _
  have hH : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit t ht))) (z : V.toScheme) = 0 := by
    intro z hz
    rw [hHeq, hpull, hcoef]
    exact hGb () (zb z) (hout z hz)
  have hgeq : ∀ j : {j : J // g j ≠ 0}, principalCartierDivisor (Spec (CommRingCat.of A))
      (specFunctionRationalUnit (g j.1) j.2) = cartierPullback (affineClosureToImage π) (Ab j) := by
    intro j
    rw [cartierPullback_affineClosureHyperplane]
    congr 1
    exact specFunctionRationalUnit_congr (hidx (some j)).symm _ _
  have hgsupp : ∀ (j : {j : J // g j ≠ 0}) (z : CodimensionOnePoint V.toScheme),
      (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (g j.1) j.2))) (z : V.toScheme) = 0 := by
    intro j z hz
    rw [hgeq, hpull, hcoef]
    exact hAsupp j (zb z) (hout z hz)
  -- the principalized divisor
  let Gc := cartierPullback V.ι Gb
  have hGc : Gc.IsEffective := cartierPullback_isEffective V.ι Gb hGbeff
  have hGc0 : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient Gc (z : V.toScheme) = 0 := fun z hz => by
    rw [hcoef]
    exact hGb0 (zb z) (hout z hz)
  have hGcI : effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
      effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (g j.1) j.2))
        (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ := by
    rw [effectiveCartierIdealSheaf_cartierPullback V.ι Gb hGbeff, hGbI,
      ← Scheme.IdealSheafData.comap_comp, ← hcomm, Scheme.IdealSheafData.comap_comp,
      (Scheme.IdealSheafData.map_gc (affineClosureToImage π)).l_iSup]
    congr 1
    apply iSup_congr
    intro j
    rw [← effectiveCartierIdealSheaf_cartierPullback (affineClosureToImage π) (Ab j) (hAb j)]
    exact effectiveCartierIdealSheaf_congr (hgeq j).symm _ _
  have hmin := fun t' => cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
    ρ (fun j : {j : J // g j ≠ 0} => principalCartierDivisor (Spec (CommRingCat.of A))
      (specFunctionRationalUnit (g j.1) j.2)) (fun j => specFunctionRationalUnit_effective (g j.1) j.2)
    Gc hGc hGcI t'
  -- the compactification
  have hcomp : HasKltSNCCompactification K N V.toScheme d (crepantBoundaryCartier ρ hρ cX fX d
      (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover) Gc := by
    have hTbprop : IsProper (Tb ↘ Spec (CommRingCat.of K)) := by
      rw [← HomIsOver.comp_over (f := ρb) (S := Spec (CommRingCat.of K))]
      infer_instance
    have hdiag := isAffineHom_diagonal_terminal_of_isSeparated (K := K) Tb
    have hDteff : (cartierPullback ρb (affineClosureInfinity π)).IsEffective :=
      cartierPullback_isEffective ρb _ (affineClosureInfinity_isEffective π)
    have hDtnef : CartierIsNef K (cartierPullback ρb (affineClosureInfinity π)) :=
      cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul ρb _ 1 le_rfl
        (by rw [one_nsmul]; exact affineClosureInfinity_globallyGenerated π)
    have hdimTb : topologicalKrullDim Tb = (N : ℕ) := etaleChart_topologicalKrullDim cTb
    have hdimXb : topologicalKrullDim (affineClosure π) = (N : ℕ) :=
      affineClosure_topologicalKrullDim π hπ cX
    obtain ⟨M, e', he', hcompe⟩ := hemb (r + 1) (affineClosureι π) inferInstance rfl
    haveI := he'
    obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart M K (e' (genericPoint Tb))
    have hProj : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H :=
      ⟨_, projectiveHyperplaneCartier_isAmpleProj e' (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) hi hcompe⟩
    have hDtbig : CartierIsBig K (cartierPullback ρb (affineClosureInfinity π)) :=
      cartierIsBig_cartierPullback_of_finiteDimensional ρb (hdimTb.trans hdimXb.symm)
        (fun m => cartier_finiteDimensional_sections_of_projective_all_dimensions hdimTb hProj _)
        (affineClosureInfinity_isBig π hπ cX hN)
    have hGnef : CartierIsNef K (1 • cartierPullback ρb (affineClosureInfinity π) - Gb) := by
      rw [one_nsmul]
      exact (hnefb (affineClosureInfinity π)
        (fun k => cartierIsGloballyGenerated_affineClosureInfinity_sub_hyperplane π _ (hig k))).2
    -- the crepant boundary of the compactification
    let Bb := crepantBoundaryCartier ρb hρb cb fb d Db cTb etaleCharts_cover
    have hrec := crepantBoundaryCartier_smooth_recombine ρb hρb cb fb d Db cTb
    let Fb : Tb.functionFieldˣ := Units.map (dominantFunctionFieldMap ρb).hom.toMonoidHom wb *
      (crepantPullbackFormUnit ρb hρb cb fb cTb ^ d)⁻¹
    have hF : d • smoothCanonicalDivisor cTb + Bb = principalCartierDivisor Tb Fb := by
      have hpr : cartierPullback ρb Db =
          principalCartierDivisor Tb (Units.map (dominantFunctionFieldMap ρb).hom.toMonoidHom wb) :=
        cartierPullback_principal ρb wb
      rw [hpr] at hrec
      simp only [Fb]
      rw [principalCartierDivisor_mul, principalCartierDivisor_inv, principalCartierDivisor_power,
        ← hrec]
      simp only [smul_add]
      abel
    have hBc : cartierPullback V.ι Bb = crepantBoundaryCartier ρ hρ cX fX d
        (principalCartierDivisor (Spec (CommRingCat.of A)) uX) cT etaleCharts_cover := by
      apply cartierDivisor_eq_of_forall_coefficient_eq hnormT
      intro z
      rw [hcoef, hcrepc z]
    refine ⟨Tb, hTbi, hTbN, hTbo, hTbs, hTbprop, hdiag, hProj, cTb, rb, ξb, Bb, Gb,
      cartierPullback ρb (affineClosureInfinity π), 1, Fb, V.ι, inferInstance, inferInstance,
      hinjb, hcohb, hsncb, hcrepb, hGb0, hF, hDteff, hDtnef, hDtbig, hGnef, ?_, hBc, rfl⟩
    intro x
    rw [Scheme.Opens.opensRange_ι,
      cartierPullback_isLocalEquationAt_one_iff ρb (affineClosureInfinity_isEffective π),
      affineClosureInfinity_isLocalEquationAt_one_iff]
    rfl
  exact ⟨V.toScheme, inferInstance, instTo, hTN, hTs, ρ, hρdom, hρover, hρprop, hρ, cT, r', ξ,
    Gc, hGc, hinj, hcoh, hsnc, hcrep, hH, hgsupp, hGc0, hGcI, hmin, hcomp⟩

end Model

end MixedFujita
