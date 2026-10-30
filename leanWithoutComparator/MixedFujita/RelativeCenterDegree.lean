/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightCenterDegree
public import MixedFujita.GradedPullbackTaylor
public import MixedFujita.RelativeWeightProfiles
public import MixedFujita.SteinCartierSections

/-!
The inequalities of one degree of section 5.3 over a fibre (step 17R-2).

Let f : X → Y be a contraction, J the hyperplane class of the base Y in projective space, (X, B) a
klt pair and π : T → X a proper simple normal crossing model; ρ = π ≫ f. For a weight w on T
minimizing the objective over the fibre of y, with a general closed point z of its centre and
tangent coordinates from the coordinate ratios of the base:

* the Taylor expansions at z of the pullbacks along π of the sections of f*E are, up to one unit
  power series, those of the pullbacks along ρ of the sections of E, so the initial exponents of
  the two spaces agree (`initialMonomialFinset_cartierPullbackTaylorLinear_pullback_eq`); the
  multiples j f*J and f*(j J) are equal divisors;
* (21) holds with the infima over the fibre: the scaled weight tests the infimum at the image under
  π of a point of the centre over the fibre (`rel_sncWeightInfimum_mul_sum_initialExponents_le`);
* (16) is the absolute bound at π(z) and (20) the absolute bound for ρ, so the inequalities
  `CenterDegreeInequalities` hold for the normalized infima over the fibre
  (`rel_projectiveHyperplane_centerDegreeInequalities`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Identification

variable {K : Type u} [Field K] {n : ℕ} {X Y T : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]

/-- The Taylor map at z of the pullbacks along π of the sections of f*E is a unit multiple of the
Taylor map of the pullbacks along π ≫ f of the sections of E. -/
theorem cartierPullbackTaylorLinear_pullback_eq_unit_mul (π : T ⟶ X)
    [π.IsOver (Spec (CommRingCat.of K))] (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of K))] (E : CartierDivisor Y) (z : T)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk z))
      (T.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    ∃ u : MvPowerSeries (Fin n) K, IsUnit u ∧ ∀ t : Γ(E.sheaf, ⊤),
      cartierPullbackTaylorLinear (cartierPullback f E) π z ez
          (cartierDominantPullbackSection f E t) =
        u * cartierPullbackTaylorLinear E (π ≫ f) z ez t := by
  obtain ⟨f₂, hf₂⟩ := E.exists_isLocalEquationAt (f (π z))
  have hf₁ := cartierPullback_isLocalEquationAt f E (π z) hf₂
  obtain ⟨v₁, hv₁⟩ := cartierStalkPullbackCoefficient_change_frame (cartierPullback f E) π z
    (Classical.choose ((cartierPullback f E).exists_isLocalEquationAt (π z))) _
    (Classical.choose_spec ((cartierPullback f E).exists_isLocalEquationAt (π z))) hf₁
  obtain ⟨v₂, hv₂⟩ := cartierStalkPullbackCoefficient_change_frame E (π ≫ f) z
    (Classical.choose (E.exists_isLocalEquationAt ((π ≫ f) z))) f₂
    (Classical.choose_spec (E.exists_isLocalEquationAt ((π ≫ f) z))) hf₂
  refine ⟨stalkTaylorExpansion z ez ((v₁ * v₂⁻¹ : (T.presheaf.stalk z)ˣ) : T.presheaf.stalk z),
    (v₁ * v₂⁻¹).isUnit.map (stalkTaylorExpansion z ez), fun t => ?_⟩
  have hcomp : cartierStalkPullbackCoefficient (cartierPullback f E) π z _ hf₁
      (cartierDominantPullbackSection f E t) =
      cartierStalkPullbackCoefficient E (π ≫ f) z f₂ hf₂ t := by
    rw [cartierStalkPullbackCoefficient_apply, cartierDominantPullbackSection_localCoefficient]
    simp only [cartierStalkPullbackCoefficient_apply, Scheme.Hom.stalkMap_comp,
      CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have h2 : cartierStalkPullbackCoefficient E (π ≫ f) z f₂ hf₂ t =
      ((v₂⁻¹ : (T.presheaf.stalk z)ˣ) : T.presheaf.stalk z) *
        cartierStalkPullbackCoefficient E (π ≫ f) z
          (Classical.choose (E.exists_isLocalEquationAt ((π ≫ f) z)))
          (Classical.choose_spec (E.exists_isLocalEquationAt ((π ≫ f) z))) t := by
    rw [hv₂ t, ← mul_assoc, Units.inv_mul, one_mul]
  change stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient (cartierPullback f E) π z
      (Classical.choose ((cartierPullback f E).exists_isLocalEquationAt (π z)))
      (Classical.choose_spec ((cartierPullback f E).exists_isLocalEquationAt (π z)))
      (cartierDominantPullbackSection f E t)) =
    stalkTaylorExpansion z ez ((v₁ * v₂⁻¹ : (T.presheaf.stalk z)ˣ) : T.presheaf.stalk z) *
      stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient E (π ≫ f) z
        (Classical.choose (E.exists_isLocalEquationAt ((π ≫ f) z)))
        (Classical.choose_spec (E.exists_isLocalEquationAt ((π ≫ f) z))) t)
  rw [hv₁, hcomp, h2, ← map_mul, ← mul_assoc, Units.val_mul]

/-- The initial exponents at z of the sections of f*E pulled back along π are those of the
sections of E pulled back along π ≫ f (f with surjective maps of sections). -/
theorem initialMonomialFinset_cartierPullbackTaylorLinear_pullback_eq (π : T ⟶ X)
    [π.IsOver (Spec (CommRingCat.of K))] (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) (m : MonomialOrder (Fin n))
    (E : CartierDivisor Y) [FiniteDimensional K Γ(E.sheaf, ⊤)]
    [FiniteDimensional K Γ((cartierPullback f E).sheaf, ⊤)] (z : T)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk z))
      (T.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    initialMonomialFinset m
        (LinearMap.range (cartierPullbackTaylorLinear (cartierPullback f E) π z ez)) =
      initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear E (π ≫ f) z ez)) := by
  obtain ⟨u, hu, huT⟩ := cartierPullbackTaylorLinear_pullback_eq_unit_mul π f E z ez
  refine initialMonomialFinset_eq_of_unit_mul m _ _ hu fun φ => ?_
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := cartierDominantPullbackSection_surjective_of_open_app_surjective f happ E s
    exact ⟨_, ⟨t, rfl⟩, huT t⟩
  · rintro ⟨ψ, ⟨t, rfl⟩, rfl⟩
    exact ⟨cartierDominantPullbackSection f E t, huT t⟩

/-- The initial exponents of the pullbacks of the sections of equal divisors agree. -/
theorem initialMonomialFinset_cartierPullbackTaylorLinear_congr {D D' : CartierDivisor X}
    (h : D = D') (π : T ⟶ X) [π.IsOver (Spec (CommRingCat.of K))] (m : MonomialOrder (Fin n))
    [FiniteDimensional K Γ(D.sheaf, ⊤)] [FiniteDimensional K Γ(D'.sheaf, ⊤)] (z : T)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk z))
      (T.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear D π z ez)) =
      initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)) := by
  subst h
  rfl

end Identification

section Comparison

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y T : Scheme.{u}} [IsIntegral X]
  [IsIntegral T] [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- The comparison (21) over a fibre for a weight minimizing the objective over the fibre of y,
whose centre has a point q over the fibre: inf_y(D') · Q ≤ inf_y(D) · Q' for the infima over the
fibre. -/
theorem rel_sncWeightInfimum_mul_sum_initialExponents_le {r N N' : ℕ} (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X) (cT : EtaleChart K T n)
    (ξ : Fin r → T) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (t : T) = 0)
    (c : EtaleChart K T n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (η : T) (hη : η ∈ c.U) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set T))
    (f : X ⟶ Y) (y : Y) (q : T) (hηq : η ⤳ q) (hq : f (π q) = y) (z : T) (hz : z ∈ c.U)
    (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk z))
      (T.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor X) [FiniteDimensional K Γ(D.sheaf, ⊤)]
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (t : T) = 0)
    (D' : CartierDivisor X) [FiniteDimensional K Γ(D'.sheaf, ⊤)]
    (hN' : Module.finrank K Γ(D'.sheaf, ⊤) = N')
    (v : Fin n → ℕ) (m : MonomialOrder (Fin n)) {lam t j t' j' : ℝ} (hlam : 0 < lam)
    (hj : 0 < j) (ht' : 0 < t') (hj' : 0 < j')
    (hmin : (∑ i, Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j)) ≤
      relWeightInfimum cX fX d D₀ D f y N t j) :
    relWeightInfimum cX fX d D₀ D' f y N' t' j' *
        ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
            (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear D π z ez)),
          Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)) / t -
            realExponentWeight (sncChartCoordinateWeights σc w) p / j) ≤
      relWeightInfimum cX fX d D₀ D f y N t j *
        ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
            (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)),
          Real.exp (lam * (∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)) / t' -
            lam * realExponentWeight (sncChartCoordinateWeights σc w) p / j') := by
  have hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a := by
    intro k hk
    cases hσ : σc k with
    | none =>
      exfalso
      have hmem : η ∈ closure ({ξ k} : Set T) ∩ c.U := ⟨hwη k hk, hη⟩
      rw [hc.2 k, hσ] at hmem
      exact hmem
    | some a => exact ⟨a, rfl⟩
  have h1 := sum_initialExponents_le_sncWeight_objective π ξ hinj hξ hsnc c σc hc z hz ez hez D B
    hGsupp w hw0 hwσ v m (∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)) t hj
  -- the infimum over the fibre at degree D' is at most the infimum at π(q)
  have hx : π η ⤳ π q := hηq.map π.continuous
  have h3 := sncWeightInfimum_le_sum_initialExponents π hπ cX fX d hd D₀ cT ξ hinj hξ hsnc hBsupp
    c σc hc η hη w hw0 hwne hwη (π q) hx z hz hηz ez hez D' hN' v m hlam ht' hj'
  have hne : (sncWeightObjectiveValues cX fX d D₀ D' (π q) N' t' j').Nonempty :=
    ⟨_, sncWeightObjectiveValues_natCast_mem cX fX d D₀ D' (π q)
      (Module.finBasisOfFinrankEq K Γ(D'.sheaf, ⊤) hN') t' j'⟩
  have h4 := relWeightInfimum_le_sncWeightInfimum cX fX d D₀ D' f hq N' t' j' hne
  rw [mul_comm (relWeightInfimum cX fX d D₀ D f y N t j)]
  exact mul_le_mul (h4.trans h3) (h1.trans hmin)
    (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)
    (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)

end Comparison

section Inequalities

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {X Y T : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T] [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T] [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The inequalities of one degree over a fibre, for a weight minimizing the objective over the
fibre of y at a general closed point of its centre, for the pullback of the hyperplane class. -/
theorem rel_projectiveHyperplane_centerDegreeInequalities
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    [∀ j : ℕ, FiniteDimensional K
      Γ((j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)]
    (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)}) {rr dd d : ℕ}
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (hdd : 1 ≤ dd) (D₀ : CartierDivisor X)
    (cT : EtaleChart K T n) (ξ : Fin rr → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (t : T) = 0)
    (c : EtaleChart K T n) (σc : Fin rr → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin rr → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0) (η : T) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set T))
    (hmax : ∀ η' : T, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set T)) → η' ⤳ η → η' = η)
    (y : Y) (q : T) (hηq : η ⤳ q) (hq : f (π q) = y) (z : T) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (hzU : (π ≫ f) z ∈ projectivePullbackCoordinateOpen e k.val)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk z))
      (T.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (hiff : ∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0)
    (Tan : Finset (Fin n)) (hTan : Tan.card = d + 1) (hTanfree : ∀ b ∈ Tan, ∀ k, σc k ≠ some b)
    (hTanU : ∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k.val} =>
        projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j)), ∃ κ : K,
      etaleChartStalkCoords c z hz (MvPolynomial.X b) =
        (π ≫ f).stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k.val)
          ((π ≫ f) z) hzU (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k.val) κ)))
    (hsat : ∀ (h' : Y.presheaf.stalk ((π ≫ f) η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ Tan →
      etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b ((π ≫ f).stalkMap η h') ∈
          IsLocalRing.maximalIdeal (T.presheaf.stalk η))
    (m₀ : MonomialOrder (Fin n)) (s : ℕ) (hs : 1 ≤ s) {D' : ℕ}
    (hD' : topologicalKrullDim (closure ({(π ≫ f) η} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι ((π ≫ f) η) ≫ e)
      (genericPoint (pointClosureScheme ((π ≫ f) η)))).asHomogeneousIdeal)
    (hdeg : ∀ r : ℕ, Filter.Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier (pointClosureι ((π ≫ f) η) ≫ e) g hg hgW).sheaf,
          ⊤) : ℝ) / (D : ℝ) ^ D') Filter.atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (l m : ℕ) (hl : 0 < l)
    (hM : l * (2 * s ^ D' + 2 ^ D' * D'.factorial + (d + 1) + s ^ (d + 1)) ≤ m)
    (B : Module.Basis (Fin (Module.finrank K
      Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤))) K
      Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
        (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) (B i) (B.ne_zero i)))
        (t : T) = 0)
    (hNm : 0 < Module.finrank K
      Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤))
    {t : ℝ} (ht : 0 < t) (a : ℝ)
    (ha : a ≤ ∑ k, w k * (((dd : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k)) / dd))
    (hmin : (∑ i, Real.exp ((∑ k, w k * (((dd : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k)) / dd)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) (B i)
            (B.ne_zero i))) (ξ k) : ℝ)) / (m : ℝ))) ≤
      relWeightInfimum cX fX dd D₀ (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen))
        f y (Module.finrank K
          Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)) t m)
    (hspec : (∑ i, Real.exp ((∑ k, w k * (((dd : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k)) / dd)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) (B i)
            (B.ne_zero i))) (ξ k) : ℝ)) / (m : ℝ))) ≤
      sncWeightInfimum cX fX dd D₀ (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen))
        (π z) (Module.finrank K
          Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)) t m) :
    CenterDegreeInequalities
      (fun j => Module.finrank K
        Γ((j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤))
      (fun j => relWeightInfimum cX fX dd D₀
        (j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) f y
        (Module.finrank K
          Γ((j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)) t j /
          Module.finrank K
            Γ((j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤))
      t s ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * (d + 1 : ℕ)) a l m (d + 1)
      (fun j => ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) (fun i => if i ∈ Tan then 1 else 0)
          (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m))
      (sectionExponentialMoment (initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) (fun i => if i ∈ Tan then 1 else 0)
          (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)))
        (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
        (fun p => (natExponentDegree (fun i => if i ∈ Tan then 1 else 0) p : ℝ)) m)
      (∑ k, w k * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k)) / dd)) := by
  -- notation
  obtain ⟨v, hvdef⟩ : ∃ v : Fin n → ℕ, v = fun i => if i ∈ Tan then 1 else 0 := ⟨_, rfl⟩
  rw [← hvdef]
  have hv : ∀ k a, σc k = some a → v a = 0 := by
    intro k' a hka
    rw [hvdef]
    exact ite_eq_right fun ha => hTanfree a ha k' hka
  have hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a := fun k' hk' => (hiff k').mpr hk'
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := lt_of_lt_of_le (Nat.mul_pos hl (by positivity)) hM
    exact_mod_cast this
  have hlm : l ≤ m := le_trans (Nat.le_mul_of_pos_right l (by positivity)) hM
  -- the initial exponents of the graded Taylor maps along π ≫ f and along π
  have hIMF : ∀ j : ℕ, initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierGradedPullbackTaylor (π ≫ f)
        (projectiveHyperplaneCartier e g hg hggen) z
        (projectiveHyperplaneUnit e g hg hggen k)
        (projectiveHyperplane_isLocalEquationAt e g hg hggen k ((π ≫ f) z) hzU) ez j)) =
      initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (j • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)) := by
    intro j
    have hfd : FiniteDimensional K
        Γ((cartierPullback f (j • projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤) := by
      rw [cartierPullback_nsmul]
      infer_instance
    rw [← initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded (π ≫ f) _
      (projectiveHyperplaneCartier e g hg hggen) z _
      (projectiveHyperplane_isLocalEquationAt e g hg hggen k ((π ≫ f) z) hzU) ez j,
      ← initialMonomialFinset_cartierPullbackTaylorLinear_pullback_eq π f happ _
        (j • projectiveHyperplaneCartier e g hg hggen) z ez]
    exact initialMonomialFinset_cartierPullbackTaylorLinear_congr
      (cartierPullback_nsmul f (projectiveHyperplaneCartier e g hg hggen) j) π _ z ez
  -- the sum Q_m is positive
  have hcard : (initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez))).card =
      Module.finrank K
        Γ((m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤) := by
    rw [initialMonomialFinset_card,
      LinearMap.finrank_range_of_inj (cartierPullbackTaylorLinear_injective π z ez _)]
  have hQm : 0 < ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)),
      Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
    refine Finset.sum_pos (fun p _ => Real.exp_pos _) ?_
    rw [← Finset.card_pos, hcard]
    exact hNm
  -- the tangential degree
  have hnat : ∀ p : Fin n →₀ ℕ, (natExponentDegree v p : ℝ) = ∑ i ∈ Tan, (p i : ℝ) := by
    intro p
    change ((∑ i, v i * p i : ℕ) : ℝ) = _
    rw [hvdef]
    push_cast
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsumv : (∑ a, (v a : ℝ)) = ((d + 1 : ℕ) : ℝ) := by
    rw [hvdef]
    have h1 : (Finset.univ.filter fun i : Fin n => i ∈ Tan) = Tan := by
      ext i
      simp
    push_cast
    rw [Finset.sum_boole, h1, hTan]
    push_cast
    ring
  refine ⟨ha, fun j => Finset.sum_nonneg fun p _ => (Real.exp_pos _).le, hQm, ?_, ?_, ?_⟩
  · -- (16)
    have h16 := sncWeight_tangential_moment_le_of_le_infimum π hπ cX fX dd hdd D₀ cT ξ hinj hξ
      hsnc hBsupp c σc hc z hz ez hez
      (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) hNm B hGsupp
      w hw0 hwne hwσ v 0 hv (fun _ _ _ => rfl) m₀ ht hmpos hspec
    rw [hsumv] at h16
    exact h16
  · -- (20)
    have h20 := projectiveHyperplane_sncWeight_partition_bound_of_degree (π ≫ f) e g hg hggen he
      k ξ c σc hc w hw0 η hη hwη hmax z hz hηz hzU ez hez hiff Tan hTan hTanfree hTanU hsat m₀ v
      s hs hD' hgW hdeg l m hl hM (m : ℝ) (by rw [hIMF]; exact hQm)
    simp only [hIMF] at h20
    have hT : sectionExponentialMoment (initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear
          (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)))
        (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
        (fun p => (natExponentDegree v p : ℝ)) m =
      (∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) *
          ∑ i ∈ Tan, (p i : ℝ)) /
        ((m : ℝ) * ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) π z ez)),
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m)) := by
      unfold sectionExponentialMoment sectionExponentialWeightSum
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      show (natExponentDegree v p : ℝ) *
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) = _
      rw [hnat p, mul_comm]
    rw [hT]
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [← hcast] at h20
    exact h20
  · -- (21)
    intro i hi
    rw [Finset.mem_Ico] at hi
    set jj := auxiliaryDegree m i l with hjj
    have hjpos : 0 < jj := by
      rw [hjj, auxiliaryDegree]
      exact Nat.div_pos (le_trans hlm (Nat.le_mul_of_pos_right m hi.1)) hl
    have hjreal : (0 : ℝ) < jj := by exact_mod_cast hjpos
    have h21 := rel_sncWeightInfimum_mul_sum_initialExponents_le π hπ cX fX dd hdd D₀ cT ξ hinj hξ
      hsnc hBsupp c σc hc η hη w hw0 hwne hwη f y q hηq hq z hz hηz ez hez
      (m • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) B hGsupp
      (jj • cartierPullback f (projectiveHyperplaneCartier e g hg hggen)) rfl v m₀
      (lam := (jj : ℝ) / m) (t := t) (j := (m : ℝ)) (t' := t) (j' := (jj : ℝ))
      (div_pos hjreal hmpos) hmpos ht hjreal hmin
    -- factor the exponentials
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ k, w k * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k)) / dd) := ⟨_, rfl⟩
    rw [← hA] at h21 ⊢
    have hsum1 : ∀ S : Finset (Fin n →₀ ℕ), (∑ p ∈ S, Real.exp (A / t -
        realExponentWeight (sncChartCoordinateWeights σc w) p / m)) =
        Real.exp (A / t) * ∑ p ∈ S,
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
      intro S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
    have hsum2 : ∀ S : Finset (Fin n →₀ ℕ), (∑ p ∈ S, Real.exp ((jj : ℝ) / m * A / t -
        (jj : ℝ) / m * realExponentWeight (sncChartCoordinateWeights σc w) p / jj)) =
        Real.exp ((jj : ℝ) / m * A / t) * ∑ p ∈ S,
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
      intro S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [hsum1, hsum2] at h21
    have hexp : Real.exp ((1 - (jj : ℝ) / m) * A / t) =
        Real.exp (A / t) / Real.exp ((jj : ℝ) / m * A / t) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp]
    refine ratio_bound_of_mul_le (Nat.cast_nonneg _) (by exact_mod_cast hNm)
      (relWeightInfimum_nonneg _ _ _ _ _ _ _ _ _ _)
      (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le) hQm (Real.exp_pos _) (Real.exp_pos _) ?_
    exact h21

end Inequalities

end MixedFujita
