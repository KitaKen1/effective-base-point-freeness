/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModuliChangedFibrationModel
public import MixedFujita.ComparisonImagePushbackRecovery
public import MixedFujita.RelativeAdjointAllDimensionSectionBounds
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-! Retain the entire original-input discriminant/moduli model, its actual
nonzero image ideal and all earlier isomorphisms and higher-model witnesses.
Construct a principalizing base blow-up sequence for the same ideal and the
actual compatible changed Stein fibration, higher crepant roundup and genuine
pushforward comparison over the original smooth base. Base-pullback comparison
and semipositivity remain separate obligations. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

universe u

/-- On an integral scheme over a field, the actual smooth relative dimension
is the ordinary geometric dimension. No dimension witness is supplied. -/
theorem geometricDimension_eq_of_smooth_relativeDimension
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of K)) {k : ℕ} [SmoothOfRelativeDimension k f] :
    topologicalKrullDim Y = k := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth k f
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set Y).Nonempty from Set.univ_nonempty) isOpen_univ.isLocallyClosed
  have hstalk := ((TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    f k).mp inferInstance).2 x hx
  exact (TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    f hx).symm.trans hstalk

variable {K : Type u} [Field K] [CharZero K] {n k : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [IsIntegral Y] [IsNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- The same original-input model internally supplies an actual principalized
changed Stein fibration and the higher roundup direct-image comparison. -/
theorem exists_compatible_snc_moduli_models_with_uniform_actual_section_bounds
    (hProjY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)
    (cY : EtaleChart K Y k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d D) (hklt : LogPairIsKlt c f d D)
    (H : CartierDivisor Y) (s : ℕ) (ψ : X.functionFieldˣ)
    (hD : D = s • cartierPullback g H + principalCartierDivisor X ψ) :
    ∃ (W : Y.Opens), genericPoint Y ∈ W ∧ ∃ S : Scheme.BlowUpSequence Y,
      ∃ (_ : IsIntegral S.last) (_ : S.last.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian S.last)
        (_ : SmoothOfRelativeDimension k (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant S.composite) (_ : S.composite.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper S.composite) (_ : IsProjective S.composite)
        (_ : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)))
        (_ : QuasiCompact (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsSeparated (S.last ↘ Spec (CommRingCat.of K)))
        (cB : EtaleChart K S.last k)
        (hnormB : ∀ b : S.last, IsIntegrallyClosed (S.last.presheaf.stalk b)),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) S.composite) ∧
        IsIso (S.composite ∣_ W) ∧ ∃ (rB : ℕ) (ξB : Fin rB → S.last),
          Function.Injective ξB ∧ (∀ i, Order.coheight (ξB i) = 1) ∧ IsSNCFamily K k ξB ∧
          (∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB →
            S.composite (β : S.last) ∈ W) ∧
          ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : IsNoetherian T)
            (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (π : T ⟶ X) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K)))
            (_ : IsProper π) (_ : IsProjective π)
            (_ : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)))
            (_ : QuasiCompact (T ↘ Spec (CommRingCat.of K)))
            (_ : IsSeparated (T ↘ Spec (CommRingCat.of K)))
            (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
            (cT : EtaleChart K T n)
            (hkltT : LogPairIsKlt cT (crepantPullbackFormUnit π hπ c f cT) d (cartierPullback π D))
            (rT : ℕ) (ξT : Fin rT → T),
            Function.Injective ξT ∧ (∀ i, Order.coheight (ξT i) = 1) ∧ IsSNCFamily K n ξT ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
                (t : T) = 0) ∧
            (∀ i, cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
              (ξT i) < (d : ℤ)) ∧
            ∃ (q : T ⟶ S.last) (_ : IsDominant q) (_ : IsProper q)
              (_ : q.IsOver (Spec (CommRingCat.of K))), q ≫ S.composite = π ≫ g ∧
              (∀ V : S.last.Opens, Function.Bijective (q.app V).hom) ∧
              (∀ b : S.last, ConnectedSpace (q.fiber b)) ∧
              ∃ Δ : CodimensionOnePoint S.last →₀ ℚ,
                (∀ β, Δ β = subKltBasePrimeDiscriminantCoefficients q hnormB cT
                  (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β) ∧
                (∀ β, Δ β < 1) ∧
                (∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB → Δ β = 0) ∧
                ∃ hQΔ : OAI.RelativeDenominators.IsQCartier S.last Δ,
                ∃ (m : ℕ), 0 < m ∧ ∃ CΔ : CartierDivisor S.last,
                  (∀ β : CodimensionOnePoint S.last,
                    (cartierCoefficient CΔ (β : S.last) : ℚ) = (m : ℚ) * Δ β) ∧
                  LogPairIsKlt cB 1 m
                    (m • (smoothCanonicalDivisor cB + principalCartierDivisor S.last 1) + CΔ) ∧
                  ∃ (M : CodimensionOnePoint S.last →₀ ℚ)
                    (hQM : OAI.RelativeDenominators.IsQCartier S.last M),
                    M = moduliWeilPart (smoothCanonicalDivisor cB) (cartierPullback S.composite H)
                      Δ ((s : ℚ) / (d : ℚ)) ∧
                    ∃ (ℓ : ℕ), 0 < ℓ ∧ ∃ CM : CartierDivisor S.last,
                      (∀ β : CodimensionOnePoint S.last,
                        (cartierCoefficient CM (β : S.last) : ℚ) = (ℓ : ℚ) * M β) ∧
                      ∃ hQ : OAI.RelativeDenominators.IsQCartier S.last
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M),
                        OAI.RelativeDenominators.pullbackQCartier hnormB q
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ =
                          ((s : ℚ) / (d : ℚ)) • rationalCartierWeilDivisor
                            (cartierPullback q (cartierPullback S.composite H)) ∧
                        OAI.RelativeDenominators.pullbackQCartier hnormB q
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ =
                          rationalCartierWeilDivisor (cartierPullback q (smoothCanonicalDivisor cB)) +
                            OAI.RelativeDenominators.pullbackQCartier hnormB q Δ hQΔ +
                            OAI.RelativeDenominators.pullbackQCartier hnormB q M hQM ∧
                        OAI.RelativeDenominators.RationallyLinearlyEquivalent T
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cT +
                            principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
                            (1 / (d : ℚ)) • rationalCartierWeilDivisor
                              (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover))
                          (OAI.RelativeDenominators.pullbackQCartier hnormB q
                            (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ) ∧
                        genericPoint S.last ∈ S.composite ⁻¹ᵁ W ∧
                        ∃ (E : CartierDivisor T) (hEff : E.IsEffective),
                          (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
                            ⌈-((cartierCoefficient
                              (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
                              (t : T) : ℝ) / (d : ℝ))⌉) ∧
                          (∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
                            cartierCoefficient E (t : T) = 0) ∧
                          IsIso ((effectiveCartierPushforwardUnitMap q E hEff).over
                            (S.composite ⁻¹ᵁ W)) ∧
                          Nonempty (((Scheme.Modules.pushforward q).obj E.sheaf).restrict
                            (S.composite ⁻¹ᵁ W).ι ≅
                            SheafOfModules.unit ((S.composite ⁻¹ᵁ W) : Scheme).ringCatSheaf) ∧
                          (∀ A : CartierDivisor S.last,
                            Nonempty (A.sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
                              ((Scheme.Modules.pushforward q).obj
                                ((Scheme.Modules.pullback q).obj A.sheaf ⊗ E.sheaf)).restrict
                                  (S.composite ⁻¹ᵁ W).ι)) ∧
                          ∃ R : SchemeWeilDivisor S.last,
                            (∀ β : CodimensionOnePoint S.last, R β = ⌈-((Δ β : ℚ) : ℝ)⌉) ∧
                            0 ≤ R ∧
                            (letI : ∀ β : CodimensionOnePoint S.last,
                                IsDiscreteValuationRing (S.last.presheaf.stalk (β : S.last)) :=
                              fun β => by
                                letI := hnormB (β : S.last)
                                exact normal_codimensionOne_stalk_DVR β
                             ∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                              letI := dominant_preimage_nonempty q V
                              ∃! t : Γ(SchemeWeilDivisor.sheaf R, V),
                                (dominantFunctionFieldMap q).hom
                                  (rationalFunctionsEquiv (X := S.last) V
                                    (Scheme.Modules.Hom.app (SchemeWeilDivisor.sheafι R) V t)) =
                                rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                  (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
                            ∃ C : CartierDivisor S.last, C.IsEffective ∧
                              (∀ β : CodimensionOnePoint S.last,
                                cartierCoefficient C (β : S.last) = R β) ∧
                              (∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                                letI := dominant_preimage_nonempty q V
                                ∃! t : Γ(C.sheaf, V),
                                  (dominantFunctionFieldMap q).hom
                                    (rationalFunctionsEquiv (X := S.last) V
                                      (Scheme.Modules.Hom.app C.sheafι V t)) =
                                  rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                    (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
                              ∃ α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf,
                                Mono α ∧
                                (∀ V : S.last.Opens, Function.Injective (Scheme.Modules.Hom.app α V)) ∧
                                (∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                                  letI := dominant_preimage_nonempty q V
                                  (dominantFunctionFieldMap q).hom
                                    (rationalFunctionsEquiv (X := S.last) V
                                      (Scheme.Modules.Hom.app C.sheafι V
                                        (Scheme.Modules.Hom.app α V s₀))) =
                                    rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                      (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
                                (∃ A : CartierDivisor S.last, CartierIsAmpleProj K A) ∧
                                (d * m) • CM = (ℓ * m * s) • cartierPullback S.composite H -
                                  (d * m * ℓ) • smoothCanonicalDivisor cB - (d * ℓ) • CΔ ∧
                                ∃ L : CartierDivisor T,
                                  L = relativeAdjointCartier π q D (smoothCanonicalDivisor cB) CΔ d m ℓ ∧
                                  L = (ℓ * m) • (d • (smoothCanonicalDivisor cT +
                                    principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
                                    crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) -
                                    (d * m * ℓ) • cartierPullback q (smoothCanonicalDivisor cB) -
                                    (d * ℓ) • cartierPullback q CΔ ∧
                                  L = cartierPullback q ((d * m) • CM) +
                                    principalCartierDivisor T
                                      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) ∧
                                  (∀ j : ℕ,
                                    Nonempty ((j • ((d * m) • CM)).sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
                                      ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf).restrict
                                        (S.composite ⁻¹ᵁ W).ι)) ∧
                                  (∀ j : ℕ,
                                    ∃ β : (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ⟶
                                        (j • ((d * m) • CM) + C).sheaf,
                                      Mono β ∧
                                      ∀ V : S.last.Opens, Function.Injective (Scheme.Modules.Hom.app β V)) ∧
                                  ((Scheme.Modules.pushforward q).obj E.sheaf).IsCoherent ∧
                                  ∃ I : S.last.IdealSheafData,
                                    (idealSheafDataModule I).IsCoherent ∧
                                    ∃ e : (-C).sheaf ⊗ (Scheme.Modules.pushforward q).obj E.sheaf ≅
                                        idealSheafDataModule I,
                                      e.hom ≫ idealSheafDataModuleInclusion I =
                                        cartierTargetImageStructureHom C α ∧
                                      Nonempty ((Scheme.Modules.pushforward q).obj E.sheaf ≅
                                        C.sheaf ⊗ idealSheafDataModule I) ∧
                                      (∀ U : S.last.affineOpens,
                                        Set.range (Scheme.Modules.Hom.app
                                          (cartierTargetImageStructureHom C α) U.1) =
                                          (I.ideal U : Set Γ(S.last, U.1))) ∧
                                      I ≠ ⊥ ∧ genericPoint S.last ∉ (I.support : Set S.last) ∧
                                      (∀ j : ℕ,
                                        Nonempty ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
                                          (j • ((d * m) • CM) + C).sheaf ⊗ idealSheafDataModule I)) ∧
                                      ∃ (B' : Scheme.{u}) (_ : IsIntegral B')
                                        (_ : B'.Over (Spec (CommRingCat.of K))) (_ : IsNoetherian B')
                                        (_ : SmoothOfRelativeDimension k (B' ↘ Spec (CommRingCat.of K)))
                                        (ρ' : B' ⟶ S.last) (_ : IsDominant ρ')
                                        (_ : ρ'.IsOver (Spec (CommRingCat.of K)))
                                        (_ : IsProper ρ') (_ : IsProjective ρ')
                                        (_ : LocallyOfFiniteType (B' ↘ Spec (CommRingCat.of K)))
                                        (_ : QuasiCompact (B' ↘ Spec (CommRingCat.of K)))
                                        (_ : IsSeparated (B' ↘ Spec (CommRingCat.of K)))
                                        (hρ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ'))
                                        (cB' : EtaleChart K B' k) (r' : ℕ) (ξ' : Fin r' → B'),
                                        Function.Injective ξ' ∧ (∀ i, Order.coheight (ξ' i) = 1) ∧
                                        IsSNCFamily K k ξ' ∧
                                        (∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ' →
                                          cartierCoefficient (crepantBoundaryCartier ρ' hρ' cB 1 m
                                            (m • (smoothCanonicalDivisor cB +
                                              principalCartierDivisor S.last 1) + CΔ)
                                            cB' etaleCharts_cover) (t : B') = 0) ∧
                                        (∀ (j : Option Bool) (t : CodimensionOnePoint B'),
                                          (t : B') ∉ Set.range ξ' →
                                          cartierCoefficient (cartierPullback ρ'
                                            (match j with | none => C | some true => CM | some false => CΔ))
                                            (t : B') = 0) ∧
                                        (∀ (N : ℕ) (eB : S.last ⟶ polynomialProjectiveScheme N K),
                                          IsClosedImmersion eB →
                                          eB ≫ polynomialProjectiveToBase N K = S.last ↘ Spec (CommRingCat.of K) →
                                          ∃ (M' : ℕ) (eB' : B' ⟶ polynomialProjectiveScheme M' K),
                                            IsClosedImmersion eB' ∧ eB' ≫ polynomialProjectiveToBase M' K =
                                              B' ↘ Spec (CommRingCat.of K)) ∧
                                        (∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ' →
                                          (t : B') ∉ (I.comap ρ').support) ∧
                                        (I.comap ρ').IsInvertible ∧
                                        (∃ a : B' ⟶ I.blowUp, a ≫ I.blowUpπ = ρ') ∧
                                        ∃ (P : CartierDivisor B') (hP : P.IsEffective),
                                          effectiveCartierIdealSheaf P hP = I.comap ρ' ∧
                                          (∀ t : CodimensionOnePoint B', (t : B') ∉ Set.range ξ' →
                                            cartierCoefficient P (t : B') = 0) ∧
                                          ∃ Z : Closeds S.last,
                                            Z = I.support ⊔ cartierSupportCloseds C ⊔
                                              cartierSupportCloseds CM ⊔ cartierSupportCloseds CΔ ∧
                                            genericPoint S.last ∉ (Z : Set S.last) ∧
                                          ∃ S₁ : Scheme.BlowUpSequence S.last,
                                            (∀ (i : Fin S₁.length) (z : S₁.stage i.castSucc), z ∈ (S₁.center i).support →
                                              S₁.stageMap i.castSucc z ∈ (Z : Set S.last)) ∧
                                            ∃ (_ : IsIntegral S₁.last) (_ : S₁.last.Over (Spec (CommRingCat.of K)))
                                              (_ : IsNoetherian S₁.last)
                                              (_ : SmoothOfRelativeDimension k (S₁.last ↘ Spec (CommRingCat.of K)))
                                              (_ : IsDominant S₁.composite) (_ : S₁.composite.IsOver (Spec (CommRingCat.of K)))
                                              (_ : IsProper S₁.composite) (_ : IsProjective S₁.composite)
                                              (_ : LocallyOfFiniteType (S₁.last ↘ Spec (CommRingCat.of K)))
                                              (_ : QuasiCompact (S₁.last ↘ Spec (CommRingCat.of K)))
                                              (_ : IsSeparated (S₁.last ↘ Spec (CommRingCat.of K)))
                                              (cB₂ : EtaleChart K S₁.last k),
                                              Function.Bijective (dominantFunctionFieldAlgHom (K := K) S₁.composite) ∧
                                              IsIso (S₁.composite ∣_ Z.compl) ∧
                                              ∃ (rB₂ : ℕ) (ξB₂ : Fin rB₂ → S₁.last), Function.Injective ξB₂ ∧
                                                (∀ i, Order.coheight (ξB₂ i) = 1) ∧ IsSNCFamily K k ξB₂ ∧
                                                (∀ b : CodimensionOnePoint S₁.last, (b : S₁.last) ∉ Set.range ξB₂ →
                                                  S₁.composite (b : S₁.last) ∉ (Z : Set S.last)) ∧
                                                (I.comap S₁.composite).IsInvertible ∧
                                                ∃ (P₂ : CartierDivisor S₁.last) (hP₂ : P₂.IsEffective),
                                                  effectiveCartierIdealSheaf P₂ hP₂ = I.comap S₁.composite ∧
                                                  (∀ b : CodimensionOnePoint S₁.last, (b : S₁.last) ∉ Set.range ξB₂ →
                                                    cartierCoefficient P₂ (b : S₁.last) = 0) ∧
                                                  ∃ (T₁ : Scheme.{u}) (_ : IsIntegral T₁) (_ : T₁.Over (Spec (CommRingCat.of K)))
                                                    (_ : IsNoetherian T₁)
                                                    (_ : SmoothOfRelativeDimension n (T₁ ↘ Spec (CommRingCat.of K)))
                                                    (τ : T₁ ⟶ T) (_ : IsDominant τ) (_ : τ.IsOver (Spec (CommRingCat.of K)))
                                                    (_ : IsProper τ) (_ : IsProjective τ)
                                                    (_ : LocallyOfFiniteType (T₁ ↘ Spec (CommRingCat.of K)))
                                                    (_ : QuasiCompact (T₁ ↘ Spec (CommRingCat.of K)))
                                                    (_ : IsSeparated (T₁ ↘ Spec (CommRingCat.of K)))
                                                    (hτ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) τ))
                                                    (cT₁ : EtaleChart K T₁ n) (rT₂ : ℕ) (ξT₂ : Fin rT₂ → T₁),
                                                    Function.Injective ξT₂ ∧ (∀ i, Order.coheight (ξT₂ i) = 1) ∧ IsSNCFamily K n ξT₂ ∧
                                                    (∀ t : CodimensionOnePoint T₁, (t : T₁) ∉ Set.range ξT₂ →
                                                      cartierCoefficient (crepantBoundaryCartier τ hτ cT (crepantPullbackFormUnit π hπ c f cT) d (cartierPullback π D) cT₁ etaleCharts_cover)
                                                        (t : T₁) = 0) ∧
                                                    LogPairIsKlt cT₁ (crepantPullbackFormUnit τ hτ cT (crepantPullbackFormUnit π hπ c f cT) cT₁) d (cartierPullback τ (cartierPullback π D)) ∧
                                                    ∃ (q₁ : T₁ ⟶ S₁.last) (_ : IsDominant q₁) (_ : IsProper q₁)
                                                      (_ : q₁.IsOver (Spec (CommRingCat.of K))),
                                                      q₁ ≫ S₁.composite = τ ≫ q ∧
                                                      (∀ U : S₁.last.Opens, Function.Bijective (q₁.app U).hom) ∧
                                                      (∀ b : S₁.last, ConnectedSpace (q₁.fiber b)) ∧
                                                      ∃ (E₁ : CartierDivisor T₁) (_ : E₁.IsEffective),
                                                        (∀ t : CodimensionOnePoint T₁, cartierCoefficient E₁ (t : T₁) =
                                                          ⌈-((cartierCoefficient (crepantBoundaryCartier τ hτ cT (crepantPullbackFormUnit π hπ c f cT) d (cartierPullback π D) cT₁ etaleCharts_cover)
                                                            (t : T₁) : ℝ) / (d : ℝ))⌉) ∧
                                                        Nonempty (E.sheaf ≅ (Scheme.Modules.pushforward τ).obj E₁.sheaf) ∧
                                                        Nonempty ((Scheme.Modules.pushforward q).obj E.sheaf ≅
                                                          (Scheme.Modules.pushforward S₁.composite).obj
                                                            ((Scheme.Modules.pushforward q₁).obj E₁.sheaf)) ∧
                                                        (∀ t : CodimensionOnePoint T₁,
                                                          cartierCoefficient E₁ (t : T₁) =
                                                          ⌈-((cartierCoefficient (crepantBoundaryCartier (τ ≫ π)
                                                            (dominantFunctionFieldAlgHom_comp_bijective π τ hπ hτ)
                                                            c f d D cT₁ etaleCharts_cover) (t : T₁) : ℝ) /
                                                              (d : ℝ))⌉) ∧
                                                        ∃ (hProjBase : ∃ A : CartierDivisor S.last, CartierIsAmpleProj K A)
                                                          (hProjChanged : ∃ A : CartierDivisor S₁.last, CartierIsAmpleProj K A)
                                                          (sF : (Scheme.Modules.pushforward q).obj E.sheaf ≅
                                                            C.sheaf ⊗ idealSheafDataModule I)
                                                          (hSquare : τ ≫ q = q₁ ≫ S₁.composite)
                                                          (hL : L = cartierPullback q ((d * m) • CM) +
                                                            principalCartierDivisor T
                                                              ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)))
                                                          (e₀ : (Scheme.Modules.pushforward q).obj E.sheaf ≅
                                                            (Scheme.Modules.pushforward S₁.composite).obj
                                                              ((Scheme.Modules.pushforward q₁).obj E₁.sheaf)),
                                                          (∀ j : ℕ, Nonempty
                                                            ((j • cartierPullback S₁.composite ((d * m) • CM) +
                                                              (cartierPullback S₁.composite C - P₂)).sheaf ≅
                                                            image (changedRoundupBaseChangeMap S₁.composite
                                                              (actualRelativeAdjointChangedMultiplePushforwardIso
                                                                hProjBase hProjChanged q S₁.composite q₁ τ hSquare
                                                                ((d * m) • CM) C L E E₁
                                                                ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
                                                                hL I sF e₀ j)))) ∧
                                                          (∀ j : ℕ, Nonempty
                                                            ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
                                                              (Scheme.Modules.pushforward S₁.composite).obj
                                                                (j • cartierPullback S₁.composite ((d * m) • CM) +
                                                                  (cartierPullback S₁.composite C - P₂)).sheaf)) ∧
                                                          topologicalKrullDim S₁.last = k ∧
                                                          (∀ j : ℕ, Nonempty
                                                            (Γ((j • L + E).sheaf, ⊤) ≃ₗ[K]
                                                              Γ((j • cartierPullback S₁.composite ((d * m) • CM) +
                                                                (cartierPullback S₁.composite C - P₂)).sheaf, ⊤))) ∧
                                                          (∀ j : ℕ, FiniteDimensional K Γ((j • L + E).sheaf, ⊤)) ∧
                                                          (∃ c : ℝ, 0 ≤ c ∧ ∀ j : ℕ,
                                                            (Module.finrank K Γ((j • L + E).sheaf, ⊤) : ℝ) ≤
                                                              c * ((j : ℝ) + 1) ^ k) ∧
                                                          (∃ c : ℝ, 0 ≤ c ∧ ∀ j : ℕ,
                                                            (Module.finrank K Γ((j • L).sheaf, ⊤) : ℝ) ≤
                                                              c * ((j : ℝ) + 1) ^ k) ∧
                                                          (∀ l : ℕ, CartierIitakaDimension K L l → l ≤ k) := by
  by_contra hNoModel
  have hPacked000 := exists_compatible_snc_moduli_models_with_changed_fibration
      hProjY g hnormX hnormY happ cY c f d hd D heff hklt H s ψ hD
  obtain ⟨W, hPacked001⟩ := hPacked000
  obtain ⟨hW, hPacked002⟩ := hPacked001
  obtain ⟨S, hPacked003⟩ := hPacked002
  obtain ⟨hBi, hPacked004⟩ := hPacked003
  obtain ⟨instB, hPacked005⟩ := hPacked004
  obtain ⟨hBN, hPacked006⟩ := hPacked005
  obtain ⟨hBsm, hPacked007⟩ := hPacked006
  obtain ⟨hρdom, hPacked008⟩ := hPacked007
  obtain ⟨hρover, hPacked009⟩ := hPacked008
  obtain ⟨hρprop, hPacked010⟩ := hPacked009
  obtain ⟨hρproj, hPacked011⟩ := hPacked010
  obtain ⟨hBft, hPacked012⟩ := hPacked011
  obtain ⟨hBqc, hPacked013⟩ := hPacked012
  obtain ⟨hBsep, hPacked014⟩ := hPacked013
  obtain ⟨cB, hPacked015⟩ := hPacked014
  obtain ⟨hnormB, hPacked016⟩ := hPacked015
  obtain ⟨hρ, hPacked017⟩ := hPacked016
  obtain ⟨hiso, hPacked018⟩ := hPacked017
  obtain ⟨rB, hPacked019⟩ := hPacked018
  obtain ⟨ξB, hPacked020⟩ := hPacked019
  obtain ⟨hinjB, hPacked021⟩ := hPacked020
  obtain ⟨hcodB, hPacked022⟩ := hPacked021
  obtain ⟨hsncB, hPacked023⟩ := hPacked022
  obtain ⟨hgood, hPacked024⟩ := hPacked023
  obtain ⟨T, hPacked025⟩ := hPacked024
  obtain ⟨hTi, hPacked026⟩ := hPacked025
  obtain ⟨instT, hPacked027⟩ := hPacked026
  obtain ⟨hTN, hPacked028⟩ := hPacked027
  obtain ⟨hTsm, hPacked029⟩ := hPacked028
  obtain ⟨π, hPacked030⟩ := hPacked029
  obtain ⟨hπdom, hPacked031⟩ := hPacked030
  obtain ⟨hπover, hPacked032⟩ := hPacked031
  obtain ⟨hπprop, hPacked033⟩ := hPacked032
  obtain ⟨hπproj, hPacked034⟩ := hPacked033
  obtain ⟨hTft, hPacked035⟩ := hPacked034
  obtain ⟨hTqc, hPacked036⟩ := hPacked035
  obtain ⟨hTsep, hPacked037⟩ := hPacked036
  obtain ⟨hπ, hPacked038⟩ := hPacked037
  obtain ⟨cT, hPacked039⟩ := hPacked038
  obtain ⟨hkltT, hPacked040⟩ := hPacked039
  obtain ⟨rT, hPacked041⟩ := hPacked040
  obtain ⟨ξT, hPacked042⟩ := hPacked041
  obtain ⟨hinjT, hPacked043⟩ := hPacked042
  obtain ⟨hcodT, hPacked044⟩ := hPacked043
  obtain ⟨hsncT, hPacked045⟩ := hPacked044
  obtain ⟨hBT, hPacked046⟩ := hPacked045
  obtain ⟨hbT, hPacked047⟩ := hPacked046
  obtain ⟨q, hPacked048⟩ := hPacked047
  obtain ⟨hqdom, hPacked049⟩ := hPacked048
  obtain ⟨hqprop, hPacked050⟩ := hPacked049
  obtain ⟨hqover, hPacked051⟩ := hPacked050
  obtain ⟨hq, hPacked052⟩ := hPacked051
  obtain ⟨hqapp, hPacked053⟩ := hPacked052
  obtain ⟨hconnected, hPacked054⟩ := hPacked053
  obtain ⟨Δ, hPacked055⟩ := hPacked054
  obtain ⟨hΔ, hPacked056⟩ := hPacked055
  obtain ⟨hlt, hPacked057⟩ := hPacked056
  obtain ⟨hΔsupp, hPacked058⟩ := hPacked057
  obtain ⟨hQΔ, hPacked059⟩ := hPacked058
  obtain ⟨m, hPacked060⟩ := hPacked059
  obtain ⟨hm, hPacked061⟩ := hPacked060
  obtain ⟨CΔ, hPacked062⟩ := hPacked061
  obtain ⟨hCΔ, hPacked063⟩ := hPacked062
  obtain ⟨hkltB, hPacked064⟩ := hPacked063
  obtain ⟨M, hPacked065⟩ := hPacked064
  obtain ⟨hQM, hPacked066⟩ := hPacked065
  obtain ⟨hM, hPacked067⟩ := hPacked066
  obtain ⟨ℓ, hPacked068⟩ := hPacked067
  obtain ⟨hℓ, hPacked069⟩ := hPacked068
  obtain ⟨CM, hPacked070⟩ := hPacked069
  obtain ⟨hCM, hPacked071⟩ := hPacked070
  obtain ⟨hQ, hPacked072⟩ := hPacked071
  obtain ⟨hpull, hPacked073⟩ := hPacked072
  obtain ⟨hseparate, hPacked074⟩ := hPacked073
  obtain ⟨hlinear, hPacked075⟩ := hPacked074
  obtain ⟨hgen, hPacked076⟩ := hPacked075
  obtain ⟨E, hPacked077⟩ := hPacked076
  obtain ⟨hEff, hPacked078⟩ := hPacked077
  obtain ⟨hEc, hPacked079⟩ := hPacked078
  obtain ⟨hExc, hPacked080⟩ := hPacked079
  obtain ⟨hunit, hPacked081⟩ := hPacked080
  obtain ⟨hframe, hPacked082⟩ := hPacked081
  obtain ⟨htwists, hPacked083⟩ := hPacked082
  obtain ⟨R, hPacked084⟩ := hPacked083
  obtain ⟨hR, hPacked085⟩ := hPacked084
  obtain ⟨hReff, hPacked086⟩ := hPacked085
  obtain ⟨hdescWeil, hPacked087⟩ := hPacked086
  obtain ⟨C, hPacked088⟩ := hPacked087
  obtain ⟨hCeff, hPacked089⟩ := hPacked088
  obtain ⟨hCR, hPacked090⟩ := hPacked089
  obtain ⟨hdescC, hPacked091⟩ := hPacked090
  obtain ⟨α, hPacked092⟩ := hPacked091
  obtain ⟨hαmono, hPacked093⟩ := hPacked092
  obtain ⟨hαinj, hPacked094⟩ := hPacked093
  obtain ⟨hαfield, hPacked095⟩ := hPacked094
  obtain ⟨hProjB, hPacked096⟩ := hPacked095
  obtain ⟨hbase, hPacked097⟩ := hPacked096
  obtain ⟨L, hPacked098⟩ := hPacked097
  obtain ⟨hLeq, hPacked099⟩ := hPacked098
  obtain ⟨hcrepant, hPacked100⟩ := hPacked099
  obtain ⟨hprincipal, hPacked101⟩ := hPacked100
  obtain ⟨hadjoint, hPacked102⟩ := hPacked101
  obtain ⟨hallj, hPacked103⟩ := hPacked102
  obtain ⟨hFcoh, hPacked104⟩ := hPacked103
  obtain ⟨I, hPacked105⟩ := hPacked104
  obtain ⟨hIcoh, hPacked106⟩ := hPacked105
  obtain ⟨e, hPacked107⟩ := hPacked106
  obtain ⟨he, hPacked108⟩ := hPacked107
  obtain ⟨hFiso, hPacked109⟩ := hPacked108
  obtain ⟨hIimage, hPacked110⟩ := hPacked109
  obtain ⟨hIne, hPacked111⟩ := hPacked110
  obtain ⟨hIgen, hPacked112⟩ := hPacked111
  obtain ⟨hAllIso, hPacked113⟩ := hPacked112
  obtain ⟨B', hPacked114⟩ := hPacked113
  obtain ⟨hB'i, hPacked115⟩ := hPacked114
  obtain ⟨instB', hPacked116⟩ := hPacked115
  obtain ⟨hB'N, hPacked117⟩ := hPacked116
  obtain ⟨hB'sm, hPacked118⟩ := hPacked117
  obtain ⟨ρ', hPacked119⟩ := hPacked118
  obtain ⟨hρ'dom, hPacked120⟩ := hPacked119
  obtain ⟨hρ'over, hPacked121⟩ := hPacked120
  obtain ⟨hρ'prop, hPacked122⟩ := hPacked121
  obtain ⟨hρ'proj, hPacked123⟩ := hPacked122
  obtain ⟨hB'ft, hPacked124⟩ := hPacked123
  obtain ⟨hB'qc, hPacked125⟩ := hPacked124
  obtain ⟨hB'sep, hPacked126⟩ := hPacked125
  obtain ⟨hρ', hPacked127⟩ := hPacked126
  obtain ⟨cB', hPacked128⟩ := hPacked127
  obtain ⟨r', hPacked129⟩ := hPacked128
  obtain ⟨ξ', hPacked130⟩ := hPacked129
  obtain ⟨hinj', hPacked131⟩ := hPacked130
  obtain ⟨hcod', hPacked132⟩ := hPacked131
  obtain ⟨hsnc', hPacked133⟩ := hPacked132
  obtain ⟨hboundary', hPacked134⟩ := hPacked133
  obtain ⟨hG', hPacked135⟩ := hPacked134
  obtain ⟨hemb', hPacked136⟩ := hPacked135
  obtain ⟨hoff', hPacked137⟩ := hPacked136
  obtain ⟨hInv', hPacked138⟩ := hPacked137
  obtain ⟨hlift', hPacked139⟩ := hPacked138
  obtain ⟨P, hPacked140⟩ := hPacked139
  obtain ⟨hP, hPacked141⟩ := hPacked140
  obtain ⟨hPI, hPacked142⟩ := hPacked141
  obtain ⟨hPsupp, hPacked143⟩ := hPacked142
  obtain ⟨Z, hPacked144⟩ := hPacked143
  obtain ⟨hZeq, hPacked145⟩ := hPacked144
  obtain ⟨hZ, hPacked146⟩ := hPacked145
  obtain ⟨S₁, hPacked147⟩ := hPacked146
  obtain ⟨hc₁, hPacked148⟩ := hPacked147
  obtain ⟨hB₂i, hPacked149⟩ := hPacked148
  obtain ⟨instB₂, hPacked150⟩ := hPacked149
  obtain ⟨hB₂N, hPacked151⟩ := hPacked150
  obtain ⟨hB₂sm, hPacked152⟩ := hPacked151
  obtain ⟨hρ₂dom, hPacked153⟩ := hPacked152
  obtain ⟨hρ₂over, hPacked154⟩ := hPacked153
  obtain ⟨hρ₂prop, hPacked155⟩ := hPacked154
  obtain ⟨hρ₂proj, hPacked156⟩ := hPacked155
  obtain ⟨hB₂ft, hPacked157⟩ := hPacked156
  obtain ⟨hB₂qc, hPacked158⟩ := hPacked157
  obtain ⟨hB₂sep, hPacked159⟩ := hPacked158
  obtain ⟨cB₂, hPacked160⟩ := hPacked159
  obtain ⟨hρ₂, hPacked161⟩ := hPacked160
  obtain ⟨hiso₂, hPacked162⟩ := hPacked161
  obtain ⟨rB₂, hPacked163⟩ := hPacked162
  obtain ⟨ξB₂, hPacked164⟩ := hPacked163
  obtain ⟨hinjB₂, hPacked165⟩ := hPacked164
  obtain ⟨hcodB₂, hPacked166⟩ := hPacked165
  obtain ⟨hsncB₂, hPacked167⟩ := hPacked166
  obtain ⟨hoffB₂, hPacked168⟩ := hPacked167
  obtain ⟨hInv₂, hPacked169⟩ := hPacked168
  obtain ⟨P₂, hPacked170⟩ := hPacked169
  obtain ⟨hP₂, hPacked171⟩ := hPacked170
  obtain ⟨hPI₂, hPacked172⟩ := hPacked171
  obtain ⟨hPsupp₂, hPacked173⟩ := hPacked172
  obtain ⟨T₁, hPacked174⟩ := hPacked173
  obtain ⟨hT₁i, hPacked175⟩ := hPacked174
  obtain ⟨instT₁, hPacked176⟩ := hPacked175
  obtain ⟨hT₁N, hPacked177⟩ := hPacked176
  obtain ⟨hT₁sm, hPacked178⟩ := hPacked177
  obtain ⟨τ, hPacked179⟩ := hPacked178
  obtain ⟨hτdom, hPacked180⟩ := hPacked179
  obtain ⟨hτover, hPacked181⟩ := hPacked180
  obtain ⟨hτprop, hPacked182⟩ := hPacked181
  obtain ⟨hτproj, hPacked183⟩ := hPacked182
  obtain ⟨hT₁ft, hPacked184⟩ := hPacked183
  obtain ⟨hT₁qc, hPacked185⟩ := hPacked184
  obtain ⟨hT₁sep, hPacked186⟩ := hPacked185
  obtain ⟨hτ, hPacked187⟩ := hPacked186
  obtain ⟨cT₁, hPacked188⟩ := hPacked187
  obtain ⟨rT₂, hPacked189⟩ := hPacked188
  obtain ⟨ξT₂, hPacked190⟩ := hPacked189
  obtain ⟨hinjT₂, hPacked191⟩ := hPacked190
  obtain ⟨hcodT₂, hPacked192⟩ := hPacked191
  obtain ⟨hsncT₂, hPacked193⟩ := hPacked192
  obtain ⟨hsuppT₂, hPacked194⟩ := hPacked193
  obtain ⟨hkltT₂, hPacked195⟩ := hPacked194
  obtain ⟨q₁, hPacked196⟩ := hPacked195
  obtain ⟨hq₁dom, hPacked197⟩ := hPacked196
  obtain ⟨hq₁prop, hPacked198⟩ := hPacked197
  obtain ⟨hq₁over, hPacked199⟩ := hPacked198
  obtain ⟨hsquare₁, hPacked200⟩ := hPacked199
  obtain ⟨happ₁, hPacked201⟩ := hPacked200
  obtain ⟨hconnected₁, hPacked202⟩ := hPacked201
  obtain ⟨E₁, hPacked203⟩ := hPacked202
  obtain ⟨hE₁eff, hPacked204⟩ := hPacked203
  obtain ⟨hE₁, hPacked205⟩ := hPacked204
  obtain ⟨hEiso, hPacked206⟩ := hPacked205
  obtain ⟨hEbaseiso, hPacked207⟩ := hPacked206
  have hEorig := hPacked207
  letI : (idealSheafDataModule I).IsCoherent := hIcoh
  letI := hIcoh.isQuasicoherent
  let sF := Classical.choice hFiso
  let e₀ := Classical.choice hEbaseiso
  have hProjChanged : ∃ A : CartierDivisor S₁.last, CartierIsAmpleProj K A :=
    blowUpSequence_exists_ample_cartier hProjB S₁
  have hUniform := actualRelativeAdjointChangedMultipleComparison_uniform_actual_image_iso
    hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀
  have hRecover := actualRelativeAdjointMultiple_principalized_pushforward_iso
    (β := S₁.composite) hProjB hProjChanged q q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀
  have hdimBase : topologicalKrullDim S₁.last = k :=
    geometricDimension_eq_of_smooth_relativeDimension (S₁.last ↘ Spec (CommRingCat.of K))
  have hSections := actualRelativeAdjointMultiple_principalized_globalSections_linearEquiv
    hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀
  have hFinite := actualRelativeAdjointMultiple_principalized_finiteDimensional_all_dimensions
    hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀ hdimBase
  have hBound := actualRelativeAdjointMultiple_principalized_finrank_polynomial_upper_all_dimensions
    hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀ hdimBase
  have hUnrounded := actualRelativeAdjointMultiple_principalized_unrounded_finrank_polynomial_upper_all_dimensions
    hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
    ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
    hprincipal I hIne sF P₂ hP₂ hPI₂ e₀ hEff hdimBase
  have hIitaka : ∀ l : ℕ, CartierIitakaDimension K L l → l ≤ k := by
    intro l hl
    exact actualRelativeAdjoint_principalized_iitakaDimension_le_all_dimensions
      hProjB hProjChanged q S₁.composite q₁ τ hsquare₁.symm ((d * m) • CM) C L E E₁
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
      hprincipal I hIne sF P₂ hP₂ hPI₂ e₀ hEff hdimBase hl
  apply hNoModel
  exact ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists,
    R, hR, hReff, hdescWeil, C, hCeff, hCR, hdescC, α, hαmono, hαinj, hαfield,
    hProjB, hbase, L, hLeq, hcrepant, hprincipal, hadjoint, hallj,
    hFcoh, I, hIcoh, e, he, hFiso, hIimage, hIne, hIgen, hAllIso,
    B', hB'i, instB', hB'N, hB'sm, ρ', hρ'dom, hρ'over, hρ'prop, hρ'proj,
    hB'ft, hB'qc, hB'sep, hρ', cB', r', ξ', hinj', hcod', hsnc',
    hboundary', hG', hemb', hoff', hInv', hlift', P, hP, hPI, hPsupp, Z, hZeq, hZ,
    S₁, hc₁, hB₂i, instB₂, hB₂N, hB₂sm, hρ₂dom, hρ₂over, hρ₂prop, hρ₂proj,
    hB₂ft, hB₂qc, hB₂sep, cB₂, hρ₂, hiso₂, rB₂, ξB₂, hinjB₂, hcodB₂, hsncB₂,
    hoffB₂, hInv₂, P₂, hP₂, hPI₂, hPsupp₂, T₁, hT₁i, instT₁, hT₁N, hT₁sm,
    τ, hτdom, hτover, hτprop, hτproj, hT₁ft, hT₁qc, hT₁sep, hτ, cT₁,
    rT₂, ξT₂, hinjT₂, hcodT₂, hsncT₂, hsuppT₂, hkltT₂,
    q₁, hq₁dom, hq₁prop, hq₁over, hsquare₁, happ₁, hconnected₁,
    E₁, hE₁eff, hE₁, hEiso, hEbaseiso, hEorig, hProjB, hProjChanged, sF, hsquare₁.symm, hprincipal, e₀, hUniform, hRecover, hdimBase, hSections, hFinite, hBound, hUnrounded, hIitaka⟩

end MixedFujita

