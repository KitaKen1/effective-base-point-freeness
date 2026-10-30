/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModuliPrincipalizedImageIdealModel
public import MixedFujita.SNCPrincipalizedChangedFibration

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

universe u

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
theorem exists_compatible_snc_moduli_models_with_changed_fibration
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
                                                              (d : ℝ))⌉) := by
  obtain ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
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
    hboundary', hG', hemb', hoff', hInv', hlift', P, hP, hPI, hPsupp⟩ :=
    exists_compatible_snc_moduli_models_with_principalized_image_ideal
      hProjY g hnormX hnormY happ cY c f d hd D heff hklt H s ψ hD
  haveI : Smooth (S.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth k _
  haveI : IsRegular S.last :=
    (Scheme.smooth_iff_isRegular (S.last ↘ Spec (CommRingCat.of K))).mp inferInstance
  haveI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨hEffN, hKltN⟩ := crepant_source_roundup_normalized_pair_effective_klt
    π hπ hnormT c f d hd D cT ξT hinjT hcodT hsncT hBT E hEff hEc
  let Z : Closeds S.last := I.support ⊔ cartierSupportCloseds C ⊔
    cartierSupportCloseds CM ⊔ cartierSupportCloseds CΔ
  have hZ : genericPoint S.last ∉ (Z : Set S.last) := by
    change ¬ (((genericPoint S.last ∈ I.support ∨
      genericPoint S.last ∈ cartierSupportCloseds C) ∨
      genericPoint S.last ∈ cartierSupportCloseds CM) ∨
      genericPoint S.last ∈ cartierSupportCloseds CΔ)
    rintro (((h | h) | h) | h)
    · exact hIgen h
    · exact genericPoint_notMem_cartierSupportCloseds C h
    · exact genericPoint_notMem_cartierSupportCloseds CM h
    · exact genericPoint_notMem_cartierSupportCloseds CΔ h
  have hIZ : (I.support : Set S.last) ⊆ (Z : Set S.last) := by
    intro b hb
    exact Or.inl (Or.inl (Or.inl hb))
  obtain ⟨S₁, hc₁, hB₂i, instB₂, hB₂N, hB₂sm, hρ₂dom, hρ₂over, hρ₂prop, hρ₂proj,
    hB₂ft, hB₂qc, hB₂sep, cB₂, hρ₂, hiso₂, rB₂, ξB₂, hinjB₂, hcodB₂, hsncB₂,
    hoffB₂, hInv₂, P₂, hP₂, hPI₂, hPsupp₂, T₁, hT₁i, instT₁, hT₁N, hT₁sm,
    τ, hτdom, hτover, hτprop, hτproj, hT₁ft, hT₁qc, hT₁sep, hτ, cT₁,
    rT₂, ξT₂, hinjT₂, hcodT₂, hsncT₂, hsuppT₂, hkltT₂,
    q₁, hq₁dom, hq₁prop, hq₁over, hsquare₁, happ₁, hconnected₁,
    E₁, hE₁eff, hE₁, hEiso, hEbaseiso⟩ :=
    exists_principalized_changed_stein_fibration_with_roundup_pushforward
      q hqapp cB Z hZ I hIZ cT (crepantPullbackFormUnit π hπ c f cT) d hd
      (cartierPullback π D) E hEff hkltT hEffN hKltN
  have hEorig : ∀ t : CodimensionOnePoint T₁, cartierCoefficient E₁ (t : T₁) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (τ ≫ π)
        (dominantFunctionFieldAlgHom_comp_bijective π τ hπ hτ) c f d D cT₁ etaleCharts_cover)
          (t : T₁) : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hE₁ t, crepantBoundaryCartier_comp π τ hπ hτ]
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
    hboundary', hG', hemb', hoff', hInv', hlift', P, hP, hPI, hPsupp, Z, rfl, hZ,
    S₁, hc₁, hB₂i, instB₂, hB₂N, hB₂sm, hρ₂dom, hρ₂over, hρ₂prop, hρ₂proj,
    hB₂ft, hB₂qc, hB₂sep, cB₂, hρ₂, hiso₂, rB₂, ξB₂, hinjB₂, hcodB₂, hsncB₂,
    hoffB₂, hInv₂, P₂, hP₂, hPI₂, hPsupp₂, T₁, hT₁i, instT₁, hT₁N, hT₁sm,
    τ, hτdom, hτover, hτprop, hτproj, hT₁ft, hT₁qc, hT₁sep, hτ, cT₁,
    rT₂, ξT₂, hinjT₂, hcodT₂, hsncT₂, hsuppT₂, hkltT₂,
    q₁, hq₁dom, hq₁prop, hq₁over, hsquare₁, happ₁, hconnected₁,
    E₁, hE₁eff, hE₁, hEiso, hEbaseiso, hEorig⟩

end MixedFujita
