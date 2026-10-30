/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompatibleSteinSNCDiscriminantSupportModel
public import MixedFujita.CrepantModuliPullbackPresentation
public import MixedFujita.SmoothSNCBaseSequence
public import MixedFujita.SNCSourceOverBaseSequence
public import MixedFujita.SNCWeilCartierMultiple
public import MixedFujita.ModifiedBaseDiscriminantWeilDivisor
public import MixedFujita.SmoothBaseBlowUpResolution
public import MixedFujita.SteinBirationalModelInvariance
public import MixedFujita.CompatibleSteinSNCModel

/-! The original effective klt Stein morphism admits one actual compatible model
whose discriminant has SNC support, a Cartier multiple and an all-model sub-klt
base pair. Its finite Weil moduli part is individually Q-Cartier and has an actual
Cartier multiple. The actual pullback splits into all three parts and satisfies
the original crepant rational linear equivalence. Moduli descent and positivity
and effectivity of a resulting base boundary are not asserted. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Individual Q-Cartierness of the moduli part follows once the actual discriminant is Q-Cartier. -/
theorem moduliWeilPart_isQCartier_of_discriminant
    {B : Scheme.{u}} [IsIntegral B] [IsNoetherian B]
    (C H : CartierDivisor B) (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ)
    (hΔ : OAI.RelativeDenominators.IsQCartier B Δ) :
    OAI.RelativeDenominators.IsQCartier B (moduliWeilPart C H Δ a) := by
  have hC := OAI.RelativeDenominators.isQCartier_smul (rationalCartierWeilDivisor_isQCartier C) (-1)
  have hnegΔ := OAI.RelativeDenominators.isQCartier_smul hΔ (-1)
  have hH := OAI.RelativeDenominators.isQCartier_smul (rationalCartierWeilDivisor_isQCartier H) a
  simpa only [moduliWeilPart, sub_eq_add_neg, neg_one_smul] using
    OAI.RelativeDenominators.isQCartier_add (OAI.RelativeDenominators.isQCartier_add hH hC) hnegΔ

/-- Construct a genuine Cartier multiple of the finite moduli Weil divisor on the same normal base. -/
theorem moduliWeilPart_exists_actual_cartier_multiple
    {B : Scheme.{u}} [IsIntegral B] [IsNoetherian B]
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (C H : CartierDivisor B) (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ)
    (hΔ : OAI.RelativeDenominators.IsQCartier B Δ) :
    ∃ (ℓ : ℕ), 0 < ℓ ∧ ∃ CM : CartierDivisor B,
      ∀ β : CodimensionOnePoint B, (cartierCoefficient CM (β : B) : ℚ) =
        (ℓ : ℚ) * moduliWeilPart C H Δ a β := by
  exact (isQCartier_iff_exists_actual_cartier_multiple hnormB _).mp
    (moduliWeilPart_isQCartier_of_discriminant C H Δ a hΔ)

/-- The actual pullback splits into canonical, discriminant and individually Q-Cartier moduli parts. -/
theorem moduliWeilPart_pullback_separate
    {B T : Scheme.{u}} [IsIntegral B] [IsNoetherian B] [IsIntegral T] [IsNoetherian T]
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (q : T ⟶ B) [IsDominant q] (C H : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (a : ℚ)
    (hΔ : OAI.RelativeDenominators.IsQCartier B Δ) :
    OAI.RelativeDenominators.pullbackQCartier hnormB q
      (rationalCartierWeilDivisor C + Δ + moduliWeilPart C H Δ a)
      (moduliWeilPart_combination_isQCartier C H Δ a) =
      rationalCartierWeilDivisor (cartierPullback q C) +
        OAI.RelativeDenominators.pullbackQCartier hnormB q Δ hΔ +
        OAI.RelativeDenominators.pullbackQCartier hnormB q (moduliWeilPart C H Δ a)
          (moduliWeilPart_isQCartier_of_discriminant C H Δ a hΔ) := by
  rw [OAI.RelativeDenominators.pullbackQCartier_add hnormB q
    (OAI.RelativeDenominators.isQCartier_add (rationalCartierWeilDivisor_isQCartier C) hΔ)
    (moduliWeilPart_isQCartier_of_discriminant C H Δ a hΔ),
    OAI.RelativeDenominators.pullbackQCartier_add hnormB q
      (rationalCartierWeilDivisor_isQCartier C) hΔ,
    rationalCartierWeilDivisor_pullback]


variable {K : Type u} [Field K] [CharZero K] {n k : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [IsIntegral Y] [IsNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- Construct the same actual SNC base, Stein source, finite discriminant and sub-klt
base pair together with the individual moduli Cartier multiple and the actual three-part
pullback relation from the original arbitrary Cartier presentation. -/
theorem exists_compatible_snc_discriminant_moduli_cartier_models
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
                            (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ) := by
  obtain ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
      hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
      T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
      hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
      q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
      hQΔ, m, hm, CΔ, hCΔ, hkltB⟩ :=
    exists_compatible_stein_snc_discriminant_support_models
      g hnormX hnormY happ cY c f d hd D heff hklt
  let M := moduliWeilPart (smoothCanonicalDivisor cB) (cartierPullback S.composite H)
    Δ ((s : ℚ) / (d : ℚ))
  have hQM := moduliWeilPart_isQCartier_of_discriminant (smoothCanonicalDivisor cB)
    (cartierPullback S.composite H) Δ ((s : ℚ) / (d : ℚ)) hQΔ
  obtain ⟨ℓ, hℓ, CM, hCM⟩ := moduliWeilPart_exists_actual_cartier_multiple hnormB
    (smoothCanonicalDivisor cB) (cartierPullback S.composite H) Δ ((s : ℚ) / (d : ℚ)) hQΔ
  have hQ := moduliWeilPart_combination_isQCartier (smoothCanonicalDivisor cB)
    (cartierPullback S.composite H) Δ ((s : ℚ) / (d : ℚ))
  have hpull := moduliWeilPart_combination_pullback hnormB q (smoothCanonicalDivisor cB)
    (cartierPullback S.composite H) Δ ((s : ℚ) / (d : ℚ))
  have hseparate := moduliWeilPart_pullback_separate hnormB q (smoothCanonicalDivisor cB)
    (cartierPullback S.composite H) Δ ((s : ℚ) / (d : ℚ)) hQΔ
  have hlinear := crepant_canonical_boundary_moduli_linear_equivalence
    π g S.composite q hq hπ hnormB c f cT D H (smoothCanonicalDivisor cB) Δ d
    (by omega) s ψ hD
  exact ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, rfl, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear⟩

end MixedFujita
