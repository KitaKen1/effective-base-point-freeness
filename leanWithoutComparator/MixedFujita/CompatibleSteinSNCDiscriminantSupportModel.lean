/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothSNCBaseSequence
public import MixedFujita.SNCSourceOverBaseSequence
public import MixedFujita.SNCWeilCartierMultiple
public import MixedFujita.ModifiedBaseDiscriminantWeilDivisor
public import MixedFujita.SmoothBaseBlowUpResolution
public import MixedFujita.SteinBirationalModelInvariance
public import MixedFujita.CompatibleSteinSNCModel

/-! Resolve the complement of an original threshold-one open on the base, compress
that sequence to one blow-up and construct the compatible SNC Stein source. The
actual new discriminant is supported on the base SNC family. It therefore has an
actual Cartier multiple and defines an all-model sub-klt base pair. Negative
coefficients are allowed; no moduli nefness, descent or effective base pair is asserted. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

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

/-- Construct the actual discriminant on one compatible SNC base and Stein source model,
with a Cartier multiple and its all-model sub-klt base pair. -/
theorem exists_compatible_stein_snc_discriminant_support_models
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)
    (cY : EtaleChart K Y k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d D) (hklt : LogPairIsKlt c f d D) :
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
                OAI.RelativeDenominators.IsQCartier S.last Δ ∧
                ∃ (m : ℕ), 0 < m ∧ ∃ CΔ : CartierDivisor S.last,
                  (∀ β : CodimensionOnePoint S.last,
                    (cartierCoefficient CΔ (β : S.last) : ℚ) = (m : ℚ) * Δ β) ∧
                  LogPairIsKlt cB 1 m
                    (m • (smoothCanonicalDivisor cB + principalCartierDivisor S.last 1) + CΔ) := by
  classical
  let hcov := normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnormX
  obtain ⟨V₀, hV₀, ht⟩ := exists_nonempty_open_canonicalBasePrimeKltThreshold_eq_one
    g hnormY hnormX hcov c f d hd D heff hklt
  have hgenV₀ : genericPoint Y ∈ V₀ := by
    apply ((genericPoint_spec Y).mem_open_set_iff V₀.isOpen).mpr
    obtain ⟨y, hy⟩ := hV₀
    exact ⟨y, Set.mem_univ y, hy⟩
  obtain ⟨I₀, hI₀, hη₀, -⟩ := exists_smooth_base_single_blowUp cY
  let W : Y.Opens := V₀ ⊓ I₀.support.compl
  let Z : Closeds Y := W.compl
  have hW : genericPoint Y ∈ W := ⟨hgenV₀, hη₀⟩
  have hZη : genericPoint Y ∉ (Z : Set Y) := by simpa [Z] using hW
  have hsing : Y.singularLocus ⊆ (Z : Set Y) := by
    intro y hy
    change y ∉ W
    intro hw
    exact hw.2 (by rw [hI₀]; exact hy)
  obtain ⟨S, hc, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
      hBft, hBqc, hBsep, cB, hρ, hisoZ, rB, ξB, hinjB, hcodB, hsncB, hnotZ⟩ :=
    exists_smooth_snc_base_sequence cY Z hZη hsing
  have hiso : IsIso (S.composite ∣_ W) := by
    have hZW : Z.compl = W := TopologicalSpace.Opens.compl_compl W
    exact Eq.mp (congrArg (fun U : Y.Opens => IsIso (S.composite ∣_ U)) hZW) hisoZ
  have hgood : ∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB →
      S.composite (β : S.last) ∈ W := by
    intro β hβ
    simpa [Z] using hnotZ β hβ
  have hBS : Smooth (S.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth k _
  have hnormB : ∀ b : S.last, IsIntegrallyClosed (S.last.presheaf.stalk b) :=
    fun b => smooth_stalk_isIntegrallyClosed (K := K) b
  obtain ⟨T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
      hTft, hTqc, hTsep, hπ, cT, rT, ξT, hinjT, hcodT, hsncT, hBT, hembT,
      q, hqdom, hqprop, hqover, hq⟩ :=
    exists_snc_source_model_over_base_sequence g S Z hc hZη c f d D
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  have hbT : ∀ i, cartierCoefficient
      (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) (ξT i) < (d : ℤ) :=
    fun i => logPairIsKlt_crepantBoundary_coefficient_lt π hπ c f d D hklt cT ⟨ξT i, hcodT i⟩
  have hqapp := stein_all_open_app_bijective_of_birational_square g π S.composite q
    hnormX hnormB (fun U => (happ U).2) hπ hρ hq
  have hqiso (V : S.last.Opens) : IsIso (q.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hqapp V)
  have hconnected := zariskiConnectednessStatement T S.last q hqiso
  let Δ := modifiedBaseCanonicalSubKltDiscriminantWeilDivisor π hπ g S.composite q hq W hW
    hnormY hnormX hnormB c f d hd D heff hklt cT
  have hΔ : ∀ β, Δ β = subKltBasePrimeDiscriminantCoefficients q hnormB cT
      (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β := fun β => rfl
  have hlt : ∀ β, Δ β < 1 := modifiedBaseCanonicalSubKltDiscriminantWeilDivisor_lt_one
    π hπ g S.composite q hq W hW hnormY hnormX hnormB c f d hd D heff hklt cT
  have hΔsupp : ∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB → Δ β = 0 := by
    intro β hβ
    have hβW : S.composite (β : S.last) ∈ W := hgood β hβ
    have hisostalk : IsIso (S.composite.stalkMap (β : S.last)) :=
      isIso_stalkMap_of_isIso_base_restrict S.composite W β hβW
    have hη : Order.coheight (S.composite (β : S.last)) = 1 :=
      (coheight_eq_of_stalkMap_bijective S.composite β
        (ConcreteCategory.bijective_of_isIso (S.composite.stalkMap (β : S.last)))).symm.trans β.property
    let η : CodimensionOnePoint Y := ⟨S.composite (β : S.last), hη⟩
    letI := hnormY (η : Y)
    have heq := modifiedBaseCanonicalSubKltDiscriminantWeilDivisor_eq_original
      π hπ g S.composite q hq W hW hnormY hnormX hnormB c f d hd D heff hklt cT η β rfl hβW
    change Δ β = _ at heq
    rw [heq]
    change 1 - canonicalBasePrimeKltThreshold g η hnormX hcov c f d hd D heff hklt = 0
    rw [ht η hβW.1, sub_self]
  have hQΔ := snc_rational_weil_isQCartier ξB hinjB hcodB hsncB Δ hΔsupp
  obtain ⟨m, hm, CΔ, hCΔ, hkltB⟩ :=
    exists_snc_rational_weil_sub_klt_pair cB ξB hinjB hcodB hsncB Δ hΔsupp hlt
  exact ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB⟩

end MixedFujita
