/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCNefBigPointwiseVanishing
public import MixedFujita.ProperKltAdjointVanishing
public import MixedFujita.ActualAcyclicCohomologyDescent

/-! For an effective klt pair on a proper normal variety, construct one smooth
projective SNC resolution and one effective exceptional roundup. Every nef-and-big
adjoint has all positive cohomology zero upstairs, with its ordinary pushforward
identified downstairs. Higher descent still explicitly requires affine-local
acyclicity for this initial resolution morphism. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The original proper klt hypotheses supply a single resolution and exceptional
roundup, ordinary pushforward for every Cartier twist, and every positive-degree
vanishing upstairs for nef-and-big adjoints. The remaining higher-descent input
is stated precisely as acyclicity on inverse images of affine opens. -/
theorem exists_klt_resolution_higher_vanishing_model
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n k X) (cX : EtaleChart k X n)
    (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D) (hklt : LogPairIsKlt cX fX d D) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (.of k)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (.of k)))
      (p : T ⟶ X) (_ : IsDominant p) (_ : p.IsOver (Spec (.of k))) (_ : IsProper p)
      (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := k) p))
      (cT : EtaleChart k T n) (r : ℕ) (ξ : Fin r → T) (J E : CartierDivisor T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily k n ξ ∧
      CartierIsAmpleProj k J ∧ E.IsEffective ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
        cartierCoefficient E t = 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E t =
        ⌈-((cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
          t : ℝ) / (d : ℝ))⌉) ∧
      (∀ P : CartierDivisor X, Nonempty
        (P.sheaf ≅ (Scheme.Modules.pushforward p).obj (cartierPullback p P + E).sheaf)) ∧
      ∀ P : CartierDivisor X, CartierIsNef k (d • P - D) → CartierIsBig k (d • P - D) →
        (∀ q : ℕ, 1 ≤ q →
          Subsingleton (Scheme.Modules.Cohomology (cartierPullback p P + E).sheaf q)) ∧
        ((∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
            Subsingleton ((cartierPullback p P + E).sheaf.H' (q + 1) (p ⁻¹ᵁ U))) →
          ∀ q : ℕ, 1 ≤ q → Subsingleton (Scheme.Modules.Cohomology P.sheaf q)) := by
  let : IsNoetherian X := properOverField_scheme_isNoetherian (K := k) (X := X)
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance⟩
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, J, hJ⟩ := exists_projective_snc_model_of_proper k cX fX d D
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : IsProper (T ↘ Spec (.of k)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let : Smooth (T ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := k) t
  obtain ⟨E, hE, hEc, hexc⟩ := exists_effective_exceptional_klt_boundary_roundup p hp
    hnorm hcov cX fX d hd D heff hklt cT ξ hinj hξ hsnc hsupp
  have hpush (P : CartierDivisor X) : Nonempty
      (P.sheaf ≅ (Scheme.Modules.pushforward p).obj (cartierPullback p P + E).sheaf) := by
    obtain ⟨aP⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant p P
    let a : ((Scheme.Modules.pullback p).obj P.sheaf ⊗ E.sheaf) ≅
        (cartierPullback p P + E).sheaf :=
      tensorIso aP (Iso.refl _) ≪≫ cartierTensorSheafIso _ _
    exact ⟨effectiveExceptionalCartierTwistedPushforwardIso hnorm hnormT p hp E hE hexc P ≪≫
      (Scheme.Modules.pushforward p).mapIso a⟩
  refine ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ, J, E,
    hinj, hξ, hsnc, hJ, hE, hexc, hEc, hpush, ?_⟩
  intro P hnef hbig
  let C := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  let fT := crepantPullbackFormUnit p hp cX fX cT
  let P₀ := cartierPullback p P - principalCartierDivisor T fT
  have hadj : d • (P₀ - smoothCanonicalDivisor cT) - C = cartierPullback p (d • P - D) := by
    have hrec := crepantBoundaryCartier_smooth_recombine p hp cX fX d D cT
    dsimp [P₀, C, fT]
    rw [cartierPullback_sub, cartierPullback_nsmul, ← hrec]
    module
  have hnefT : CartierIsNef k (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsNef_cartierPullback_of_dominant p hnef
  have hbigT : CartierIsBig k (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsBig_cartierPullback hnorm hnormT p hp
      ((etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim cX).symm) hbig
  have he : (P₀ + E) + principalCartierDivisor T fT = cartierPullback p P + E := by
    dsimp only [P₀]
    abel
  let e : (P₀ + E).sheaf ≅ (cartierPullback p P + E).sheaf :=
    (cartierSheafPrincipalShiftIso (P₀ + E) fT).symm ≪≫ eqToIso (congrArg CartierDivisor.sheaf he)
  have hvan (q : ℕ) (hq : 1 ≤ q) :
      Subsingleton (Scheme.Modules.Cohomology (cartierPullback p P + E).sheaf q) := by
    let : Subsingleton (Scheme.Modules.Cohomology (P₀ + E).sheaf q) :=
      signed_snc_roundup_nef_big_higher_vanishing_of_charZero k J hJ cT ξ hinj hξ hsnc
        C E P₀ d hd hsupp hEc hnefT hbigT q hq
    exact (actualCohomologyLinearEquivOfIso e q).symm.subsingleton
  refine ⟨hvan, fun hlocal q hq => ?_⟩
  obtain ⟨a⟩ := hpush P
  let := P.isInvertible_sheaf
  let : P.sheaf.IsQuasicoherent := invertibleModule_isQuasicoherent _
  exact (actual_cohomology_subsingleton_iff_of_acyclic_pushforward p _ P.sheaf a hlocal q).mp
    (hvan q hq)

end MixedFujita
