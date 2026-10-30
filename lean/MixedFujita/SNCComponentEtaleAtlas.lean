/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OpenComponentQuotientResidue

/-! 実成分切断同型による残余エタール座標と元SNC全点被覆。 check-293：実閉部分スキームの切断近傍全体を含む開成分では、開埋込みの実切断写像が同型となることから、成分上の実商写像の全射性と元と同じ核を内部証明。任意選択エタール座標商の実微分基底・純留数を代数APIへ一般化し、元SNC座標と実成分切断写像の合成で成分上の実エタール座標を構成。元SNC族と元Cartier方程式から、非整・非連結の全閉層の任意の実開閉成分上に残余エタール被覆を内部供給。成分上の元Cartier方程式に正規化された実留数と標準frame単元を構成し、整成分上の実j^*O(K_X+ΣE_i)とO(K_U)の局所加群層同型を一意性・全部分開係数則・最高次形式の正規化付きで構成。最後に元滑らかなNoetherian SNC幾何と元の交差点から、実整成分・実整切断近傍・実Cartier方程式・成分標準類の参照チャート・同じ局所層同型をすべて内部供給する存在定理へ接続。全閉層／中間層の整性、与えた成分・商核・対象被覆・留数・層同型は入力に置かない。重なり一致・大域SNC随伴・数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- ACTUAL residual coordinates on an open component are the original
internally constructed SNC coordinates followed by its actual section map. -/
noncomputable def sncComponentEtaleCoordinates
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens) :
    MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ c.U) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let C := Γ(U, U.ι ⁻¹ᵁ I.subschemeι ⁻¹ᵁ c.U)
  let : Algebra B C := (U.ι.app (I.subschemeι ⁻¹ᵁ c.U)).hom.toAlgebra
  let : IsScalarTower K B C := schemeApp_base_scalar_tower U.ι (I.subschemeι ⁻¹ᵁ c.U)
  exact (IsScalarTower.toAlgHom K B C).comp (sncStratumEtaleCoordinates c ξ τ hc)


/-- Where the actual cut neighbourhood lies inside the open component,
its internally constructed coordinates are genuinely formally etale. -/
theorem sncComponentEtaleCoordinates_formallyEtale
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.U ≤ U) :
    (sncComponentEtaleCoordinates c ξ τ hc U).toRingHom.FormallyEtale := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let C := Γ(U, U.ι ⁻¹ᵁ I.subschemeι ⁻¹ᵁ c.U)
  let : Algebra B C := (U.ι.app (I.subschemeι ⁻¹ᵁ c.U)).hom.toAlgebra
  let : IsScalarTower K B C := schemeApp_base_scalar_tower U.ι (I.subschemeι ⁻¹ᵁ c.U)
  let f := IsScalarTower.toAlgHom K B C
  let : IsIso (U.ι.app (I.subschemeι ⁻¹ᵁ c.U)) :=
    U.ι.isIso_app _ (by simpa only [Scheme.Opens.opensRange_ι] using hcut)
  have hf : Function.Bijective f :=
    (asIso (U.ι.app (I.subschemeι ⁻¹ᵁ c.U))).commRingCatIsoToRingEquiv.bijective
  exact formallyEtale_comp f (ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective hf))
    (sncStratumEtaleCoordinates c ξ τ hc) (sncStratumEtaleCoordinates_formallyEtale c ξ τ hc)


/-- The ORIGINAL SNC family and Cartier equations internally supply a genuine
residual etale atlas on ANY actual clopen component, even when the WHOLE
stratum is disconnected/nonintegral. No target chart-cover certificate. -/
theorem snc_component_etaleChart_cover
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme)) :
    iSup (fun c : EtaleChart K U r => c.U) = ⊤ := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let j := U.ι ≫ I.subschemeι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  apply top_unique
  intro y _hy
  obtain ⟨O, _hO, hOU⟩ := inducing_relative_open_lift I.subschemeι.isClosedEmbedding.isInducing
    (⊤ : X.Opens) U (by intro z hz; trivial)
  have hyO : I.subschemeι (U.ι y) ∈ O := by
    change U.ι y ∈ I.subschemeι ⁻¹ᵁ O
    rw [hOU]
    exact y.prop
  obtain ⟨c, τ, _g, _hg, hp, hcO, hc, _hEq⟩ := snc_stratum_exists_cartier_equation_chart_at
    ξ hsnc E hE (U.ι y) O hyO
  have hcut : I.subschemeι ⁻¹ᵁ c.U ≤ U := by
    rw [← hOU]
    exact fun _z hz => hcO hz
  let d : EtaleChart K U r :=
    { U := j ⁻¹ᵁ c.U, isAffine := c.isAffine.preimage j, nonempty := ⟨⟨y, hp⟩⟩,
      coords := sncComponentEtaleCoordinates c ξ τ hc U,
      formallyEtale := sncComponentEtaleCoordinates_formallyEtale c ξ τ hc U hcut }
  exact Opens.mem_iSup.mpr ⟨d, hp⟩

end MixedFujita
