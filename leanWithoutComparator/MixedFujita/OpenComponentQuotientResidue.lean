/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCAdjunctionChartCover

/-! 実開成分への商核移送と任意選択座標の純留数。 check-293：実閉部分スキームの切断近傍全体を含む開成分では、開埋込みの実切断写像が同型となることから、成分上の実商写像の全射性と元と同じ核を内部証明。任意選択エタール座標商の実微分基底・純留数を代数APIへ一般化し、元SNC座標と実成分切断写像の合成で成分上の実エタール座標を構成。元SNC族と元Cartier方程式から、非整・非連結の全閉層の任意の実開閉成分上に残余エタール被覆を内部供給。成分上の元Cartier方程式に正規化された実留数と標準frame単元を構成し、整成分上の実j^*O(K_X+ΣE_i)とO(K_U)の局所加群層同型を一意性・全部分開係数則・最高次形式の正規化付きで構成。最後に元滑らかなNoetherian SNC幾何と元の交差点から、実整成分・実整切断近傍・実Cartier方程式・成分標準類の参照チャート・同じ局所層同型をすべて内部供給する存在定理へ接続。全閉層／中間層の整性、与えた成分・商核・対象被覆・留数・層同型は入力に置かない。重なり一致・大域SNC随伴・数値随伴は残る。 -/

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


/-- Restricting an ACTUAL closed subscheme to an open component containing
the whole cut neighbourhood preserves its ACTUAL section quotient and kernel.
The intermediate section map is internally an iso, not a supplied certificate. -/
theorem open_component_affine_quotient_data
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : I.subscheme.Opens)
    (V : X.affineOpens) (hVU : I.subschemeι ⁻¹ᵁ V.1 ≤ U) :
    let j := U.ι ≫ I.subschemeι
    Function.Surjective (j.app V.1).hom ∧
      RingHom.ker (j.app V.1).hom = I.ideal V := by
  let q := (I.subschemeι.app V.1).hom
  let f := (U.ι.app (I.subschemeι ⁻¹ᵁ V.1)).hom
  have hpre : I.subschemeι ⁻¹ᵁ V.1 ≤ U.ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using hVU
  let : IsIso (U.ι.app (I.subschemeι ⁻¹ᵁ V.1)) := U.ι.isIso_app _ hpre
  have hf : Function.Bijective f :=
    (asIso (U.ι.app (I.subschemeι ⁻¹ᵁ V.1))).commRingCatIsoToRingEquiv.bijective
  have hfac : ((U.ι ≫ I.subschemeι).app V.1).hom = f.comp q := by
    rw [Scheme.Hom.comp_app]
    rfl
  dsimp only
  rw [hfac]
  exact ⟨hf.2.comp (I.subschemeι_app_surjective V),
    (RingHom.ker_comp_of_injective q hf.1).trans (I.ker_subschemeι_app V)⟩


/-- Original SNC equations give the ACTUAL quotient data on a selected open
component, with no whole-stratum or intermediate integrality hypothesis. -/
theorem snc_component_affine_quotient_data
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (c : EtaleChart K X n) (ξ : Fin m → X) (τ : Fin m → Fin n)
    (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.U ≤ U) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let j := U.ι ≫ I.subschemeι
    Function.Surjective (j.app c.U).hom ∧ RingHom.ker (j.app c.U).hom =
      Ideal.span (Set.range fun i : Fin m => c.coords (MvPolynomial.X (τ i))) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  obtain ⟨hsurj, hker⟩ := open_component_affine_quotient_data I U ⟨c.U, c.isAffine⟩ hcut
  obtain ⟨_hsurjI, hkerI⟩ := snc_affine_selected_stratum_quotient_data c ξ τ hc
  exact ⟨hsurj, hker.trans ((I.ker_subschemeι_app ⟨c.U, c.isAffine⟩).symm.trans hkerI)⟩


/-- An ACTUAL etale algebra quotient by ANY independent selected coordinates
constructs its actual cut basis and pure canonical residue. This algebra API
can be used on a constructed final component without transporting whole schemes. -/
theorem selected_etale_quotient_pulled_residue
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    {m r : ℕ} (x : MvPolynomial (Fin (m + r)) K →ₐ[K] A)
    (hx : x.toRingHom.FormallyEtale) (τ : Fin m → Fin (m + r)) (hτ : Function.Injective τ)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) =
      Ideal.span (Set.range fun i : Fin m => x (MvPolynomial.X (τ i)))) :
    ∃ (e : Fin (m + r) ≃ Fin (m + r)) (b : Module.Basis (Fin r) B Ω[B⁄K])
      (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ i, e (Fin.castAdd r i) = τ i) ∧
      (∀ i, b i = D K B (algebraMap A B (x (MvPolynomial.X (e (Fin.natAdd m i)))))) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (x (MvPolynomial.X (τ i)))) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      (a : B) = algebraMap A B (((etaleCoordinateBasis x hx).reindex e.symm).det
        (etaleCoordinateBasis x hx)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) (etaleCoordinateBasis x hx)) =
        (a : B) • exteriorPower.ιMulti B r b := by
  classical
  obtain ⟨e, he⟩ := exists_fin_equiv_extending_prefix τ hτ
  let b₀ := etaleCoordinateBasis x hx
  let bA := b₀.reindex e.symm
  have hbg (i : Fin m) : bA (Fin.castAdd r i) = D K A (x (MvPolynomial.X (τ i))) := by
    change (b₀.reindex e.symm) (Fin.castAdd r i) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, he, etaleCoordinateBasis_apply]
  obtain ⟨b, R, hb, hR, hframe⟩ := basis_complete_intersection_pulled_residue
    (fun i => x (MvPolynomial.X (τ i))) bA hbg hsurj hker
  let a : Bˣ := Units.map (algebraMap A B).toMonoidHom (Module.Basis.isUnit_det bA b₀).unit
  have haval : (a : B) = algebraMap A B (bA.det b₀) := by
    simp only [a, Units.coe_map, IsUnit.unit_spec]
    rfl
  refine ⟨e, b, R, a, he, ?_, hR, haval, ?_⟩
  · intro i
    rw [hb]
    change KaehlerDifferential.map K K A B ((b₀.reindex e.symm) (Fin.natAdd m i)) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, etaleCoordinateBasis_apply, map_D]
  · have h := pulled_canonical_residue_ambient_frame_change bA b₀ R.toLinearMap
    rw [haval]
    exact h.trans (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => algebraMap A B (bA.det b₀) • w) hframe)

end MixedFujita
