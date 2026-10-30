/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdjunctionOverlaps

/-! 元SNC幾何から実整成分の一意な大域正規化随伴。 check-296：元幾何のみから選択したSNC整成分の実局所標準層同型について、周囲・内部対象座標変更と全Cartier方程式変更からの独立性を証明。任意の対象エタール座標と独立な純正規化留数・frame単元でも同じ選択層同型を表すことを証明し、内部対象座標の選択が制限で一致するとの仮定を除去。元方程式の実affine制限チャートを構成し、選択済み実層写像の任意affine制限一致を空開を含む全部分開で証明。共通affine細分での両座標・全方程式比較と、一般点での一つの共通affine近傍・実線束の制限単射性から、任意二チャート重なりの全部分開で実写像の一致を証明。内部全点被覆と既存の加群層貼合せ・被覆上同型判定により、元j^*O(K_X+ΣE_i)とO(K_U)の一意な大域正規化随伴層同型を構成し、全部分開の局所写像との一致・各局所純留数と正確なframe単元による正規化を証明。最後に元smooth Noetherian SNC幾何の任意の交差点から、実整開閉成分・成分標準類参照チャート・同じ一意な大域随伴層同型まで内部供給する存在定理へ接続。全閉層・中間層の整性や、与えた成分・対象被覆・留数・局所同型・重なり証明・大域同型を追加仮定にしない。法線成分順序は固定。数値随伴・正値性・一般KV・F1F2は残る。 -/

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




/-- ORIGINAL SNC/Cartier geometry yields the unique GLOBAL normalized
adjunction of the actual sheaves j^*O(K_X+SUM E_i) and O(K_U) on a fixed
integral clopen component. All local maps, overlap laws and cover are internal. -/
theorem snc_component_global_adjunction_iso
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r) :
    let i := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let M := (Scheme.Modules.pullback i).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
    let N := (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)).sheaf
    ∃! Φ : M ≅ N, ∀ (c : SNCComponentAdjunctionChart K (r := r) ξ E U) (V : U.toScheme.Opens)
      (hVc : V ≤ (sncComponentAdjunctionCutChart ξ E U hclosed c).U) (s : Γ(M, V)),
      Scheme.Modules.Hom.app Φ.hom V s =
        (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
          (op (Over.mk (homOfLE hVc))) s := by
  let Y : Scheme := U
  let i := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
  let M := (Scheme.Modules.pullback i).obj
    (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
  let N := (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)).sheaf
  let Vchart (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :=
    (sncComponentAdjunctionCutChart ξ E U hclosed c).U
  have hcover : iSup Vchart = ⊤ := sncComponentAdjunctionChart_cover ξ hsnc E hE U hclosed
  obtain ⟨F, hF⟩ := exists_moduleHom_of_compatible_over_cover M N Vchart hcover
    (fun c => (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom)
      (fun c d V hVc hVd s =>
        sncComponentAdjunctionLocalIso_overlap_apply ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c d V hVc hVd s)
  have hover (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
      F.over (Vchart c) = (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom := by
    ext V s
    exact hF c V.unop.left V.unop.hom.le s
  have hIso : IsIso F := by
    apply SheafOfModules.isIso_of_coversTop
      ((Opens.coversTop_iff (Y : Type u) Vchart).mpr (IsOpenCover.mk hcover))
    intro c
    rw [hover c]
    infer_instance
  letI := hIso
  dsimp only
  refine ⟨asIso F, hF, ?_⟩
  intro Ψ hΨ
  apply Iso.ext
  ext T s
  let V (c : SNCComponentAdjunctionChart K (r := r) ξ E U) : Y.Opens := T ⊓ Vchart c
  have hTcover : T ≤ iSup V := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_sncComponentAdjunctionChart_at ξ hsnc E hE U hclosed x
    exact Opens.mem_iSup.mpr ⟨c, hx, hc⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Y)
    V T (fun _c => homOfLE inf_le_left) hTcover
  intro c
  let j : V c ⟶ T := homOfLE inf_le_left
  have hnΨ := Ψ.hom.mapPresheaf.naturality_apply j.op s
  have hnF := F.mapPresheaf.naturality_apply j.op s
  exact hnΨ.symm.trans ((hΨ c (V c) inf_le_right (M.presheaf.map j.op s)).trans
    ((hF c (V c) inf_le_right (M.presheaf.map j.op s)).symm.trans hnF))


/-- The actual global SNC component adjunction isomorphism. -/
noncomputable def sncComponentGlobalAdjunctionIso
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r) :
    ((Scheme.Modules.pullback (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf) ≅
        (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)).sheaf :=
  Classical.choose (snc_component_global_adjunction_iso ξ E U hclosed hsnc hE hI cX₀ hX cY₀)


/-- The global actual map equals the original chosen local map on ALL
subopens, including empty ones. -/
theorem sncComponentGlobalAdjunctionIso_apply
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r) :
    let i := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let M := (Scheme.Modules.pullback i).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
    ∀ (c : SNCComponentAdjunctionChart K (r := r) ξ E U) (V : U.toScheme.Opens)
      (hVc : V ≤ (sncComponentAdjunctionCutChart ξ E U hclosed c).U) (s : Γ(M, V)),
      Scheme.Modules.Hom.app (sncComponentGlobalAdjunctionIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀).hom V s =
        (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
          (op (Over.mk (homOfLE hVc))) s := by
  exact (Classical.choose_spec (snc_component_global_adjunction_iso ξ E U hclosed hsnc hE hI cX₀ hX cY₀)).1


/-- Restricting the global ACTUAL iso gives exactly the chosen local iso. -/
theorem sncComponentGlobalAdjunctionIso_over
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r)
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    (SheafOfModules.overFunctor U.toScheme.ringCatSheaf
        (sncComponentAdjunctionCutChart ξ E U hclosed c).U).mapIso
          (sncComponentGlobalAdjunctionIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀) =
      sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c := by
  apply Iso.ext
  ext V s
  exact sncComponentGlobalAdjunctionIso_apply ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c
    V.unop.left V.unop.hom.le s


/-- The global SNC component iso has the actual pure dg normalization and
exact canonical frame unit on every genuine original-data chart. -/
theorem sncComponentGlobalAdjunctionIso_residue_normalization
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r)
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    let A := Γ(X, c.1.ambient.U)
    let B := Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
    let : Algebra A B := ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι).app c.1.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.1.ambient.U
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun k : Fin m => KaehlerDifferential.D K A (c.1.equation k)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis c.1.ambient.coords c.1.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r
            (etaleCoordinateBasis (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
              (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale) ∧
      ((SheafOfModules.overFunctor U.toScheme.ringCatSheaf
          (sncComponentAdjunctionCutChart ξ E U hclosed c).U).mapIso
            (sncComponentGlobalAdjunctionIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀)) = moduleOverFrameWeightedIso _ _ (sncComponentAdjunctionCutChart ξ E U hclosed c).U
        (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX c) (sncComponentAdjunctionTargetFrame ξ E U hclosed cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed) c) a := by
  rw [sncComponentGlobalAdjunctionIso_over]
  exact sncComponentAdjunctionLocalIso_spec ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c


/-- At every point, ORIGINAL smooth Noetherian SNC geometry constructs an
actual integral clopen component, its canonical reference and a GLOBAL
normalized adjunction. No component/target atlas/residue/gluing certificate input. -/
theorem snc_original_geometry_exists_global_component_adjunction_at
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (p : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    ∃ (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
      (hint : IsIntegral U)
      (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
      (_hpU : p ∈ U) (cY₀ : EtaleChart K U r),
      let : IsIntegral U := hint
      ∃! Φ : ((Scheme.Modules.pullback (U.ι ≫
          (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)).obj
            (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf) ≅
              (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)).sheaf,
        ∀ (c : SNCComponentAdjunctionChart K (r := r) ξ E U) (V : U.toScheme.Opens)
          (hVc : V ≤ (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
          (s : Γ((Scheme.Modules.pullback (U.ι ≫
            (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)).obj
              (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf, V)),
          Scheme.Modules.Hom.app Φ.hom V s =
            (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
              (op (Over.mk (homOfLE hVc))) s := by
  obtain ⟨U, _W, hpU, _hpW, _hWU, hclosed, hint, _hj⟩ :=
    snc_stratum_exists_lifted_integral_component ξ hsnc p
  let : IsIntegral U := hint
  have hcover := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U r => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cY₀, _hcY₀⟩ := Opens.mem_iSup.mp hgeneric
  exact ⟨U, hint, hclosed, hpU, cY₀,
    snc_component_global_adjunction_iso ξ E U hclosed hsnc hE hI cX₀ hX cY₀⟩

end MixedFujita
