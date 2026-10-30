/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAdjunctionChartCover
public import MixedFujita.ModuleOverCoverGluing
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-! 元Cartier切断の一意な大域正規化Poincare留数層同型。 check-288：元の周囲／切断etale被覆、有効Cartier因子の実局所正則方程式、閉埋め込みの実開持ち上げから、切断の全点に実随伴チャートを構成し全点被覆を証明。既存の層の一意貼合せで、任意の両立する実加群層写像を全部分開の正確な公式付きで大域化し、線形性・制限自然性も内部証明。元のCartier切断にこれを適用し、287の任意二チャート重なり一致とTauCetiの被覆上同型判定から、元のi^*O(K_X+D)とO(K_Y)の大域正規化Poincare留数層同型を存在・一意性付きで構成。実大域同型cartierGlobalAdjunctionIsoを定義し、各チャートへの制限が元の局所同型そのものであること、純dg留数と正確なcanonical frame単元による全部分開の正規化を証明。空開を含む。SNC反復随伴、正値性を伴う数値随伴、一般KV／BPF／F1F2は残る。 -/

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

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {D : CartierDivisor X} {hD : D.IsEffective}
  [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))]
  [(effectiveCartierIdealSheaf D hD).subschemeι.IsOver (Spec (CommRingCat.of K))]
  [IsIntegral (effectiveCartierIdealSheaf D hD).subscheme] {r : ℕ}



/-- ORIGINAL Cartier-cut geometry and the two original etale atlases
construct the unique GLOBAL normalized Poincare residue isomorphism of the
ACTUAL sheaves i^*O(K_X+D) and O(K_Y). All charts, local isos, compatibility
and cover are internal; no residue map, compatible atlas or gluing is supplied. -/
theorem smooth_effectiveCartier_global_adjunction_iso
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤) :
    let Y := (effectiveCartierIdealSheaf D hD).subscheme
    let i := (effectiveCartierIdealSheaf D hD).subschemeι
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
    let N := (canonicalDivisor r cY₀ hY).sheaf
    ∃! Φ : M ≅ N, ∀ (c : CartierAdjunctionChart K D hD r) (V : Y.Opens)
      (hVc : V ≤ (cartierAdjunctionCutChart c).U) (s : Γ(M, V)),
      Scheme.Modules.Hom.app Φ.hom V s =
        (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val.app (op (Over.mk (homOfLE hVc))) s := by
  let Y := (effectiveCartierIdealSheaf D hD).subscheme
  let i := (effectiveCartierIdealSheaf D hD).subschemeι
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
  let N := (canonicalDivisor r cY₀ hY).sheaf
  let U (c : CartierAdjunctionChart K D hD r) := (cartierAdjunctionCutChart c).U
  have hU : iSup U = ⊤ := cartierAdjunctionChart_cover hX hY
  obtain ⟨F, hF⟩ := exists_moduleHom_of_compatible_over_cover M N U hU
    (fun c => (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom)
      (fun c d V hVc hVd s => cartierAdjunctionLocalIso_overlap_apply cX₀ hX cY₀ hY c d V hVc hVd s)
  have hover (c : CartierAdjunctionChart K D hD r) :
      F.over (U c) = (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom := by
    ext V s
    exact hF c V.unop.left V.unop.hom.le s
  have hIso : IsIso F := by
    apply SheafOfModules.isIso_of_coversTop ((Opens.coversTop_iff (Y : Type u) U).mpr (IsOpenCover.mk hU))
    intro c
    rw [hover c]
    infer_instance
  letI := hIso
  dsimp only
  refine ⟨asIso F, hF, ?_⟩
  intro Ψ hΨ
  apply Iso.ext
  ext T s
  let V (c : CartierAdjunctionChart K D hD r) : Y.Opens := T ⊓ U c
  have hcover : T ≤ iSup V := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_cartierAdjunctionChart_at hX hY x
    exact Opens.mem_iSup.mpr ⟨c, hx, hc⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Y)
    V T (fun _c => homOfLE inf_le_left) hcover
  intro c
  let j : V c ⟶ T := homOfLE inf_le_left
  have hnΨ := Ψ.hom.mapPresheaf.naturality_apply j.op s
  have hnF := F.mapPresheaf.naturality_apply j.op s
  exact hnΨ.symm.trans ((hΨ c (V c) inf_le_right (M.presheaf.map j.op s)).trans
    ((hF c (V c) inf_le_right (M.presheaf.map j.op s)).symm.trans hnF))


/-- The actual global canonical adjunction isomorphism with pure residue normalization. -/
noncomputable def cartierGlobalAdjunctionIso
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤) :
    ((Scheme.Modules.pullback (effectiveCartierIdealSheaf D hD).subschemeι).obj
        (canonicalDivisor (1 + r) cX₀ hX + D).sheaf) ≅
      (canonicalDivisor r cY₀ hY).sheaf :=
  Classical.choose (smooth_effectiveCartier_global_adjunction_iso (D := D) (hD := hD) cX₀ hX cY₀ hY)


/-- Its GLOBAL sheaf map has exactly the chosen normalized local residue
map on every subopen of every genuine geometric chart, including empty opens. -/
theorem cartierGlobalAdjunctionIso_apply
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤) :
    let Y := (effectiveCartierIdealSheaf D hD).subscheme
    let i := (effectiveCartierIdealSheaf D hD).subschemeι
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
∀ (c : CartierAdjunctionChart K D hD r) (V : Y.Opens)
      (hVc : V ≤ (cartierAdjunctionCutChart c).U) (s : Γ(M, V)),
      Scheme.Modules.Hom.app (cartierGlobalAdjunctionIso cX₀ hX cY₀ hY).hom V s =
        (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val.app (op (Over.mk (homOfLE hVc))) s := by
  exact (Classical.choose_spec (smooth_effectiveCartier_global_adjunction_iso (D := D) (hD := hD) cX₀ hX cY₀ hY)).1


/-- The restriction of the global ACTUAL sheaf iso is exactly the original
chosen local iso, not merely some unit multiple. -/
theorem cartierGlobalAdjunctionIso_over
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    (SheafOfModules.overFunctor (effectiveCartierIdealSheaf D hD).subscheme.ringCatSheaf
        (cartierAdjunctionCutChart c).U).mapIso (cartierGlobalAdjunctionIso cX₀ hX cY₀ hY) =
      cartierAdjunctionLocalIso cX₀ hX cY₀ hY c := by
  apply Iso.ext
  ext V s
  exact cartierGlobalAdjunctionIso_apply cX₀ hX cY₀ hY c V.unop.left V.unop.hom.le s


/-- The GLOBAL adjunction is normalized by the actual pure dg residue
and exact canonical-frame unit on every genuine chart and all its subopens. -/
theorem cartierGlobalAdjunctionIso_residue_normalization
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    let A := Γ(X, c.ambient.U)
    let B := Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U)
    let : Algebra A B := ((effectiveCartierIdealSheaf D hD).subschemeι.app c.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.ambient.U
    ∃ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A c.equation) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis c.ambient.coords c.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis c.cutCoords c.cutEtale) ∧
      ∀ (V : (effectiveCartierIdealSheaf D hD).subscheme.Opens)
        (hVc : V ≤ (cartierAdjunctionCutChart c).U)
        (s : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf D hD).subschemeι).obj
          (canonicalDivisor (1 + r) cX₀ hX + D).sheaf, V)),
        moduleOverFrameCoefficient (canonicalDivisor r cY₀ hY).sheaf
          (cartierAdjunctionCutChart c).U (cartierAdjunctionTargetFrame cY₀ hY c) V hVc
            (Scheme.Modules.Hom.app (cartierGlobalAdjunctionIso cX₀ hX cY₀ hY).hom V s) =
          (effectiveCartierIdealSheaf D hD).subscheme.presheaf.map (homOfLE hVc).op ↑a *
            moduleOverFrameCoefficient _ (cartierAdjunctionCutChart c).U
              (cartierAdjunctionSourceFrame cX₀ hX c) V hVc s := by
  letI := c.cutNonempty
  let A := Γ(X, c.ambient.U)
  let B := Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U)
  let : Algebra A B := ((effectiveCartierIdealSheaf D hD).subschemeι.app c.ambient.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.ambient.U
  obtain ⟨R, a, hR, ha, hΦ⟩ := cartierAdjunctionLocalIso_spec cX₀ hX cY₀ hY c
  dsimp only
  refine ⟨R, a, hR, ha, ?_⟩
  intro V hVc s
  rw [cartierGlobalAdjunctionIso_apply, hΦ]
  exact moduleOverFrameWeightedIso_coefficient _ _ _ _ _ a V hVc s

end MixedFujita
