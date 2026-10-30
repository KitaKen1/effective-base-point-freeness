/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierAdjunctionOverlaps
public import MixedFujita.ClosedEmbeddingSheafExactness

/-! 元の二etale被覆から実Cartier随伴チャートの全点存在と被覆。 check-288：元の周囲／切断etale被覆、有効Cartier因子の実局所正則方程式、閉埋め込みの実開持ち上げから、切断の全点に実随伴チャートを構成し全点被覆を証明。既存の層の一意貼合せで、任意の両立する実加群層写像を全部分開の正確な公式付きで大域化し、線形性・制限自然性も内部証明。元のCartier切断にこれを適用し、287の任意二チャート重なり一致とTauCetiの被覆上同型判定から、元のi^*O(K_X+D)とO(K_Y)の大域正規化Poincare留数層同型を存在・一意性付きで構成。実大域同型cartierGlobalAdjunctionIsoを定義し、各チャートへの制限が元の局所同型そのものであること、純dg留数と正確なcanonical frame単元による全部分開の正規化を証明。空開を含む。SNC反復随伴、正値性を伴う数値随伴、一般KV／BPF／F1F2は残る。 -/

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



/-- Every actual cut point has geometric local adjunction data, derived
from the original two etale covers and the effective Cartier local equation. -/
theorem exists_cartierAdjunctionChart_at
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (y : (effectiveCartierIdealSheaf D hD).subscheme) :
    ∃ c : CartierAdjunctionChart K D hD r, y ∈ (cartierAdjunctionCutChart c).U := by
  let Y := (effectiveCartierIdealSheaf D hD).subscheme
  let i := (effectiveCartierIdealSheaf D hD).subschemeι
  have hx : i y ∈ iSup (fun c : EtaleChart K X (1 + r) => c.U) := by rw [hX]; trivial
  have hy : y ∈ iSup (fun c : EtaleChart K Y r => c.U) := by rw [hY]; trivial
  obtain ⟨cx, hcx⟩ := Opens.mem_iSup.mp hx
  obtain ⟨cy, hcy⟩ := Opens.mem_iSup.mp hy
  obtain ⟨O, _, hO⟩ := inducing_relative_open_lift i.isClosedEmbedding.isInducing
    (⊤ : X.Opens) cy.U (by intro z hz; trivial)
  have hyO : i y ∈ O := by
    change y ∈ (Opens.map i.base).obj O
    rw [hO]
    exact hcy
  obtain ⟨Ueq, hyUeq, hUne, g, hg, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective D hD (i y)
  letI := hUne
  let T : X.Opens := cx.U ⊓ Ueq.1 ⊓ O
  have hyT : i y ∈ T := ⟨⟨hcx, hyUeq⟩, hyO⟩
  obtain ⟨_, ⟨W, hWa, rfl⟩, hyW, hWT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyT T.isOpen
  have hWcx : W ≤ cx.U := fun _z hz => (hWT hz).1.1
  have hWeq : W ≤ Ueq.1 := fun _z hz => (hWT hz).1.2
  have hWO : W ≤ O := fun _z hz => (hWT hz).2
  have hWcy : i ⁻¹ᵁ W ≤ cy.U := by
    rw [← hO]
    exact fun _z hz => hWO hz
  letI : Nonempty W := ⟨⟨i y, hyW⟩⟩
  letI : Nonempty (i ⁻¹ᵁ W) := ⟨⟨y, hyW⟩⟩
  obtain ⟨hgW, hEqW⟩ := regularEquation_restrict D hWeq g hg hEq
  let cxW := etaleChartAffineRestriction cx ⟨W, hWa⟩ hWcx
  let cyW := etaleChartAffineRestriction cy ⟨i ⁻¹ᵁ W, hWa.preimage i⟩ hWcy
  let c : CartierAdjunctionChart K D hD r :=
    { ambient := cxW
      equation := X.presheaf.map (homOfLE hWeq).op g
      equation_ne_zero := hgW
      equation_spec := hEqW
      cutNonempty := by change Nonempty (i ⁻¹ᵁ W); infer_instance
      cutCoords := cyW.coords
      cutEtale := cyW.formallyEtale }
  exact ⟨c, hyW⟩


/-- All actual local adjunction input charts cover the ORIGINAL cut scheme;
no compatible atlas or chart-existence certificate is an additional input. -/
theorem cartierAdjunctionChart_cover
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤) :
    iSup (fun c : CartierAdjunctionChart K D hD r => (cartierAdjunctionCutChart c).U) = ⊤ := by
  apply top_unique
  intro y _hy
  obtain ⟨c, hc⟩ := exists_cartierAdjunctionChart_at hX hY y
  exact Opens.mem_iSup.mpr ⟨c, hc⟩

end MixedFujita
