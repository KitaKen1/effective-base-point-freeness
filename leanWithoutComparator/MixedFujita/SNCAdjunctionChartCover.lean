/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCStratumIntegralNeighbourhoods

/-! 元幾何だけを持つ実SNC随伴チャートと全点被覆。 check-292：実SNC閉層の各点が元の全成分閉包に属することを実イデアル台の反変性から証明し、元IsSNCFamilyだけから全選択成分に座標の付くチャートと、非整・非連結にも対応する実閉層全体の残余エタール被覆を内部構成。任意affine細分でも元SNC条件が保たれることを証明し、元有効Cartier因子の実局所方程式を任意の指定近傍内の同じSNCチャートに内部供給。元滑らかなNoetherian SNCモデルから、既存正則成分APIで各点を通る実開閉整成分、その周囲開持ち上げ、元空間への実閉埋込みを構成し、その成分内の実整切断近傍と元Cartier方程式を同時供給。元幾何だけを持つSNCAdjunctionChartと、291の内部残余座標を使う実切断チャートを定義し、これらが実閉層全体を覆うことを証明。成分上への標準層同型の移送・重なり一致・大域SNC随伴と数値随伴は残る。 -/

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


/-- A local SNC adjunction chart contains ORIGINAL geometric data only.
Target coordinates, residues, canonical-frame units and local isomorphisms
are internally constructed from these fields. -/
structure SNCAdjunctionChart (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {m r : ℕ}
    (ξ : Fin m → X) (E : Fin m → CartierDivisor X) where
  ambient : EtaleChart K X (m + r)
  selected : Fin m → Fin (m + r)
  snc : IsSNCChart ambient ξ (fun i => some (selected i))
  equation : Fin m → Γ(X, ambient.U)
  equation_ne_zero : ∀ i, equation i ≠ 0
  equation_spec : ∀ i, rationalUnitClass X ambient.U
    (Additive.ofMul (regularEquationRationalUnit X ambient.U (equation i) (equation_ne_zero i))) =
      E i |_ ambient.U
  cutNonempty : Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ ambient.U)


/-- The ACTUAL cut chart uses the internally constructed residual etale coordinates. -/
noncomputable def sncAdjunctionCutChart
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} {ξ : Fin m → X} {E : Fin m → CartierDivisor X}
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (c : SNCAdjunctionChart K (r := r) ξ E) :
    EtaleChart K (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme r where
  U := (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.ambient.U
  isAffine := c.ambient.isAffine.preimage _
  nonempty := c.cutNonempty
  coords := sncStratumEtaleCoordinates c.ambient ξ c.selected c.snc
  formallyEtale := sncStratumEtaleCoordinates_formallyEtale c.ambient ξ c.selected c.snc


/-- At EVERY point the original SNC family and effective Cartier divisors
construct a genuine adjunction chart; no equation/coordinate atlas certificate. -/
theorem exists_sncAdjunctionChart_at
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    ∃ c : SNCAdjunctionChart K (r := r) ξ E, y ∈ (sncAdjunctionCutChart c).U := by
  obtain ⟨c, τ, g, hg, hp, _hO, hc, hEq⟩ := snc_stratum_exists_cartier_equation_chart_at
    ξ hsnc E hE y ⊤ (by trivial)
  let d : SNCAdjunctionChart K (r := r) ξ E :=
    { ambient := c, selected := τ, snc := hc, equation := g,
      equation_ne_zero := hg, equation_spec := hEq, cutNonempty := ⟨⟨y, hp⟩⟩ }
  exact ⟨d, hp⟩


/-- ALL genuine SNC adjunction charts cover the ACTUAL whole stratum,
including a disconnected/nonintegral stratum. Compatibility is not assumed. -/
theorem sncAdjunctionChart_cover
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    iSup (fun c : SNCAdjunctionChart K (r := r) ξ E => (sncAdjunctionCutChart c).U) = ⊤ := by
  apply top_unique
  intro y _hy
  obtain ⟨c, hc⟩ := exists_sncAdjunctionChart_at ξ hsnc E hE y
  exact Opens.mem_iSup.mpr ⟨c, hc⟩

end MixedFujita
