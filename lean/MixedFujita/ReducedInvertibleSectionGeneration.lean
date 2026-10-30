/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierDirectImageGeneration
public import Mathlib.AlgebraicGeometry.Properties

/-! 被約源の非零可逆切断から生成点と元Cartier基点除去。 See reports/check-246-lc-radical-reduced-fixed-subscheme-lifting.json for the verified scope. The actual lc kernel image ideal is radical and its nonempty lower-dimensional subscheme W is reduced. One fixed I and W works for all nef-big adjoints. Usual KV gives actual restriction section lifting; any nonzero restricted section removes an original basepoint on W. Usual KV itself, restricted-section nonvanishing and stable-base-locus placement remain unproved; no normal lc-center adjunction, klt BPF or full F1/F2 is claimed. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A nonzero actual global section of an invertible module on a REDUCED scheme
generates at some point. No irreducibility, properness, noetherianity or field is needed. -/
theorem nonzero_invertible_section_generates_somewhere_on_reduced
    {Y : Scheme.{u}} [IsReduced Y] (M : Y.Modules)
    (hM : SheafOfModules.isInvertible Y M) (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    ∃ (y : Y) (U : Y.Opens) (hy : y ∈ U)
      (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)),
      IsUnit (moduleOverFrameGlobalCoefficientGerm M U e y hy s) := by
  classical
  obtain ⟨ι, U, hU, e⟩ := SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  let d (i : ι) := moduleRestrictFrameOverIso M (U i) (Classical.choice (e i)).symm
  let a (i : ι) := moduleOverFrameCoefficient M (U i) (d i) (U i) le_rfl
    (M.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s)
  by_contra hn
  apply hs
  have ha (i : ι) : a i = 0 := by
    apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot
    apply Opens.ext
    apply Set.ext
    intro y
    change y ∈ Y.basicOpen (a i) ↔ False
    refine ⟨fun hy => ?_, False.elim⟩
    have hyU : y ∈ U i := (Y.basicOpen_le _) hy
    apply hn
    exact ⟨y, U i, hyU, d i, (Y.mem_basicOpen (a i) y hyU).mp hy⟩
  let F : TopCat.Sheaf AddCommGrpCat Y := (SheafOfModules.toSheaf Y.ringCatSheaf).obj M
  apply F.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top)
    (by rw [hU.iSup_eq_top]) s 0
  intro i
  rw [map_zero]
  apply (moduleOverFrameCoefficient M (U i) (d i) (U i) le_rfl).injective
  rw [map_zero]
  exact ha i


/-- Ordinary nonvanishing on a REDUCED actual source, combined with actual global
restriction surjectivity, gives an ORIGINAL Cartier generator at one image point. -/
theorem cartier_generator_at_image_of_nonzero_reduced_pullback_section
    {X Y : Scheme.{u}} [IsIntegral X] [IsReduced Y]
    (p : Y ⟶ X) (P : CartierDivisor X)
    (r : P.sheaf ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj P.sheaf))
    (hr : Function.Surjective (Scheme.Modules.Hom.app r ⊤))
    (t : Γ((Scheme.Modules.pullback p).obj P.sheaf, ⊤)) (ht : t ≠ 0) :
    ∃ y : Y, p y ∈ cartierGenerationOpen P := by
  obtain ⟨y, U, hy, e, hgen⟩ := nonzero_invertible_section_generates_somewhere_on_reduced
    ((Scheme.Modules.pullback p).obj P.sheaf) (cartierPullbackSheaf_isInvertible P p) t ht
  exact ⟨y, mem_cartierGenerationOpen_of_surjective_pushforward_generator p P _ r hr y U hy e t hgen⟩

end MixedFujita
