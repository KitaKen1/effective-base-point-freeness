/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.QuasicoherentImageIdealSheaf
public import MixedFujita.CanonicalImageIdealNonvanishing
public import MixedFujita.ProperClosedImmersionDimension
public import MixedFujita.CohomologyOneSectionLifting

/-! 実像イデアル商の非零単位・非空閉部分スキーム・次元降下。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

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


/-- A unit outside the global image of an actual module monomorphism gives a
specific NONZERO global cokernel section, without ANY H1 or vanishing assumption. -/
theorem cokernel_unit_section_ne_zero_of_one_not_in_global_range
    {X : Scheme.{u}} (M : X.Modules) (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (h : ¬ ∃ s : Γ(M, ⊤), Scheme.Modules.Hom.app j ⊤ s = (1 : Γ(X, ⊤))) :
    Scheme.Modules.Hom.app (cokernel.π j) ⊤ (1 : Γ(X, ⊤)) ≠ 0 := by
  intro hz
  have hseq : (ShortComplex.cokernelSequence j).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact j) inferInstance inferInstance
  exact h ((Scheme.Modules.exact_sections hseq (1 : Γ(X, ⊤))).mp hz)


/-- The actual image ideal is zero exactly when the original quasicoherent module map
is zero; no invertibility or generic-rank input is required. -/
theorem quasicoherentModuleImageIdealSheaf_eq_bot_iff_map_zero
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    quasicoherentModuleImageIdealSheaf M j = ⊥ ↔ j = 0 := by
  constructor
  · intro h
    apply moduleHom_ext_affine
    intro U
    ext s
    have hm : Scheme.Modules.Hom.app j U.1 s ∈
        (quasicoherentModuleImageIdealSheaf M j).ideal U := ⟨s, rfl⟩
    rw [h, Scheme.IdealSheafData.ideal_bot] at hm
    exact hm
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    apply SetLike.coe_injective
    ext a
    change (∃ s : Γ(M, U.1), Scheme.Modules.Hom.app j U.1 s = a) ↔ a = 0
    rw [h]
    simp [eq_comm]


/-- Failure of the global unit to lift gives a NONZERO canonical section of the
actual image-ideal quotient, without any vanishing assumption. -/
theorem quasicoherentImageIdeal_unit_quotient_section_ne_zero
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (h : ¬ ∃ s : Γ(M, ⊤), Scheme.Modules.Hom.app j ⊤ s = (1 : Γ(X, ⊤))) :
    Scheme.Modules.Hom.app
      (schemeUnitToPushforwardUnit (quasicoherentModuleImageIdealSheaf M j).subschemeι) ⊤
        (1 : Γ(X, ⊤)) ≠ 0 := by
  intro hz
  exact h ((Scheme.Modules.exact_sections (quasicoherentImageIdealShortComplex_shortExact j)
    (1 : Γ(X, ⊤))).mp hz)


/-- The actual closed image-ideal subscheme is nonempty when the global unit does
not lift. No reducedness, integrality or local-support witness is imposed on this subscheme. -/
theorem quasicoherentImageIdeal_subscheme_nonempty_of_unit_not_in_range
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (h : ¬ ∃ s : Γ(M, ⊤), Scheme.Modules.Hom.app j ⊤ s = (1 : Γ(X, ⊤))) :
    Nonempty (quasicoherentModuleImageIdealSheaf M j).subscheme := by
  let I := quasicoherentModuleImageIdealSheaf M j
  have hn := quasicoherentImageIdeal_unit_quotient_section_ne_zero M j h
  by_contra hempty
  let : IsEmpty I.subscheme := not_nonempty_iff.mp hempty
  have hbot : I.subschemeι ⁻¹ᵁ ⊤ = ⊥ := by
    ext x
    exact isEmptyElim x
  let : Subsingleton Γ(SheafOfModules.unit I.subscheme.ringCatSheaf, I.subschemeι ⁻¹ᵁ ⊤) :=
    abelianSheaf_empty_sections_subsingleton
      ((SheafOfModules.toSheaf I.subscheme.ringCatSheaf).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) hbot
  apply hn
  change (_ : Γ(SheafOfModules.unit I.subscheme.ringCatSheaf, I.subschemeι ⁻¹ᵁ ⊤)) = 0
  exact Subsingleton.elim _ _


/-- A nonzero actual image ideal on an integral source cuts out a proper lower-dimensional
closed subscheme. Nilpotents and embedded components in the closed subscheme are allowed. -/
theorem quasicoherentImageIdeal_subscheme_dimension_le_predecessor
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) [M.IsQuasicoherent]
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (hj : j ≠ 0)
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ)) :
    topologicalKrullDim (quasicoherentModuleImageIdealSheaf M j).subscheme ≤ n := by
  let I := quasicoherentModuleImageIdealSheaf M j
  have hI : I ≠ ⊥ := fun h => hj ((quasicoherentModuleImageIdealSheaf_eq_bot_iff_map_zero M j).mp h)
  apply properClosedImmersion_topologicalKrullDim_le_predecessor I.subschemeι ?_ n hdim
  rw [Scheme.IdealSheafData.range_subschemeι]
  intro hs
  apply integral_genericPoint_notMem_support_of_ideal_ne_bot I hI
  rw [hs]
  trivial

end MixedFujita
