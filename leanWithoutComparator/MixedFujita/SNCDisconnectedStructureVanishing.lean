/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentCodimension
public import MixedFujita.StalkBaseChangeOpenAssembly
public import MixedFujita.SmoothCentreModulePullbackVanishing
public import MixedFujita.HironakaPrincipalizingRound
public import Hironaka.Scheme.BlowUp.Glue.RestrictOpen

/-! Structure-sheaf relative vanishing for a single SNC-center blow-up,
allowing disconnected centers with different codimensions. The component
neighborhoods, dimensions and Cartesian squares are constructed internally.
This does not yet assemble the componentwise exceptional roundup twists. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000 in
theorem sncCentre_structure_allPoint_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] (hη : genericPoint X ∉ Z.support) (x : X) (q : ℕ) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Z.blowUp) (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' Z.blowUpπ (X.fromSpecStalk x) ∧
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Z.blowUp.ringCatSheaf)).toAbSheaf
        (q + 1)) := by
  classical
  by_cases hx : x ∈ Z.support
  · obtain ⟨U, c, hxU, hc, hcn, hZU, hdim, _⟩ :=
      sncCentre_exists_open_positive_codimension f n D Z hZ hη x hx
    let : Nonempty U := ⟨⟨x, hxU⟩⟩
    let ZU := Z.comap U.ι
    let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
    let : U.toScheme.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from U.ι]
      infer_instance⟩
    let : SmoothOfRelativeDimension n (U.ι ≫ f) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))
    have hsub : c - 1 + 1 = c := by omega
    let : SmoothOfRelativeDimension (n - ((c - 1) + 1)) (ZU.subschemeι ≫ (U.ι ≫ f)) := by
      simpa only [hsub] using hdim
    have hrn : c - 1 + 1 ≤ n := by omega
    have hηU : genericPoint U.toScheme ∉ ZU.support := by
      intro h
      have h' := (mem_support_comap_iff_apply Z U.ι _).mp h
      rw [genericPoint_eq_of_isOpenImmersion U.ι] at h'
      exact hη h'
    let := blowUp_isIntegral_of_genericPoint_notMem_support ZU hηU
    let := blowUp_isDominant_of_genericPoint_notMem_support ZU hηU
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian ZU
    let : IsProper ZU.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π ZU
    let : ZU.blowUp.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from ZU.blowUpπ]
      infer_instance⟩
    obtain ⟨E, hE, hEI⟩ := exists_effectiveCartier_of_invertibleIdeal
      ZU.exceptionalDivisor (Scheme.IdealSheafData.blowUp.isInvertible_comap_π ZU)
    let y : U := ⟨x, hxU⟩
    let := affineBlowUp_isIntegral_of_ne_bot (ZU.stalkIdeal y)
      (smoothCentre_stalkIdeal_ne_bot (U.ι ≫ f) n (c - 1) ZU hrn y)
    obtain ⟨τ, hτ, H, hv⟩ := smoothCentre_allPoint_local_exceptional_combination_vanish
      (U.ι ≫ f) n (c - 1) ZU hrn E hE hEI 0 0 0 (Nat.zero_le _)
      (by simp [cartierPullback_zero]) y
    let := hτ
    let a := Scheme.Hom.blowUpMap U.ι Z
    obtain ⟨s, hs⟩ := stalk_baseChange_paste_open U y
      (Scheme.IdealSheafData.blowUp.isPullback_restrictHom Z U) H
    let : Subsingleton (Scheme.Modules.Cohomology
        (0 : CartierDivisor (affineBlowUp (ZU.stalkIdeal y))).sheaf (q + 1)) := by
      simpa only [cartierPullback_zero] using hv q
    let : Subsingleton (Scheme.Modules.Cohomology
        (SheafOfModules.unit (affineBlowUp (ZU.stalkIdeal y)).ringCatSheaf) (q + 1)) :=
      (actualCohomologyLinearEquivOfIso (cartierZeroSheafIso _).symm (q + 1)).subsingleton
    refine ⟨_, τ ≫ a, s, hs, ?_⟩
    exact (actualCohomologyLinearEquivOfIso
      (Scheme.Modules.pullbackObjUnitIso' (τ ≫ a)) (q + 1)).subsingleton
  · obtain ⟨τ, H⟩ := exists_isPullback_fromSpecStalk Z x
    let := localBlowUp_isIso_off_center Z x hx
    let : IsAffine (affineBlowUp (Z.stalkIdeal x)) := IsAffine.of_isIso (affineBlowUp.π _)
    let : IsLocallyNoetherian (affineBlowUp (Z.stalkIdeal x)) :=
      LocallyOfFiniteType.isLocallyNoetherian (affineBlowUp.π _)
    let M := (Scheme.Modules.pullback τ).obj (SheafOfModules.unit Z.blowUp.ringCatSheaf)
    let := finiteAffine_cohomologyOn_vanish M (isAffineOpen_top _) (q + 1) (by omega)
    exact ⟨_, τ, affineBlowUp.π (Z.stalkIdeal x), H,
      (Modules.cohomologyOnTopIso M (q + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton⟩

theorem sncCentre_structure_relative_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] (hη : genericPoint X ∉ Z.support) :
    let M : Z.blowUp.Modules := SheafOfModules.unit Z.blowUp.ringCatSheaf
    (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ M (q + 1))) := by
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  dsimp only
  have h := sncCentre_structure_allPoint_vanishing f n D Z hZ hη
  exact ⟨fun _ hU q ↦ affine_open_preimage_cohomology_vanish_of_all_stalk_baseChange
      Z.blowUpπ _ q (fun x ↦ h x q) hU,
    fun q ↦ cohomologicalDirectImage_isZero_of_all_stalk_baseChange
      Z.blowUpπ _ q (fun x ↦ h x q)⟩

theorem sncCentre_structure_relative_vanishing_of_smooth
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] (hη : genericPoint X ∉ Z.support) :
    let M : Z.blowUp.Modules := SheafOfModules.unit Z.blowUp.ringCatSheaf
    (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ M (q + 1))) := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_of_preconnectedSpace f
  let := hn
  exact sncCentre_structure_relative_vanishing f n D Z hZ hη

end MixedFujita
