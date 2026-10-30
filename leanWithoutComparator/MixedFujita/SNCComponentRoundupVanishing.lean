/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DominantCartierPullbackSheaf
public import MixedFujita.ComponentExceptionalModulePullback
public import MixedFujita.SNCComponentAdaptedCoordinates
public import MixedFujita.SNCDisconnectedStructureVanishing

/-! Vanishing for component-dependent exceptional corrections. Isolating an
actual centre component reduces the correction to one exceptional divisor;
the dimension witness is restricted from that same component. Ordinary
module pullback then gives all stalk squares and relative cohomology.
Check 579 removes the former signed-effective presentation restriction: the
Cartier twist on the base is arbitrary, using the dominant pullback sheaf theorem. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem centre_open_restriction_smoothOfRelativeDimension
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (d : ℕ)
    [SmoothOfRelativeDimension d (I.subschemeι ≫ f)] (U : X.Opens) :
    SmoothOfRelativeDimension d ((I.comap U.ι).subschemeι ≫ U.ι ≫ f) := by
  let j := (centreOpenRestrictionIso I U).hom ≫ (I.subschemeι ⁻¹ᵁ U).ι
  have he : j ≫ (I.subschemeι ≫ f) = (I.comap U.ι).subschemeι ≫ U.ι ≫ f := by
    dsimp only [j]
    rw [Category.assoc, ← morphismRestrict_ι_assoc,
      centreOpenRestrictionIso_hom_inclusion_assoc]
  rw [← he]
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (j ≫ (I.subschemeι ≫ f)))

theorem sncCentre_cartier_correction_allPoint_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (c : Z.componentFamily.ι → ℕ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ n ∧
      SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ f))
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ)
    (Q : CartierDivisor X)
    (C : CartierDivisor Z.blowUp) (j : Z.componentFamily.ι → ℕ)
    (hj : ∀ i, j i ≤ c i - 1)
    (hC : C = cartierPullback Z.blowUpπ Q + ∑ i, j i • E i)
    (x : X) (q : ℕ) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Z.blowUp) (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' Z.blowUpπ (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj C.sheaf).toAbSheaf (q + 1)) := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := C.isInvertible_sheaf
  let := invertibleModule_isQuasicoherent C.sheaf
  by_cases hx : x ∈ Z.support
  · obtain ⟨i, hxi⟩ := regularCentre_exists_component_through Z (HasSncWith.isRegular f hZ) x hx
    obtain ⟨U, hiU, hother, hZU⟩ :=
      regularCentre_exists_component_isolating_open Z (HasSncWith.isRegular f hZ) i
    have hxU : x ∈ U := hiU hxi
    let : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : IsDominant U.ι := flat_nonempty_isDominant U.ι
    let ZU := Z.comap U.ι
    let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
    let : U.toScheme.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from U.ι]
      infer_instance⟩
    let : SmoothOfRelativeDimension n (U.ι ≫ f) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))
    let := (hc i).2.2
    have hsub : c i - 1 + 1 = c i := by have := (hc i).1; omega
    let : SmoothOfRelativeDimension (n - ((c i - 1) + 1)) (ZU.subschemeι ≫ (U.ι ≫ f)) := by
      dsimp only [ZU]
      rw [hZU, hsub]
      exact centre_open_restriction_smoothOfRelativeDimension f (Z.componentFamily.component i) _ U
    have hrn : c i - 1 + 1 ≤ n := by have := (hc i).2.1; omega
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
    obtain ⟨E', hE', hE'I⟩ := exists_effectiveCartier_of_invertibleIdeal
      ZU.exceptionalDivisor (Scheme.IdealSheafData.blowUp.isInvertible_comap_π ZU)
    let aU := Scheme.Hom.blowUpMap U.ι Z
    have Hopen := Scheme.IdealSheafData.blowUp.isPullback_restrictHom Z U
    let : IsOpenImmersion aU :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback Hopen.flip inferInstance
    let : IsDominant aU := flat_nonempty_isDominant aU
    have hlocalC := (component_exceptional_decomposition_pullback_square
      Z.blowUpπ ZU.blowUpπ U.ι aU Hopen.w Z.componentFamily.component i hother
      E hE hEI E' hE' (by rw [← hZU]; exact hE'I)
      Q C j hC).2.2
    let y : U := ⟨x, hxU⟩
    let := affineBlowUp_isIntegral_of_ne_bot (ZU.stalkIdeal y)
      (smoothCentre_stalkIdeal_ne_bot (U.ι ≫ f) n (c i - 1) ZU hrn y)
    obtain ⟨τ, hτ, H, hv⟩ := smoothCentre_allPoint_local_exceptional_combination_vanish
      (U.ι ≫ f) n (c i - 1) ZU hrn E' hE' hE'I
      (cartierPullback U.ι Q) (cartierPullback aU C) (j i) (hj i) hlocalC y
    let := hτ
    obtain ⟨s, hs⟩ := stalk_baseChange_paste_open U y Hopen H
    obtain ⟨e⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant (τ ≫ aU) C
    let : Subsingleton (Scheme.Modules.Cohomology (cartierPullback (τ ≫ aU) C).sheaf (q + 1)) := by
      simpa only [cartierPullback_comp] using hv q
    exact ⟨_, τ ≫ aU, s, hs, (actualCohomologyLinearEquivOfIso e (q + 1)).subsingleton⟩
  · obtain ⟨τ, H⟩ := exists_isPullback_fromSpecStalk Z x
    let := localBlowUp_isIso_off_center Z x hx
    let : IsAffine (affineBlowUp (Z.stalkIdeal x)) := IsAffine.of_isIso (affineBlowUp.π _)
    let : IsLocallyNoetherian (affineBlowUp (Z.stalkIdeal x)) :=
      LocallyOfFiniteType.isLocallyNoetherian (affineBlowUp.π _)
    let M := (Scheme.Modules.pullback τ).obj C.sheaf
    let := finiteAffine_cohomologyOn_vanish M (isAffineOpen_top _) (q + 1) (by omega)
    exact ⟨_, τ, affineBlowUp.π (Z.stalkIdeal x), H,
      (Modules.cohomologyOnTopIso M (q + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton⟩

theorem sncCentre_cartier_correction_relative_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (c : Z.componentFamily.ι → ℕ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ n ∧
      SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ f))
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ)
    (Q : CartierDivisor X)
    (C : CartierDivisor Z.blowUp) (j : Z.componentFamily.ι → ℕ)
    (hj : ∀ i, j i ≤ c i - 1)
    (hC : C = cartierPullback Z.blowUpπ Q + ∑ i, j i • E i) :
    (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (C.sheaf.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ C.sheaf (q + 1))) := by
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  let := C.isInvertible_sheaf
  let := invertibleModule_isQuasicoherent C.sheaf
  have h := sncCentre_cartier_correction_allPoint_vanishing f n D Z hZ hη
    c hc E hE hEI Q C j hj hC
  exact ⟨fun _ hU q ↦ affine_open_preimage_cohomology_vanish_of_all_stalk_baseChange
      Z.blowUpπ C.sheaf q (fun x ↦ h x q) hU,
    fun q ↦ cohomologicalDirectImage_isZero_of_all_stalk_baseChange
      Z.blowUpπ C.sheaf q (fun x ↦ h x q)⟩

set_option linter.unusedVariables false in
/-- The original signed-effective interface, retaining its now-unneeded `hP` argument. -/
theorem sncCentre_component_correction_allPoint_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (c : Z.componentFamily.ι → ℕ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ n ∧
      SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ f))
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ)
    {ι : Type*} [Fintype ι] (P : ι → CartierDivisor X)
    (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (C : CartierDivisor Z.blowUp) (j : Z.componentFamily.ι → ℕ)
    (hj : ∀ i, j i ≤ c i - 1)
    (hC : C = cartierPullback Z.blowUpπ (∑ i, a i • P i) + ∑ i, j i • E i)
    (x : X) (q : ℕ) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Z.blowUp) (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' Z.blowUpπ (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj C.sheaf).toAbSheaf (q + 1)) := by
  clear hP
  exact sncCentre_cartier_correction_allPoint_vanishing f n D Z hZ hη c hc E hE hEI
    (∑ i, a i • P i) C j hj hC x q

set_option linter.unusedVariables false in
/-- The original signed-effective interface, retaining its now-unneeded `hP` argument. -/
theorem sncCentre_component_correction_relative_vanishing
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (c : Z.componentFamily.ι → ℕ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ n ∧
      SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ f))
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ)
    {ι : Type*} [Fintype ι] (P : ι → CartierDivisor X)
    (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (C : CartierDivisor Z.blowUp) (j : Z.componentFamily.ι → ℕ)
    (hj : ∀ i, j i ≤ c i - 1)
    (hC : C = cartierPullback Z.blowUpπ (∑ i, a i • P i) + ∑ i, j i • E i) :
    (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (C.sheaf.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ C.sheaf (q + 1))) := by
  clear hP
  exact sncCentre_cartier_correction_relative_vanishing f n D Z hZ hη c hc E hE hEI
    (∑ i, a i • P i) C j hj hC

end MixedFujita
