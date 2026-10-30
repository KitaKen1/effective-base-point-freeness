/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CentreComponentOpenRestriction
public import MixedFujita.SNCConnectedCentreDimension
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc

/-! A possibly disconnected SNC center has ambient neighborhoods with
integral restricted center and fixed positive relative codimension. The
codimension may vary between components. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem sncCentre_exists_open_positive_codimension
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] (hη : genericPoint X ∉ Z.support)
    (x : X) (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (c : ℕ), x ∈ U ∧ 0 < c ∧ c ≤ n ∧
      IsIntegral (Z.comap U.ι).subscheme ∧
      SmoothOfRelativeDimension (n - c) ((Z.comap U.ι).subschemeι ≫ U.ι ≫ f) ∧
      topologicalKrullDim (Z.comap U.ι).subscheme = n - c := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨U, hxU, hZU, _⟩ := sncCentre_exists_integral_open_restriction f D Z hZ x hx
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : SmoothOfRelativeDimension n (U.ι ≫ f) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f))
  let : IsIntegral (Z.comap U.ι).subscheme := hZU
  let j := (centreOpenRestrictionIso Z U).hom ≫ (Z.subschemeι ⁻¹ᵁ U).ι
  let : IsLocallyNoetherian (Z.comap U.ι).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian j
  let : NoetherianSpace (Z.comap U.ι).subscheme := j.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian (Z.comap U.ι).subscheme := {}
  have hZU' : (D.comap U.ι).HasSncWith (Z.comap U.ι) :=
    hasSncWith_comap_of_smooth f U.ι hZ
  have hηU : genericPoint U.toScheme ∉ (Z.comap U.ι).support := by
    intro h
    have h' := (mem_support_comap_iff_apply Z U.ι _).mp h
    rw [genericPoint_eq_of_isOpenImmersion U.ι] at h'
    exact hη h'
  obtain ⟨c, hc, hcn, hdim, htop⟩ := snc_connectedCentre_exists_codimension_of_relativeDimension
    (U.ι ≫ f) n (D.comap U.ι) (Z.comap U.ι) hZU' hηU
  exact ⟨U, c, hxU, hc, hcn, hZU, hdim, htop⟩

end MixedFujita
