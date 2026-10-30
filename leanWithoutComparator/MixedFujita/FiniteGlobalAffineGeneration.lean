/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.QuasicoherentAffineEpi
public import MixedFujita.FiniteFreeGlobalGenerators
public import MixedFujita.ModuleOpenFrameGerms
public import Mathlib.RingTheory.LocalRing.Basic

/-! 同じ有限大域生成族のアフィン生成と任意frameの単元係数。 See reports/check-260-ideal-exterior-affine-generation.json for the verified scope. Actual quasicoherent epimorphisms are surjective on every affine open; the SAME finite global generators span there and have a unit coefficient at any specified affine frame. Empty actual ideal support gives an isomorphic inclusion; the nonflat actual comap comparison makes natural ideal inclusion and Cartier-twisted inclusion epimorphic after mapping off support. ALL high original ample powers construct one finite actual ambient Cartier family naturally zero on the actual closed center whose canonical finite-free map pulls back epimorphically on its canonical open complement. Identifying this with the canonical map of the same naturally pulled global sections, pointwise original Cartier basepointfreeness, exterior LC/Bertini, ambient nonLC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000


/-- A canonical finite global generating epimorphism generates the ACTUAL
module sections over EVERY actual affine open by the restrictions of the SAME
global sections. This is the required local span statement, without a new
generation certificate. -/
theorem finite_global_generators_span_on_every_affine
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (g : Fin k → Γ(M, ⊤))
    [Epi (biproduct.desc (fun i => CohomologyAux.homOfSection M (g i)))]
    (U : X.affineOpens) :
    Submodule.span Γ(X, U.1) (Set.range (fun i =>
      M.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op (g i))) = ⊤ := by
  classical
  let Q := fun _ : Fin k => CohomologyAux.unitModule X
  let π : (⨁ Q) ⟶ M := biproduct.desc (fun i => CohomologyAux.homOfSection M (g i))
  let : Epi π := inferInstanceAs (Epi (biproduct.desc (fun i => CohomologyAux.homOfSection M (g i))))
  have hsurj := quasicoherent_epi_app_surjective_on_affine π U
  apply top_unique
  intro m _
  obtain ⟨r, hr⟩ := hsurj m
  have hrdecomp : ∑ i, Scheme.Modules.Hom.app (biproduct.ι Q i) U.1
      (Scheme.Modules.Hom.app (biproduct.π Q i) U.1 r) = r := by
    let ev : ((⨁ Q) ⟶ (⨁ Q)) →+ Γ((⨁ Q), U.1) :=
      { toFun := fun a => Scheme.Modules.Hom.app a U.1 r,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev (biproduct.total (f := Q))
    rw [map_sum] at h
    exact h
  rw [← hr, ← hrdecomp, map_sum]
  apply Submodule.sum_mem
  intro i _
  change Scheme.Modules.Hom.app (biproduct.ι Q i ≫ π) U.1
    (Scheme.Modules.Hom.app (biproduct.π Q i) U.1 r) ∈ _
  rw [biproduct.ι_desc, CohomologyAux.homOfSection_app]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


/-- Taking the image of an actual global section is compatible with its
canonical structure-sheaf hom. -/
theorem homOfSection_comp_module_hom
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (s : Γ(M, ⊤)) :
    CohomologyAux.homOfSection M s ≫ f =
      CohomologyAux.homOfSection N (Scheme.Modules.Hom.app f ⊤ s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(X, U) at r
  change Scheme.Modules.Hom.app f U (Scheme.Modules.Hom.app (CohomologyAux.homOfSection M s) U r) = _
  rw [CohomologyAux.homOfSection_app, CohomologyAux.homOfSection_app,
    Scheme.Modules.Hom.app_smul, CohomologyAux.hom_app_presheaf_map]


/-- A finite actual generating epimorphism has a generator with UNIT
coefficient in ANY specified affine local frame at the specified point.
The short local-ring argument uses a finite sum equal to 1, rather than a
classification of supports or any normality assumption. -/
theorem finite_global_generators_exists_unit_at_affine_frame
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (g : Fin k → Γ(M, ⊤))
    [Epi (biproduct.desc (fun i => CohomologyAux.homOfSection M (g i)))]
    (U : X.affineOpens) (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : X) (hx : x ∈ U.1) :
    ∃ i, IsUnit (moduleOverFrameGlobalCoefficientGerm M U.1 e x hx (g i)) := by
  classical
  let c := moduleOverFrameCoefficient M U.1 e U.1 le_rfl
  let t (i : Fin k) := M.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op (g i)
  have hmem : c.symm 1 ∈ Submodule.span Γ(X, U.1) (Set.range t) := by
    rw [finite_global_generators_span_on_every_affine M k g U]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  have hc := congrArg c ha
  rw [map_sum] at hc
  simp only [LinearEquiv.map_smul, smul_eq_mul, LinearEquiv.apply_symm_apply] at hc
  have hsum : ∑ i, X.presheaf.germ U.1 x hx (a i) *
      moduleOverFrameGlobalCoefficientGerm M U.1 e x hx (g i) = 1 := by
    have h := congrArg (X.presheaf.germ U.1 x hx) hc
    simpa only [map_sum, map_mul, map_one, moduleOverFrameGlobalCoefficientGerm, c, t] using h
  have hu : IsUnit (∑ i, X.presheaf.germ U.1 x hx (a i) *
      moduleOverFrameGlobalCoefficientGerm M U.1 e x hx (g i)) := by rw [hsum]; exact isUnit_one
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum hu
  exact ⟨i, (IsUnit.mul_iff.mp hi).2⟩

end MixedFujita
