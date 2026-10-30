/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BaseRingSectionLocalization
public import MixedFujita.LocalizedCechCoboundaryDescent
public import SGA.Foundations.Cohomology.LerayTransfer
public import Mathlib.Algebra.Category.Grp.Zero

/-! Common-denominator descent for the actual pullback unit in a Cartesian
localization square. All section-localization and linearity hypotheses are
constructed. For a finite affine cover with affine intersections, vanishing
of the actual pulled module's cohomology supplies target Cech exactness. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TopCat.Presheaf
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem affine_pullback_cech_exact_of_cohomology_vanishing
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]
    (M : X.Modules) [M.IsQuasicoherent]
    {n : ℕ} (U : Fin n → X.Opens)
    (hU : ∀ {m : ℕ} (i : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U i))
    (hcover : (⨆ i, U i) = ⊤) (p : ℕ)
    (hvan : Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    (cechComplex U
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)).presheaf).ExactAt
        (p + 1) := by
  let N := (Scheme.Modules.pullback g).obj M
  have hV : ∀ {m : ℕ} (i : Fin (m + 1) → Fin n),
      IsAffineOpen (cechOpen (fun j ↦ g ⁻¹ᵁ U j) i) := by
    intro m i
    rw [CohomologyAux.cechOpen_preimage]
    exact (hU i).preimage g
  obtain ⟨e⟩ := N.nonempty_cechHomologyIso (fun j ↦ g ⁻¹ᵁ U j) hV (p + 1)
  have htop : (⨆ i, g ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  rw [htop] at e
  let : Subsingleton (Sheaf.H N.toAbSheaf (p + 1)) := hvan
  let : Subsingleton (N.H (p + 1)) :=
    (Scheme.Modules.H.addEquivSheafH N (p + 1)).toEquiv.subsingleton
  let : Subsingleton ((cechComplex (fun i ↦ g ⁻¹ᵁ U i) N.presheaf).homology (p + 1)) :=
    e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  let : Subsingleton ((cechComplex U ((Scheme.Modules.pushforward g).obj N).presheaf).homology
      (p + 1)) :=
    (CohomologyAux.cechHomologyPushforwardAddEquiv g N U (p + 1)).toEquiv.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (AddCommGrpCat.isZero_of_subsingleton _)

variable {A L : CommRingCat.{u}} {β : A ⟶ L} {X Y : Scheme.{u}}
  {f : X ⟶ Spec A} {g : Y ⟶ X} {g' : Y ⟶ Spec L}
  (H : IsPullback g g' f (Spec.map β)) (S : Submonoid A)
  (M : X.Modules) [M.IsQuasicoherent]
  {n : ℕ} (U : Fin n → X.Opens)
  (hU : ∀ {m : ℕ} (i : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U i))

include H hU

theorem localization_baseChange_cech_cocycle_denominator (p : ℕ)
    (hex : (cechComplex U
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)).presheaf).ExactAt
        (p + 1)) :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L → ∀ (c : CechCochain U M.presheaf (p + 1)),
      cechD U M.presheaf (p + 1) c = 0 →
      ∃ (s : S) (b : CechCochain U M.presheaf p),
        ∀ i, cechD U M.presheaf p b i = sectionBaseRingHom f (cechOpen U i) s • c i := by
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc c hc
  let N := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)
  let : ∀ V : X.Opens, Module A Γ(M, V) := sectionBaseModule f M
  let : ∀ V : X.Opens, Module A Γ(N, V) := sectionBaseModule f N
  let φ := pullbackSectionPresheafMap g M
  have hφ := pullbackSectionPresheafMap_smul f g M
  have hsections : ∀ m : ℕ, ∀ i : Fin (m + 1) → Fin n,
      IsLocalizedModule S (presheafLinearApp M.presheaf N.presheaf φ hφ (cechOpen U i)) := by
    intro m i
    exact affine_localization_baseChange_baseModule H (hU i) S M hloc
  obtain ⟨s, b, hb⟩ := finite_cech_cocycle_exists_denominator_of_target_exact
    M.presheaf N.presheaf φ hφ U S (sectionBaseModule_restrict_smul f M)
    (sectionBaseModule_restrict_smul f N) p hsections hex c hc
  exact ⟨s, b, fun i ↦ congrFun hb i⟩

theorem localization_baseChange_cech_denominator_of_cohomology_vanishing
    (hcover : (⨆ i, U i) = ⊤) (p : ℕ)
    (hvan : Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L → ∀ (c : CechCochain U M.presheaf (p + 1)),
      cechD U M.presheaf (p + 1) c = 0 →
      ∃ (s : S) (b : CechCochain U M.presheaf p),
        ∀ i, cechD U M.presheaf p b i = sectionBaseRingHom f (cechOpen U i) s • c i := by
  let : IsAffineHom g := CohomologyAux.isAffineHom_of_isPullback H
  exact localization_baseChange_cech_cocycle_denominator H S M U hU p
    (affine_pullback_cech_exact_of_cohomology_vanishing g M U hU hcover p hvan)

omit hU in
theorem localization_baseChange_exists_cech_denominator_cover
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (⨆ i, U i) = ⊤ ∧
      (∀ {m : ℕ} (i : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U i)) ∧
      ∀ p : ℕ,
        Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1)) →
        let : Algebra A L := β.hom.toAlgebra
        IsLocalization S L → ∀ (c : CechCochain U M.presheaf (p + 1)),
          cechD U M.presheaf (p + 1) c = 0 →
          ∃ (s : S) (b : CechCochain U M.presheaf p),
            ∀ i, cechD U M.presheaf p b i = sectionBaseRingHom f (cechOpen U i) s • c i := by
  obtain ⟨n, U, hcover, hU⟩ := CohomologyAux.exists_cechCover X
  exact ⟨n, U, hcover, hU, fun p hvan ↦
    localization_baseChange_cech_denominator_of_cohomology_vanishing H S M U hU hcover p hvan⟩

end MixedFujita
