/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.StalkBaseChangeRelativeVanishing
public import SGA.Foundations.Cohomology.LerayTransfer
public import SGA.Foundations.Cohomology.PushforwardProjective

/-! Relative acyclicity composes through the actual ordinary direct image.
A finite affine cover of a compact open and SGA's Leray comparison avoid
requiring an identification with a derived higher direct image. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable def acyclicPushforwardCompactOpenAddEquiv
    {T X : Scheme.{u}} [X.IsSeparated] (f : T ⟶ X) (M : T.Modules)
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (hvan : ∀ V : X.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (f ⁻¹ᵁ V)))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (p : ℕ) :
    M.H' p (f ⁻¹ᵁ U) ≃+ ((Scheme.Modules.pushforward f).obj M).H' p U := by
  classical
  apply Classical.choice
  obtain ⟨n, V, hV, hcover⟩ := CohomologyAux.exists_affine_cover_of_isCompact U hU
  let : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X)) :=
    inferInstance
  have hcech : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      IsAffineOpen (TopCat.Presheaf.cechOpen V x) :=
    fun x => CohomologyAux.isAffineOpen_cechOpen V hV x
  have e := CohomologyAux.pushforwardH'AddEquiv M V p f hcech
    (fun x q => hvan _ (hcech x) q)
  rw [← Scheme.Hom.preimage_iSup, hcover] at e
  exact ⟨e⟩

noncomputable def acyclicPushforwardIsoCompactOpenAddEquiv
    {T X : Scheme.{u}} [X.IsSeparated] (f : T ⟶ X) (M : T.Modules)
    (N : X.Modules) [N.IsQuasicoherent]
    (e : N ≅ (Scheme.Modules.pushforward f).obj M)
    (hvan : ∀ V : X.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (f ⁻¹ᵁ V)))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (p : ℕ) :
    M.H' p (f ⁻¹ᵁ U) ≃+ N.H' p U := by
  let : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_of_iso e
  exact (acyclicPushforwardCompactOpenAddEquiv f M hvan U hU p).trans
    (Scheme.Modules.H'.mapIso e.symm p U).toAddEquiv

theorem affine_relative_vanishing_comp_of_pushforward_iso
    {T X B : Scheme.{u}} [X.IsSeparated] (f : T ⟶ X) (g : X ⟶ B) [QuasiCompact g]
    (M : T.Modules) (N : X.Modules) [N.IsQuasicoherent]
    (e : N ≅ (Scheme.Modules.pushforward f).obj M)
    (hf : ∀ V : X.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (f ⁻¹ᵁ V)))
    (hg : ∀ U : B.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (N.H' (q + 1) (g ⁻¹ᵁ U))) :
    (∀ U : B.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) ((f ≫ g) ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage (f ≫ g) M (q + 1))) := by
  have hv : ∀ U : B.Opens, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) ((f ≫ g) ⁻¹ᵁ U)) := by
    intro U hU q
    let := hg U hU q
    have hc : IsCompact (g ⁻¹ᵁ U : Set X) := by
      exact g.isCompact_preimage hU.isCompact
    exact (acyclicPushforwardIsoCompactOpenAddEquiv f M N e hf
      (g ⁻¹ᵁ U) hc (q + 1)).subsingleton
  exact ⟨hv, fun q => cohomologicalDirectImage_isZero_of_affine_vanishing
    (f ≫ g) M (q + 1) (fun U hU => hv U hU q)⟩

end MixedFujita
