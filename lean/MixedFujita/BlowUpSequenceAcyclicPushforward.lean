/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AcyclicPushforwardComposition
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.BlowUp.Composite

/-! Induction on Hironaka's actual dependent sequence of blow-ups. The
step data explicitly contain the ordinary pushforward isomorphism and
affine relative acyclicity; the SNC constructor supplies these from geometry.
No derived higher direct image identification is asserted here. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def blowUpSequenceAcyclicModules : {X : Scheme.{u}} → (S : BlowUpSequence X) →
    X.Modules → S.last.Modules → Prop
  | _, .nil _, M, N => Nonempty (M ≅ N)
  | _, .cons _ Z rest, M, N =>
      ∃ L : Z.blowUp.Modules, L.IsQuasicoherent ∧
        Nonempty (M ≅ (Scheme.Modules.pushforward Z.blowUpπ).obj L) ∧
        (∀ U, IsAffineOpen U → ∀ q : ℕ,
          Subsingleton (L.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
        blowUpSequenceAcyclicModules rest L N

theorem blowUpSequence_acyclic_pushforward
    {X : Scheme.{u}} (S : BlowUpSequence X) [hX : IsLocallyNoetherian X]
    [hsep : X.IsSeparated] (M : X.Modules) [hM : M.IsQuasicoherent]
    (N : S.last.Modules) (h : blowUpSequenceAcyclicModules S M N) :
    Nonempty (M ≅ (Scheme.Modules.pushforward S.composite).obj N) ∧
    (∀ U, IsAffineOpen U → ∀ q : ℕ,
      Subsingleton (N.H' (q + 1) (S.composite ⁻¹ᵁ U))) ∧
    (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage S.composite N (q + 1))) := by
  revert hX hsep M hM N
  induction S with
  | nil X =>
    intro _ _ M _ N h
    obtain ⟨e⟩ := h
    let : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso e
    have hv : ∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
        Subsingleton (N.H' (q + 1) ((𝟙 X) ⁻¹ᵁ U)) := by
      intro U hU q
      rw [Scheme.Hom.id_preimage]
      exact N.H'_subsingleton_of_isAffineOpen hU q
    exact ⟨⟨e ≪≫ ((Scheme.Modules.pushforwardId X).app N).symm⟩, hv,
      fun q => cohomologicalDirectImage_isZero_of_affine_vanishing
        (𝟙 X) N (q + 1) (fun U hU => hv U hU q)⟩
  | cons X Z rest ih =>
    intro _ _ M _ N h
    obtain ⟨L, hL, ⟨e⟩, hstep, hrest⟩ := h
    let : L.IsQuasicoherent := hL
    let : IsLocallyNoetherian Z.blowUp := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
    let : Z.blowUp.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from Z.blowUpπ]
      infer_instance⟩
    obtain ⟨⟨erest⟩, hvrest, _⟩ := ih L N hrest
    have hv := affine_relative_vanishing_comp_of_pushforward_iso
      rest.composite Z.blowUpπ N L erest hvrest hstep
    exact ⟨⟨e ≪≫ (Scheme.Modules.pushforward Z.blowUpπ).mapIso erest ≪≫
      (Scheme.Modules.pushforwardComp rest.composite Z.blowUpπ).app N⟩, hv⟩

theorem blowUpSequence_compact_open_cohomology_comparison
    {X : Scheme.{u}} (S : BlowUpSequence X) [IsLocallyNoetherian X]
    [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    (N : S.last.Modules) (h : blowUpSequenceAcyclicModules S M N)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (p : ℕ) :
    Nonempty (N.H' p (S.composite ⁻¹ᵁ U) ≃+ M.H' p U) := by
  obtain ⟨⟨e⟩, hv, _⟩ := blowUpSequence_acyclic_pushforward S M N h
  exact ⟨acyclicPushforwardIsoCompactOpenAddEquiv S.composite N M e hv U hU p⟩

end MixedFujita
