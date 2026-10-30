module
public import MixedFujita.PrincipalizedRelativeAdjointSectionBounds
public import MixedFujita.ProjectiveAllDimensionSectionBounds

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {B B' T T' : Scheme.{u}}
    [IsIntegral B] [IsIntegral B'] [IsIntegral T] [IsIntegral T']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]
    [T.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian B']


variable [Infinite K]

/-- Every original relative-adjoint multiple has finite global sections,
by the actual principalized comparison on the same base in every dimension.
No projectivity of the original source is added. -/
theorem actualRelativeAdjointMultiple_principalized_finiteDimensional_all_dimensions
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    {k : ℕ} (hdim : topologicalKrullDim B' = k) :
    ∀ j : ℕ, FiniteDimensional K Γ((j • L + E).sheaf, ⊤) := by
  intro j
  obtain ⟨i⟩ := actualRelativeAdjointMultiple_principalized_globalSections_linearEquiv
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e j
  letI := cartier_finiteDimensional_sections_of_projective_all_dimensions hdim hProj'
    (j • cartierPullback β A + (cartierPullback β C - P))
  exact Module.Finite.equiv i.symm

/-- One polynomial of the base dimension bounds all original relative-adjoint
section spaces, with the same fixed correction and no positivity assumption
on the original A or on the principalized line direction. -/
theorem actualRelativeAdjointMultiple_principalized_finrank_polynomial_upper_all_dimensions
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    {k : ℕ} (hdim : topologicalKrullDim B' = k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ j : ℕ,
      (Module.finrank K Γ((j • L + E).sheaf, ⊤) : ℝ) ≤ c * ((j : ℝ) + 1) ^ k := by
  obtain ⟨c, hc, hbound⟩ := cartier_affineMultiples_finrank_polynomial_upper_all_dimensions
    hdim hProj' (cartierPullback β A) (cartierPullback β C - P)
  refine ⟨c, hc, fun j => ?_⟩
  rw [actualRelativeAdjointMultiple_principalized_h0_eq
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e j]
  exact hbound j

/-- Effectivity of the actual original roundup removes that correction for an
upper bound by multiplication by one nonzero section, without source projectivity. -/
theorem actualRelativeAdjointMultiple_principalized_unrounded_finrank_polynomial_upper_all_dimensions
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    (hE : E.IsEffective) {k : ℕ} (hdim : topologicalKrullDim B' = k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ j : ℕ,
      (Module.finrank K Γ((j • L).sheaf, ⊤) : ℝ) ≤ c * ((j : ℝ) + 1) ^ k := by
  obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isEffective E hE
  obtain ⟨c, hc, hbound⟩ := actualRelativeAdjointMultiple_principalized_finrank_polynomial_upper_all_dimensions
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e hdim
  refine ⟨c, hc, fun j => ?_⟩
  have hfin := actualRelativeAdjointMultiple_principalized_finiteDimensional_all_dimensions
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e hdim j
  have hle := finrank_le_of_eq_add_of_section (K := K) (j • L) E (j • L + E) rfl t ht hfin
  exact (Nat.cast_le.mpr hle).trans (hbound j)

/-- Every existing Iitaka exponent of the actual relative-adjoint divisor is
at most the base dimension, including zero. This does not assert existence or numerical equality. -/
theorem actualRelativeAdjoint_principalized_iitakaDimension_le_all_dimensions
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    (hE : E.IsEffective) {k : ℕ} (hdim : topologicalKrullDim B' = k)
    {l : ℕ} (hIitaka : CartierIitakaDimension K L l) : l ≤ k := by
  obtain ⟨⟨c, hc, hlow⟩, -⟩ := hIitaka
  obtain ⟨Cbound, -, hupper⟩ :=
    actualRelativeAdjointMultiple_principalized_unrounded_finrank_polynomial_upper_all_dimensions
      hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e hE hdim
  exact polynomialGrowth_lower_exponent_le (by positivity) hc hlow hupper

end MixedFujita
