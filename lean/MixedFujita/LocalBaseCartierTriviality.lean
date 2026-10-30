/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierGradedPullback
public import MixedFujita.SGATwistPullbackIso

/-! A Cartier divisor over a local domain has one global rational equation.
The closed-point neighbourhood argument constructs a frame for its sheaf
and for every actual module pullback, including nonreduced sources. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]

theorem localSpec_cartier_exists_principal
    (D : CartierDivisor (Spec (CommRingCat.of R))) :
    ∃ f, principalCartierDivisor (Spec (CommRingCat.of R)) f = D := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (IsLocalRing.closedPoint R)
  obtain ⟨U, hx, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have htop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
  subst U
  rw [← principalCartierDivisor_restrict _ f ⊤] at hU
  exact ⟨f, by simpa only [TopCat.Presheaf.restrict_self] using hU⟩

noncomputable def localSpecCartierFrameIso
    (D : CartierDivisor (Spec (CommRingCat.of R))) :
    D.sheaf ≅ CohomologyAux.unitModule (Spec (CommRingCat.of R)) := by
  let f := Classical.choose (localSpec_cartier_exists_principal R D)
  have hf := Classical.choose_spec (localSpec_cartier_exists_principal R D)
  exact eqToIso (congrArg CartierDivisor.sheaf hf.symm) ≪≫
    (CartierDivisor.unitIsoSheafPrincipalCartierDivisor _ f).symm

noncomputable def localSpecCartierPullbackFrameIso {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of R))
    (D : CartierDivisor (Spec (CommRingCat.of R))) :
    (Scheme.Modules.pullback p).obj D.sheaf ≅ CohomologyAux.unitModule Y :=
  (Scheme.Modules.pullback p).mapIso (localSpecCartierFrameIso R D) ≪≫
    Scheme.Modules.pullbackObjUnitIso p

end MixedFujita
