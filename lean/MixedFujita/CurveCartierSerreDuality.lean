/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCurveIntrinsicDegree
public import TauCeti.AlgebraicGeometry.LineBundle.SerreDuality

/-!
Actual Cartier Serre duality on an integral Noetherian regular curve. A divisor
in the Weil differential canonical class is chosen internally and transported
through the existing actual Weil--Cartier equivalence. The duality targets
actual global sections; its degree is twice the actual H1 genus minus two.
This does not identify the chosen divisor with smoothCanonicalDivisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] [IsNoetherian X]
  [X.IsSeparated]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  (hex : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of K)))
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hF : TauCeti.IsFunctionField K X.functionField)
  (hk : IsIntegrallyClosedIn K X.functionField)

/-- Choose an actual divisor in the Weil differential canonical class. -/
def curveDualizingWeilDivisor : SchemeWeilDivisor X :=
  (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
    ((TauCeti.Place.orderSystem hF).divisorClass_surjective
      (TauCeti.canonicalClass hF hk)).choose

theorem curveDualizingWeilDivisor_canonicalClass :
    (TauCeti.Place.orderSystem hF).divisorClass
      (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim
        (curveDualizingWeilDivisor hex hdim hF hk)) = TauCeti.canonicalClass hF hk := by
  simp only [curveDualizingWeilDivisor, AddEquiv.apply_symm_apply]
  exact ((TauCeti.Place.orderSystem hF).divisorClass_surjective
    (TauCeti.canonicalClass hF hk)).choose_spec

/-- The same dualizing divisor as an actual Cartier divisor. -/
def curveDualizingCartierDivisor : CartierDivisor X :=
  SchemeWeilDivisor.equivCartierDivisor hdim (curveDualizingWeilDivisor hex hdim hF hk)

theorem curveDualizingCartierDivisor_toWeilDivisor :
    (curveDualizingCartierDivisor hex hdim hF hk).toWeilDivisor =
      curveDualizingWeilDivisor hex hdim hF hk := by
  rw [curveDualizingCartierDivisor,
    ← SchemeWeilDivisor.equivCartierDivisor_symm_apply hdim, AddEquiv.symm_apply_apply]

/-- Serre duality for the actual Cartier sheaf, with an internally chosen dualizing divisor. -/
def curveCartierSerreDuality (D : CartierDivisor X) :
    Module.Dual K (Scheme.Modules.Cohomology D.sheaf 1) ≃ₗ[K]
      Γ((curveDualizingCartierDivisor hex hdim hF hk - D).sheaf, ⊤) := by
  classical
  exact Classical.choice (show Nonempty _ from by
    let W := curveDualizingWeilDivisor hex hdim hF hk
    let C := curveDualizingCartierDivisor hex hdim hF hk
    obtain ⟨ω, -, hω, hW⟩ := TauCeti.exists_isGreatest_of_divisorClass_eq_canonicalClass
      hF hk (curveDualizingWeilDivisor_canonicalClass hex hdim hF hk)
    have hsub : (C - D).toWeilDivisor = W - D.toWeilDivisor := by
      calc
        (C - D).toWeilDivisor = C.toWeilDivisor - D.toWeilDivisor := by
          simpa only [CartierDivisor.toWeilDivisorHom_apply] using
            (CartierDivisor.toWeilDivisorHom : CartierDivisor X →+ SchemeWeilDivisor X).map_sub C D
        _ = W - D.toWeilDivisor := by
          rw [show C.toWeilDivisor = W from
            curveDualizingCartierDivisor_toWeilDivisor hex hdim hF hk]
    exact ⟨(Scheme.Modules.cohomologyBaseLinearEquivOfIso K
        (D.sheafIsoToWeilDivisor hdim) 1).dualMap.symm.trans <|
      (SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero
        hex hdim hF hk hω hW D.toWeilDivisor).trans <|
      (Scheme.Modules.cohomologyBaseLinearEquivOfIso K
        ((eqToIso (congrArg SchemeWeilDivisor.sheaf hsub)).symm ≪≫
          ((C - D).sheafIsoToWeilDivisor hdim).symm) 0).trans
        (Scheme.Modules.cohomologyZeroBaseLinearEquiv K X (C - D).sheaf)⟩
  )

theorem curveDualizingCartierDivisor_degree [IsProper (X ↘ Spec (CommRingCat.of K))] :
    CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
      (curveDualizingCartierDivisor hex hdim hF hk) =
      2 * (Module.finrank K (Scheme.Modules.Cohomology
        (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 := by
  letI := (Scheme.Modules.finiteDimensional_cohomology_congr K
    (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
      (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField
        hex hdim hF 0)
  have hdegree := SchemeWeilDivisor.relativeDegree_eq_two_mul_genus_sub_two
    hex hdim hF hk (curveDualizingWeilDivisor_canonicalClass hex hdim hF hk)
  have hz : Module.finrank K (Scheme.Modules.Cohomology (0 : CartierDivisor X).sheaf 1) =
      Module.finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
    exact Scheme.Modules.finrank_cohomology_congr K
      ((CartierDivisor.sheafIsoToWeilDivisor hdim 0) ≪≫
        eqToIso (by rw [← CartierDivisor.toWeilDivisorHom_apply, map_zero]) ≪≫
        SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1
  rw [CartierDivisor.relativeDegree_apply, curveDualizingCartierDivisor_toWeilDivisor,
    hdegree, Scheme.genus_def, hz]

end
end MixedFujita
