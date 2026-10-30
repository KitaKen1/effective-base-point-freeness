/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutSemiampleness
public import MixedFujita.LocalBaseCartierTriviality

/-! One conormal frame determines all integer Cartier restrictions.
No integrality assumption is made on the restriction scheme. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} [IsIntegral X]

noncomputable def cartierPulledSGANegativeNatPowerIso (p : Y ⟶ X)
    (H : CartierDivisor X) (L : Y.LineBundle)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ L.toModules 1) (j : ℕ) :
    (Scheme.Modules.pullback p).obj (-(j • H)).sheaf ≅ L.toModules (-(j : ℤ)) := by
  let A := L.toModules (-(j : ℤ))
  let B := L.toModules (j : ℤ)
  let C := (Scheme.Modules.pullback p).obj (-(j • H)).sheaf
  let b : A ⊗ B ≅ unitModule Y :=
    sgaLineBundleTensorPowerIso L (-(j : ℤ)) j ≪≫
      eqToIso (congrArg L.toModules (neg_add_cancel (j : ℤ))) ≪≫ sgaLineBundleZeroPowerIso L
  let c : B ⊗ C ≅ unitModule Y :=
    tensorIso (cartierPulledSGANatPowerIso p H L a j).symm (Iso.refl C) ≪≫
      (cartierPullbackTensorIso (j • H) p (-(j • H)).sheaf).symm ≪≫
        (Scheme.Modules.pullback p).mapIso
          (cartierTensorSheafIso (j • H) (-(j • H)) ≪≫
            eqToIso (congrArg CartierDivisor.sheaf (add_neg_cancel (j • H))) ≪≫
              cartierZeroSheafIso X) ≪≫ Scheme.Modules.pullbackObjUnitIso p
  exact ((ρ_ A).symm ≪≫ tensorIso (Iso.refl A) c.symm ≪≫ (α_ A B C).symm ≪≫
    tensorIso b (Iso.refl C) ≪≫ λ_ C).symm

noncomputable def cartierPulledSGAIntPowerIso (p : Y ⟶ X)
    (H : CartierDivisor X) (L : Y.LineBundle)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ L.toModules 1) (j : ℤ) :
    (Scheme.Modules.pullback p).obj (j • H).sheaf ≅ L.toModules j := by
  cases j with
  | ofNat j => simpa using cartierPulledSGANatPowerIso p H L a j
  | negSucc j =>
    simpa only [Int.negSucc_eq, ← Int.natCast_succ, neg_smul, natCast_zsmul] using
      cartierPulledSGANegativeNatPowerIso p H L a (j + 1)

noncomputable def cartierTrivialPlusConormalPowerIso (p : Y ⟶ X)
    (F E : CartierDivisor X) (L : Y.LineBundle)
    (a : (Scheme.Modules.pullback p).obj (-E).sheaf ≅ L.toModules 1)
    (b : F.sheaf ≅ unitModule X) (j : ℤ) :
    (Scheme.Modules.pullback p).obj (F + j • E).sheaf ≅ L.toModules (-j) := by
  let c : (Scheme.Modules.pullback p).obj (j • E).sheaf ≅ L.toModules (-j) := by
    simpa only [smul_neg, neg_smul, neg_neg] using cartierPulledSGAIntPowerIso p (-E) L a (-j)
  exact (Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso F (j • E)).symm ≪≫
    cartierPullbackTensorIso F p (j • E).sheaf ≪≫
      tensorIso ((Scheme.Modules.pullback p).mapIso b ≪≫ Scheme.Modules.pullbackObjUnitIso p) c ≪≫
        λ_ (L.toModules (-j))

noncomputable def cartierLocalBasePlusConormalPowerIso
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X)
    (P : CartierDivisor (Spec (CommRingCat.of R))) (F E : CartierDivisor X)
    (b : F.sheaf ≅ (Scheme.Modules.pullback f).obj P.sheaf)
    (L : Y.LineBundle) (a : (Scheme.Modules.pullback p).obj (-E).sheaf ≅ L.toModules 1)
    (j : ℤ) : (Scheme.Modules.pullback p).obj (F + j • E).sheaf ≅ L.toModules (-j) :=
  cartierTrivialPlusConormalPowerIso p F E L a
    (b ≪≫ localSpecCartierPullbackFrameIso R f P) j

end MixedFujita
