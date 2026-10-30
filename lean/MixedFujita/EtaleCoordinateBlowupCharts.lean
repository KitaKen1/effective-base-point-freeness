/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional
public import Hironaka.Scheme.Smooth.BlowUpSmoothChart
public import Hironaka.Scheme.Smooth.EtaleCoordinatesAdapted
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Actual etale charts for blow-ups of coordinate centers of arbitrary
codimension, with the projection and exceptional ideal computed internally. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {n r : ℕ}
  {f : X ⟶ Spec (.of K)} {Z : X.IdealSheafData} {x : X}

theorem exists_etaleCoordinateBlowup_modelMap (E : EtaleCoordinatesAdapted f n r Z x) :
    ∃ φ : Scheme.IdealSheafData.blowUp (Z.comap E.U.1.ι) ⟶
        CoordinateSubspace.modelBlowUp K n r,
      IsPullback φ (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))
        (affineBlowUp.π (CoordinateSubspace.centerIdeal K n r))
        (toAffineSpace f E.U.1 E.v) ∧ Etale φ := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace K n r
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp E
  have : Etale φ := etale_of_isPullback_blowUp E H
  refine ⟨φ ≫ e.hom, ?_, inferInstance⟩
  exact H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using he.symm) (by simp)

/-- The actual local blow-up map to the standard affine model. -/
noncomputable def etaleCoordinateBlowupModelMap (E : EtaleCoordinatesAdapted f n r Z x) :=
  (exists_etaleCoordinateBlowup_modelMap E).choose

theorem etaleCoordinateBlowupModelMap_isPullback (E : EtaleCoordinatesAdapted f n r Z x) :
    IsPullback (etaleCoordinateBlowupModelMap E)
      (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))
      (affineBlowUp.π (CoordinateSubspace.centerIdeal K n r))
      (toAffineSpace f E.U.1 E.v) :=
  (exists_etaleCoordinateBlowup_modelMap E).choose_spec.1

instance etaleCoordinateBlowupModelMap_etale (E : EtaleCoordinatesAdapted f n r Z x) :
    Etale (etaleCoordinateBlowupModelMap E) :=
  (exists_etaleCoordinateBlowup_modelMap E).choose_spec.2

/-- An actual open chart of the local blow-up, étale over the standard affine chart. -/
@[reducible]
noncomputable def etaleCoordinateBlowupChart (E : EtaleCoordinatesAdapted f n r Z x) (k : Fin n) (hk : k.val < r) :
    Scheme.{u} :=
  pullback (etaleCoordinateBlowupModelMap E) (CoordinateSubspace.modelChart K n r k hk)

instance etaleCoordinateBlowupChart_openImmersion (E : EtaleCoordinatesAdapted f n r Z x)
    (k : Fin n) (hk : k.val < r) : IsOpenImmersion
      (pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk)) := inferInstance

instance etaleCoordinateBlowupChart_etale (E : EtaleCoordinatesAdapted f n r Z x) (k : Fin n) (hk : k.val < r) :
    Etale (pullback.snd (etaleCoordinateBlowupModelMap E)
      (CoordinateSubspace.modelChart K n r k hk)) := inferInstance

theorem etaleCoordinateBlowupChart_projection (E : EtaleCoordinatesAdapted f n r Z x) (k : Fin n) (hk : k.val < r) :
    pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk) ≫
      Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι) ≫ toAffineSpace f E.U.1 E.v =
    pullback.snd (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n r) k).toRingHom) := by
  rw [← (etaleCoordinateBlowupModelMap_isPullback E).w,
    ← Category.assoc, pullback.condition, Category.assoc,
    CoordinateSubspace.modelChart_π]

theorem etaleCoordinateBlowupChart_exists_preimage (E : EtaleCoordinatesAdapted f n r Z x)
    (q : Scheme.IdealSheafData.blowUp (Z.comap E.U.1.ι)) :
    ∃ (k : Fin n) (hk : k.val < r) (p : etaleCoordinateBlowupChart E k hk),
      pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk) p = q := by
  have h : etaleCoordinateBlowupModelMap E q ∈
      ⨆ (k : Fin n) (hk : k.val < r),
        (CoordinateSubspace.modelChart K n r k hk).opensRange := by
    rw [CoordinateSubspace.iSup_opensRange_modelChart]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨hk, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp hk
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hq
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (etaleCoordinateBlowupModelMap E)
      (CoordinateSubspace.modelChart K n r k hk)) q z hz.symm
  exact ⟨k, hk, p, hp⟩

theorem etaleCoordinateBlowup_exceptionalIdeal (E : EtaleCoordinatesAdapted f n r Z x) :
    (Z.comap E.U.1.ι).comap (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι)) =
      (affineBlowUp.exceptionalIdeal (CoordinateSubspace.centerIdeal K n r)).comap
        (etaleCoordinateBlowupModelMap E) := by
  calc
    _ = ((coordinateSubspace K n r).comap (toAffineSpace f E.U.1 E.v)).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι)) :=
      congrArg (fun J => J.comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))) E.adapted
    _ = _ := by
      rw [← Scheme.IdealSheafData.comap_comp,
    ← (etaleCoordinateBlowupModelMap_isPullback E).w, Scheme.IdealSheafData.comap_comp]
      rfl

theorem etaleCoordinateBlowupChart_exceptionalIdeal (E : EtaleCoordinatesAdapted f n r Z x)
    (k : Fin n) (hk : k.val < r) :
    ((Z.comap E.U.1.ι).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))).comap
      (pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk)) =
    (Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {(MvPolynomial.X k : MvPolynomial (Fin n) K)}).map
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) K))).inv.hom)).comap
      (pullback.snd (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk)) := by
  rw [etaleCoordinateBlowup_exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
    pullback.condition, Scheme.IdealSheafData.comap_comp,
    CoordinateSubspace.comap_exceptionalIdeal_modelChart]


end MixedFujita
