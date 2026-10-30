/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHyperplaneAdjunction

/-!
Residues along the strict transform of a hyperplane of the product (step 15, the klt restriction
theorem).

Let f : T → P = Spec B ×_K Y be a model, c a chart of T in which the strict transform of the
hyperplane u_0 = 0 is y_0 = 0 with f*u_0 = y_0 w_0, and σ : U = Spec(Γ(T, c.U)/(y_0)) →
H = Spec(B/(u_0)) ×_K Y the test model, with ζ the image in T of the generic point of U. The
residue map g : O_{T,ζ} → K(U) sends

* the stalk Jacobian det J(f; c_P, c) at ζ to sign(π) · g(w_0) · J(σ; c_H, c_U)
  (`hyperplaneTest_jacobian_residue`): permuting the coordinates of the product chart c_P by π
  (`hyperplanePerm`) puts u_0 first, the residue of the Jacobian along y_0 = 0 is g(w_0) times
  the Jacobian of the residues (`etaleRelativeJacobian_det_residue`), and the residues of the other
  coordinates of c_P are the pullbacks along σ of the coordinates of c_H
  (`fibreProductCoords_hyperplanePerm_appLE`);
* the germ of the pullback of a section s of Y to σ*(s|_H) (`hyperplaneTest_constant_residue`),
  while its image in the function field of T is f*(s|_P) (`hyperplaneTest_constant_value`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Germs

/-- The germ of a restricted pullback of a section is the image under the stalk map of its
germ. -/
theorem appLE_germ_eq_stalkMap_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (s : Γ(Y, U)) :
    X.presheaf.germ V x hx (f.appLE U V e s) = f.stalkMap x (Y.presheaf.germ U (f x) (e hx) s) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ V x hx (X.presheaf.map (homOfLE e).op (f.app U s)) = _
  exact X.presheaf.germ_res_apply (homOfLE e) x hx _

end Germs

section Residue

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [IsDomain B]
  [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower specFibreProduct_isIntegral
  specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant specFibreProductSnd_isOver
  specFibreProductFst_isOver hyperplaneTestInclusion_isOver

omit [IsAlgClosed K] [IsDomain B] [Algebra.FiniteType K B] [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- The germ at a point of T of the pullback of a constant b of B is the germ of its image in a
chart. -/
theorem specFibreProduct_stalkMap_germ_algebraMap {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] (fT : T ⟶ specFibreProduct K B Y)
    [fT.IsOver (Spec (CommRingCat.of K))] (U' : (specFibreProduct K B Y).Opens) (t : T)
    (ht : fT t ∈ U') (O : T.Opens) (hO : t ∈ O) (b : B) :
    fT.stalkMap t ((specFibreProduct K B Y).presheaf.germ U' (fT t) ht
        (algebraMap B Γ(specFibreProduct K B Y, U') b)) =
      T.presheaf.germ O t hO (modelChartAlgHom (K := K) (fT ≫ specFibreProductFst K B Y) O b) := by
  have h1 : algebraMap B Γ(specFibreProduct K B Y, U') b =
      (specFibreProductFst K B Y).appLE ⊤ U' le_top
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
    change (((specFibreProduct K B Y).baseRingToStructurePresheaf B).app (op U')) b = _
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    rfl
  have h2 : ∀ a : Γ(Spec (CommRingCat.of B), ⊤),
      fT.app U' ((specFibreProductFst K B Y).appLE ⊤ U' le_top a) =
        (fT ≫ specFibreProductFst K B Y).appLE ⊤ (fT ⁻¹ᵁ U') le_top a := by
    intro a
    rw [← Scheme.Hom.appLE_eq_app, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [h1, Scheme.Hom.germ_stalkMap_apply, h2, modelChartAlgHom_apply,
    appLE_germ_eq_stalkMap_germ (fT ≫ specFibreProductFst K B Y) ⊤ (fT ⁻¹ᵁ U') le_top t ht,
    appLE_germ_eq_stalkMap_germ (fT ≫ specFibreProductFst K B Y) ⊤ O le_top t hO]

variable (cY : EtaleChart K Y n) (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B)
  (hφ : φ.toRingHom.FormallyEtale) [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
  {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  (fT : T ⟶ specFibreProduct K B Y) [IsDominant fT] [fT.IsOver (Spec (CommRingCat.of K))]
  (c : EtaleChart K T (n + (e + 1))) [(Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime]
  (w₀ : Γ(T, c.U))
  (hw₀ : modelChartAlgHom (K := K) (fT ≫ specFibreProductFst K B Y) c.U (φ (MvPolynomial.X 0)) =
    c.coords (MvPolynomial.X 0) * w₀)
  [IsDominant (hyperplaneTestMap c fT φ w₀ hw₀)]
  [(hyperplaneTestMap c fT φ w₀ hw₀).IsOver (Spec (CommRingCat.of K))]

omit [IsIntegral T] [IsDominant fT] in
set_option maxHeartbeats 1600000 in
/-- **The residue of the Jacobian of the model along the strict transform of the hyperplane**:
for ζ the image in T of the generic point of the test model U, the residue g = (O_{T,ζ} → K(U))
of the stalk Jacobian det J(f; c_P, c) at ζ is sign(π) · g(w_0) · J(σ; c_H, c_U), with π the
permutation of the product coordinates moving u_0 first. -/
theorem hyperplaneTest_jacobian_residue
    (hζ : hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))) ∈
      c.U)
    (hζP : fT (hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of
      (hyperplaneTestRing c))))) ∈ (fibreProductEtaleChart cY φ hφ).U) :
    stalkFunctionFieldAlgHom (K := K) (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
        (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c)
          (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
          (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) fT
            (hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))))
            (etaleChartStalkCoords (fibreProductEtaleChart cY φ hφ) _ hζP)
            (etaleChartStalkCoords c _ hζ) (etaleChartStalkCoords_formallyEtale c _ hζ)).det) =
      ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
        stalkFunctionFieldAlgHom (K := K)
          (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
          (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c)
            (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
            (T.presheaf.germ c.U _ hζ w₀)) *
        chartRelativeJacobianDet (hyperplaneTestMap c fT φ w₀ hw₀)
          (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ))
          (specAlgebraEtaleChart (K := K) (hyperplaneCoords c.coords)
            (hyperplaneCoords_formallyEtale c.coords c.formallyEtale)) := by
  classical
  -- notation
  let ηU := genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))
  let ζ₀ := hyperplaneTestInclusion c ηU
  let ψ := schemeStalkMapAlgHom (K := K) fT ζ₀
  let p := etaleChartStalkCoords (fibreProductEtaleChart cY φ hφ) (fT ζ₀) hζP
  let y : MvPolynomial (Fin (n + e + 1)) K →ₐ[K] T.presheaf.stalk ζ₀ :=
    etaleChartStalkCoords c ζ₀ hζ
  have hy : y.toRingHom.FormallyEtale := etaleChartStalkCoords_formallyEtale c ζ₀ hζ
  let x : MvPolynomial (Fin (n + e + 1)) K →ₐ[K] (specFibreProduct K B Y).presheaf.stalk (fT ζ₀) :=
    p.comp (MvPolynomial.rename (hyperplanePerm n e))
  let g : T.presheaf.stalk ζ₀ →ₐ[K] (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField :=
    (stalkFunctionFieldAlgHom (K := K) ηU).comp
      (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c) ηU)
  let wS := T.presheaf.germ c.U ζ₀ hζ w₀
  let cH := fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ)
  let cU := specAlgebraEtaleChart (K := K) (hyperplaneCoords c.coords)
    (hyperplaneCoords_formallyEtale c.coords c.formallyEtale)
  have hsq := hyperplaneTestMap_comm c fT φ w₀ hw₀
  have hζP' : fT ζ₀ ∈ specFibreProductSnd K B Y ⁻¹ᵁ cY.U := hζP
  -- residues of sections of P over the product chart
  have hV' : specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ cY.U ≤
      specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ⁻¹ᵁ
        (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) := fun x hx => by
    change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
      specFibreProductSnd K B Y) x ∈ cY.U
    rw [specFibreProductMap_snd]
    exact hx
  have : Nonempty cY.U := cY.nonempty
  have : Nonempty (hyperplaneTestInclusion c ⁻¹ᵁ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U))) :=
    ⟨⟨ηU, hζP'⟩⟩
  have C1 : ∀ s : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ cY.U),
      g (ψ ((specFibreProduct K B Y).presheaf.germ _ (fT ζ₀) hζP' s)) =
        (dominantFunctionFieldMap (hyperplaneTestMap c fT φ w₀ hw₀)).hom
          ((specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
            (specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ cY.U)
            ((specFibreProductMap (Y := Y)
              (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE _ _ hV' s)) := by
    intro s
    have h1 : ψ ((specFibreProduct K B Y).presheaf.germ _ (fT ζ₀) hζP' s) =
        T.presheaf.germ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)) ζ₀ hζP'
          (fT.appLE _ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)) le_rfl s) := by
      rw [appLE_germ_eq_stalkMap_germ]
      rfl
    rw [AlgHom.comp_apply, h1]
    exact residue_germ_appLE_eq_of_comm (K := K) (hyperplaneTestInclusion c) fT
      (hyperplaneTestMap c fT φ w₀ hw₀) _ hsq ηU (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)
      (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)) le_rfl hζP' s _ hV'
  -- the coordinates of the residue
  let yF := etaleChartFunctionFieldCoords cU
  have hyFe : yF.toRingHom.FormallyEtale := etaleChartFunctionFieldCoords_formallyEtale cU
  have hyF : ∀ k : Fin (n + e), yF (MvPolynomial.X k) = g (y (MvPolynomial.X k.succ)) := by
    intro k
    change (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv
          (hyperplaneCoords c.coords (MvPolynomial.X k))) =
      stalkFunctionFieldAlgHom (K := K) ηU (schemeStalkMapAlgHom (K := K)
        (hyperplaneTestInclusion c) ηU (T.presheaf.germ c.U ζ₀ hζ (c.coords
          (MvPolynomial.X (k.succ : Fin (n + e + 1)) : MvPolynomial (Fin (n + e + 1)) K))))
    rw [hyperplaneTest_residue_germ c _ hζ, hyperplaneCoords_X]
    rfl
  have hg0 : g (y (MvPolynomial.X 0)) = 0 := by
    have h0 : (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X (0 : Fin (n + e + 1)))})
        (c.coords (MvPolynomial.X (0 : Fin (n + e + 1)))) : hyperplaneTestRing c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    change stalkFunctionFieldAlgHom (K := K) ηU (schemeStalkMapAlgHom (K := K)
      (hyperplaneTestInclusion c) ηU (T.presheaf.germ c.U ζ₀ hζ
        (c.coords (MvPolynomial.X (0 : Fin (n + e + 1)))))) = 0
    rw [hyperplaneTest_residue_germ c _ hζ]
    have h1 := congrArg (fun z : hyperplaneTestRing c =>
      (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv z)) h0
    simp only [map_zero] at h1
    exact h1
  let xF := (dominantFunctionFieldAlgHom (K := K) (hyperplaneTestMap c fT φ w₀ hw₀)).comp
    (etaleChartFunctionFieldCoords cH)
  have hxF : ∀ k : Fin (n + e), xF (MvPolynomial.X k) = g (ψ (x (MvPolynomial.X k.succ))) := by
    intro k
    have hx : x (MvPolynomial.X k.succ) = (specFibreProduct K B Y).presheaf.germ _ (fT ζ₀) hζP'
        (fibreProductCoords cY φ (MvPolynomial.X (hyperplanePerm n e (k.succ : Fin (n + e + 1))))) := by
      change p (MvPolynomial.rename _ (MvPolynomial.X _)) = _
      rw [MvPolynomial.rename_X]
      rfl
    rw [hx, C1, fibreProductCoords_hyperplanePerm_appLE]
    rfl
  -- the first coordinate: f*u_0 = y_0 w_0
  have hw : ψ (x (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * wS := by
    have hx0 : x (MvPolynomial.X 0) = (specFibreProduct K B Y).presheaf.germ _ (fT ζ₀) hζP'
        (algebraMap B Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ cY.U)
          (φ (MvPolynomial.X 0))) := by
      change p (MvPolynomial.rename _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.rename_X, hyperplanePerm_zero]
      change (specFibreProduct K B Y).presheaf.germ _ (fT ζ₀) hζP'
        (fibreProductCoords cY φ (MvPolynomial.X (Fin.natAdd n 0))) = _
      rw [fibreProductCoords_X_natAdd, specFibreProductSectionsEquiv_tmul, map_one, mul_one]
    rw [hx0, schemeStalkMapAlgHom_apply, specFibreProduct_stalkMap_germ_algebraMap fT _ ζ₀ hζP' c.U hζ,
      hw₀, map_mul]
    rfl
  -- the residue identity and the permutation of the rows
  have hres := etaleRelativeJacobian_det_residue (N := n + e) ψ x y hy wS hw g hg0 yF hyF hyFe xF
    hxF
  have hren := etaleRelativeJacobian_det_rename ψ p y hy (hyperplanePerm n e)
  have h1 : g (etaleRelativeJacobian ψ x y hy).det =
      ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
        g (etaleRelativeJacobian ψ p y hy).det := by
    have h := congrArg g hren
    rw [map_mul, map_intCast] at h
    exact h
  have hJ' : (etaleRelativeJacobian (AlgHom.id K _) xF yF hyFe).det =
      chartRelativeJacobianDet (hyperplaneTestMap c fT φ w₀ hw₀) cH cU := by
    unfold chartRelativeJacobianDet
    rw [etaleRelativeJacobian_eq_of_apply_eq (AlgHom.id K _) xF
      (dominantFunctionFieldAlgHom (K := K) (hyperplaneTestMap c fT φ w₀ hw₀))
      (etaleChartFunctionFieldCoords cH) yF hyFe (fun i => rfl)]
  rw [h1, hJ'] at hres
  have hs : ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
      ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  change g (etaleRelativeJacobian ψ p y hy).det = _ * g wS * _
  calc g (etaleRelativeJacobian ψ p y hy).det =
        (((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
        ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField)) *
        g (etaleRelativeJacobian ψ p y hy).det := by rw [hs, one_mul]
    _ = ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
        (((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
        g (etaleRelativeJacobian ψ p y hy).det) := by ring
    _ = _ := by rw [hres]; ring

omit [IsDomain B] [IsIntegral T] [IsDominant fT]
  [(hyperplaneTestMap c fT φ w₀ hw₀).IsOver (Spec (CommRingCat.of K))] in
/-- **The residue of a function pulled back from Y**: the germ at ζ of the pullback to T of a
section s of Y has residue σ*(s|_H). -/
theorem hyperplaneTest_constant_residue (WY : Y.Opens) [Nonempty WY] (sY : Γ(Y, WY))
    (hζ : fT (hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of
      (hyperplaneTestRing c))))) ∈ specFibreProductSnd K B Y ⁻¹ᵁ WY) :
    stalkFunctionFieldAlgHom (K := K) (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
        (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c)
          (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
          (T.presheaf.germ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY)) _ hζ
            (fT.appLE _ _ le_rfl ((specFibreProductSnd K B Y).appLE WY _ le_rfl sY)))) =
      (dominantFunctionFieldMap (hyperplaneTestMap c fT φ w₀ hw₀)).hom
        ((dominantFunctionFieldMap
          (specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y)).hom
            (Y.germToFunctionField WY sY)) := by
  have hsq := hyperplaneTestMap_comm c fT φ w₀ hw₀
  have hV' : specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ WY ≤
      specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ⁻¹ᵁ
        (specFibreProductSnd K B Y ⁻¹ᵁ WY) := fun x hx => by
    change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
      specFibreProductSnd K B Y) x ∈ WY
    rw [specFibreProductMap_snd]
    exact hx
  have : Nonempty (hyperplaneTestInclusion c ⁻¹ᵁ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY))) :=
    ⟨⟨_, hζ⟩⟩
  rw [residue_germ_appLE_eq_of_comm (K := K) (hyperplaneTestInclusion c) fT
    (hyperplaneTestMap c fT φ w₀ hw₀) _ hsq _ (specFibreProductSnd K B Y ⁻¹ᵁ WY)
    (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY)) le_rfl hζ _ _ hV', specFibreProductMap_appLE_snd,
    dominantFunctionFieldMap_germ _ WY _ le_rfl]

omit [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime] [fT.IsOver (Spec (CommRingCat.of K))] in
/-- The image in the function field of T of the germ of the pullback of a section s of Y is
f*(s|_P). -/
theorem hyperplaneTest_constant_value (WY : Y.Opens) [Nonempty WY] (sY : Γ(Y, WY)) (t : T)
    (ht : fT t ∈ specFibreProductSnd K B Y ⁻¹ᵁ WY) :
    stalkFunctionFieldAlgHom (K := K) t
        (T.presheaf.germ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY)) t ht
          (fT.appLE _ _ le_rfl ((specFibreProductSnd K B Y).appLE WY _ le_rfl sY))) =
      (dominantFunctionFieldMap fT).hom ((dominantFunctionFieldMap
        (specFibreProductSnd K B Y)).hom (Y.germToFunctionField WY sY)) := by
  have : Nonempty (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY)) := ⟨⟨t, ht⟩⟩
  change algebraMap (T.presheaf.stalk t) T.functionField _ = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← dominantFunctionFieldMap_germ,
    ← dominantFunctionFieldMap_germ]

end Residue

end MixedFujita
