/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HyperplaneResidueJacobian
public import MixedFujita.KltCompactifiedModels
public import MixedFujita.KltSpecializationFromProduct
public import MixedFujita.KltFibreLogDiscrepancy
public import MixedFujita.RegularEquationCartier
public import MixedFujita.ProjectiveClosureBaseChange
public import MixedFujita.ModelChartJacobian

/-!
The test model of a hyperplane of the product given by the strict transform (step 15, adjunction
for the klt restriction theorem).

* **Residues of pulled back sections** (`residue_germ_appLE_eq_of_comm`): for a commutative square
  ι_U ≫ f = σ ≫ ι_H of morphisms U → T → P and U → H → P with σ dominant, the residue of the germ
  at ι_U(u) of the pullback along f of a section s of P is the pullback along σ of the function
  of the restriction of s to H. This is how functions of the singular P, regular at the generic
  point of the hyperplane but not at the points over the singular point, are restricted to the
  strict transform.
* **The fibre product map of an algebra map** θ : B → B' (`specFibreProductMap θ`):
  Spec B' ×_K Y → Spec B ×_K Y, with the second projections equal, the first ones related by
  Spec θ, the fibres over K-points w' ∘ … compatible, and the coordinates of the product charts
  restricted: the coordinates of Y are kept and b ∈ B goes to θ(b)
  (`specFibreProductMap_appLE_snd`, `specFibreProductMap_appLE_algebraMap`).
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

section Residue

variable {K : Type u} [Field K] {U T P H : Scheme.{u}} [IsIntegral U] [IsIntegral H]
  [U.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ιU : U ⟶ T) [ιU.IsOver (Spec (CommRingCat.of K))] (f : T ⟶ P) (σ : U ⟶ H) [IsDominant σ]
  (ιH : H ⟶ P) (hsq : ιU ≫ f = σ ≫ ιH)

include hsq in
/-- **The residue of a pulled back section along a commutative square**: the image in the function
field of U of the germ at ι_U(u) of f^* s is σ^* of the function of ι_H^* s. -/
theorem residue_germ_appLE_eq_of_comm (u : U) (U' : P.Opens) (O : T.Opens)
    (hO : O ≤ f ⁻¹ᵁ U') (hu : ιU u ∈ O) (s : Γ(P, U')) (V' : H.Opens) [Nonempty V']
    (hV' : V' ≤ ιH ⁻¹ᵁ U') [Nonempty (ιU ⁻¹ᵁ O)] :
    stalkFunctionFieldAlgHom (K := K) u (schemeStalkMapAlgHom (K := K) ιU u
        (T.presheaf.germ O (ιU u) hu (f.appLE U' O hO s))) =
      (dominantFunctionFieldMap σ).hom (H.germToFunctionField V' (ιH.appLE U' V' hV' s)) := by
  rw [stalkFunctionFieldAlgHom_stalkMap_germ]
  have hne1 : Nonempty (ιU ⁻¹ᵁ (f ⁻¹ᵁ U')) := by
    obtain ⟨⟨v, hv⟩⟩ := (inferInstance : Nonempty (ιU ⁻¹ᵁ O))
    exact ⟨⟨v, hO hv⟩⟩
  -- the pullback of the restriction is the restriction of the pullback
  have h1 : U.germToFunctionField (ιU ⁻¹ᵁ O) (ιU.app O (f.appLE U' O hO s)) =
      U.germToFunctionField (ιU ⁻¹ᵁ (f ⁻¹ᵁ U')) (ιU.app (f ⁻¹ᵁ U') (f.app U' s)) := by
    have hnat := congrArg (fun φ => φ (f.app U' s)) (ιU.naturality (homOfLE hO).op)
    simp only [CommRingCat.comp_apply] at hnat
    have he : f.appLE U' O hO s = T.presheaf.map (homOfLE hO).op (f.app U' s) := rfl
    rw [he, hnat]
    exact germToFunctionField_restrict U _ _
  rw [h1]
  -- the commutative square
  have h2 : ∀ (g : U ⟶ P), g = σ ≫ ιH → ∀ (_ : Nonempty (g ⁻¹ᵁ U')),
      U.germToFunctionField (g ⁻¹ᵁ U') (g.app U' s) =
        @Scheme.germToFunctionField U _ ((σ ≫ ιH) ⁻¹ᵁ U') (hsq ▸ hne1) ((σ ≫ ιH).app U' s) := by
    intro g hg _
    subst hg
    rfl
  have h3 : U.germToFunctionField (ιU ⁻¹ᵁ (f ⁻¹ᵁ U')) (ιU.app (f ⁻¹ᵁ U') (f.app U' s)) =
      @Scheme.germToFunctionField U _ ((ιU ≫ f) ⁻¹ᵁ U') hne1 ((ιU ≫ f).app U' s) := rfl
  rw [h3, h2 (ιU ≫ f) hsq hne1]
  have hne2 : Nonempty (ιH ⁻¹ᵁ U') := by
    obtain ⟨⟨v, hv⟩⟩ := (inferInstance : Nonempty V')
    exact ⟨⟨v, hV' hv⟩⟩
  have hne3 : Nonempty (σ ⁻¹ᵁ (ιH ⁻¹ᵁ U')) := by
    obtain ⟨⟨v, hv⟩⟩ := hne1
    refine ⟨⟨v, ?_⟩⟩
    change (σ ≫ ιH) v ∈ U'
    rw [← hsq]
    exact hv
  change @Scheme.germToFunctionField U _ (σ ⁻¹ᵁ (ιH ⁻¹ᵁ U')) hne3
    (σ.app (ιH ⁻¹ᵁ U') (ιH.app U' s)) = _
  rw [← Scheme.Hom.appLE_eq_app,
    ← dominantFunctionFieldMap_germ σ (ιH ⁻¹ᵁ U') (σ ⁻¹ᵁ (ιH ⁻¹ᵁ U')) le_rfl (ιH.app U' s)]
  congr 1
  have he2 : ιH.appLE U' V' hV' s = H.presheaf.map (homOfLE hV').op (ιH.app U' s) := rfl
  rw [he2]
  exact (germToFunctionField_restrict H hV' (ιH.app U' s)).symm

end Residue

section FibreProductMap

variable {K : Type u} [Field K] {B B' : Type u} [CommRing B] [CommRing B'] [Algebra K B]
  [Algebra K B'] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower

/-- The structure morphism of Spec B' factors through Spec B along an algebra map θ : B → B'. -/
theorem specMap_algHom_comp_over (θ : B →ₐ[K] B') :
    (Spec (CommRingCat.of B') ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K B')) =
    Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K B))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext k
  exact (θ.commutes k).symm

/-- **The map of fibre products of an algebra map** θ : B → B': Spec B' ×_K Y → Spec B ×_K Y. -/
noncomputable def specFibreProductMap (θ : B →ₐ[K] B') :
    specFibreProduct K B' Y ⟶ specFibreProduct K B Y :=
  pullback.map (Spec (CommRingCat.of B') ↘ Spec (CommRingCat.of K)) (Y ↘ Spec (CommRingCat.of K))
    (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) (Y ↘ Spec (CommRingCat.of K))
    (Spec.map (CommRingCat.ofHom θ.toRingHom)) (𝟙 Y) (𝟙 _)
    ((Category.comp_id _).trans (specMap_algHom_comp_over θ))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem specFibreProductMap_snd (θ : B →ₐ[K] B') :
    specFibreProductMap (Y := Y) θ ≫ specFibreProductSnd K B Y = specFibreProductSnd K B' Y := by
  simp only [specFibreProductMap, specFibreProductSnd, pullback.lift_snd, Category.comp_id]

theorem specFibreProductMap_fst (θ : B →ₐ[K] B') :
    specFibreProductMap (Y := Y) θ ≫ specFibreProductFst K B Y =
      specFibreProductFst K B' Y ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) := by
  simp only [specFibreProductMap, specFibreProductFst, pullback.lift_fst]

/-- For a surjective θ the map of fibre products is a closed immersion. -/
theorem specFibreProductMap_isClosedImmersion (θ : B →ₐ[K] B') (hθ : Function.Surjective θ) :
    IsClosedImmersion (specFibreProductMap (Y := Y) θ) := by
  have h₁ : IsClosedImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hθ
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) h₁
    (inferInstance : IsClosedImmersion (𝟙 Y)) (specMap_algHom_comp_over θ) (Category.id_comp _).symm

/-- The fibre of Spec B' ×_K Y over w' maps to the fibre of Spec B ×_K Y over w' ∘ θ. -/
theorem specFibreProductFibre_comp_map (θ : B →ₐ[K] B') (w' : B' →ₐ[K] K) :
    specFibreProductFibre (V := Y) w' ≫ specFibreProductMap θ =
      specFibreProductFibre (V := Y) (w'.comp θ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, specFibreProductMap_fst, ← Category.assoc, specFibreProductFibre_fst,
      specFibreProductFibre_fst, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  · rw [Category.assoc, specFibreProductMap_snd, specFibreProductFibre_snd,
      specFibreProductFibre_snd]

/-- The pullback of a section of Y is kept by the map of fibre products. -/
theorem specFibreProductMap_appLE_snd (θ : B →ₐ[K] B') (U₀ : Y.Opens) (a : Γ(Y, U₀)) :
    (specFibreProductMap θ).appLE (specFibreProductSnd K B Y ⁻¹ᵁ U₀)
        (specFibreProductSnd K B' Y ⁻¹ᵁ U₀) (fun x hx => by
          change (specFibreProductMap θ ≫ specFibreProductSnd K B Y) x ∈ U₀
          rw [specFibreProductMap_snd]
          exact hx)
        ((specFibreProductSnd K B Y).appLE U₀ (specFibreProductSnd K B Y ⁻¹ᵁ U₀) le_rfl a) =
      (specFibreProductSnd K B' Y).appLE U₀ (specFibreProductSnd K B' Y ⁻¹ᵁ U₀) le_rfl a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq (specFibreProductMap_snd θ)]

/-- The constants of B go to their images under θ. -/
theorem specFibreProductMap_appLE_algebraMap (θ : B →ₐ[K] B') (U' : (specFibreProduct K B Y).Opens)
    (V' : (specFibreProduct K B' Y).Opens) (e : V' ≤ specFibreProductMap θ ⁻¹ᵁ U') (b : B) :
    (specFibreProductMap θ).appLE U' V' e
        (algebraMap B Γ(specFibreProduct K B Y, U') b) =
      algebraMap B' Γ(specFibreProduct K B' Y, V') (θ b) := by
  change (specFibreProductMap θ).appLE U' V' e
      (((specFibreProduct K B Y).baseRingToStructurePresheaf B).app (op U') b) =
    (((specFibreProduct K B' Y).baseRingToStructurePresheaf B').app (op V')) (θ b)
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
    Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specFibreProductFst K B Y).appLE ⊤ U' le_top ≫
      (specFibreProductMap θ).appLE U' V' e) b =
    ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (specFibreProductFst K B' Y).appLE ⊤ V' le_top)
      (θ b)
  rw [Scheme.Hom.appLE_comp_appLE]
  have h := appLE_eq_of_eq (specFibreProductMap_fst θ) ⊤ V' (by simp)
  rw [h, Scheme.Hom.comp_appLE]
  rw [← Category.assoc]
  erw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end FibreProductMap

section HyperplaneCoordinates

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower

/-- The permutation of the coordinates (z, u_0, …, u_e) of a product chart moving u_0 to the
front: 0 ↦ n, i + 1 ↦ i for i < n, and i ↦ i for i > n. -/
noncomputable def hyperplanePerm (n e : ℕ) : Equiv.Perm (Fin (n + (e + 1))) :=
  (Fin.cycleRange (⟨n, by omega⟩ : Fin (n + (e + 1)))).symm

theorem hyperplanePerm_zero : hyperplanePerm n e 0 = Fin.natAdd n 0 := by
  rw [hyperplanePerm, Equiv.symm_apply_eq]
  have h : (Fin.natAdd n (0 : Fin (e + 1)) : Fin (n + (e + 1))) = ⟨n, by omega⟩ :=
    Fin.ext (by simp)
  rw [h, Fin.cycleRange_self]

theorem hyperplanePerm_succ_castAdd (j : Fin n) :
    hyperplanePerm n e ((Fin.castAdd e j).succ : Fin (n + e + 1)) = Fin.castAdd (e + 1) j := by
  rw [hyperplanePerm, Equiv.symm_apply_eq]
  apply Fin.ext
  rw [Fin.coe_cycleRange_of_lt (show (Fin.castAdd (e + 1) j : Fin (n + (e + 1))) <
    ⟨n, by omega⟩ from Fin.mk_lt_mk.mpr j.2)]
  simp

theorem hyperplanePerm_succ_natAdd (l : Fin e) :
    hyperplanePerm n e ((Fin.natAdd n l).succ : Fin (n + e + 1)) = Fin.natAdd n l.succ := by
  rw [hyperplanePerm, Equiv.symm_apply_eq]
  have h : (⟨n, by omega⟩ : Fin (n + (e + 1))) < Fin.natAdd n l.succ := by
    rw [Fin.lt_def]
    simp
  rw [Fin.cycleRange_of_gt h]
  apply Fin.ext
  simp
  omega

/-- **The product coordinates on the hyperplane u_0 = 0**: the map of fibre products of
B → B/(u_0) sends the coordinate of index π(k + 1) of the product chart of Spec B ×_K Y to the
coordinate of index k of the product chart of Spec (B/(u_0)) ×_K Y with the coordinates
`hyperplaneCoords φ`, for the permutation π = `hyperplanePerm`. -/
theorem fibreProductCoords_hyperplanePerm_appLE (cY : EtaleChart K Y n)
    (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B) (k : Fin (n + e)) :
    (specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
        (specFibreProductSnd K B Y ⁻¹ᵁ cY.U)
        (specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ cY.U)
        (fun x hx => by
          change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
            specFibreProductSnd K B Y) x ∈ cY.U
          rw [specFibreProductMap_snd]
          exact hx)
        (fibreProductCoords cY φ (MvPolynomial.X (hyperplanePerm n e (k.succ : Fin (n + e + 1))))) =
      fibreProductCoords cY (hyperplaneCoords φ) (MvPolynomial.X k) := by
  refine Fin.addCases (fun j => ?_) (fun l => ?_) k
  · rw [hyperplanePerm_succ_castAdd, fibreProductCoords_X_castAdd, fibreProductCoords_X_castAdd,
      specFibreProductSectionsEquiv_tmul, specFibreProductSectionsEquiv_tmul, map_one, map_one,
      one_mul, one_mul]
    exact specFibreProductMap_appLE_snd _ cY.U _
  · rw [hyperplanePerm_succ_natAdd, fibreProductCoords_X_natAdd, fibreProductCoords_X_natAdd,
      specFibreProductSectionsEquiv_tmul, specFibreProductSectionsEquiv_tmul, map_one, map_one,
      mul_one, mul_one, specFibreProductMap_appLE_algebraMap, hyperplaneCoords_X]
    rfl

end HyperplaneCoordinates

section TestModel

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))] {N e : ℕ}

attribute [local instance] specAlgebraOver specFibreProductOverAlgebra specFibreProductOverField

/-- The first projection of the fibre product is a morphism over K. -/
theorem specFibreProductFst_isOver :
    (specFibreProductFst K B Y).IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩

attribute [local instance] specFibreProductFst_isOver

/-- The ring of the strict transform of the hyperplane in a chart: Γ(T, c.U)/(y_0). -/
abbrev hyperplaneTestRing (c : EtaleChart K T (N + 1)) : Type u :=
  Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}

/-- The inclusion of the strict transform of the hyperplane in the chart into T. -/
noncomputable def hyperplaneTestInclusion (c : EtaleChart K T (N + 1)) :
    Spec (CommRingCat.of (hyperplaneTestRing c)) ⟶ T :=
  specAlgebraHom c.isAffine (Ideal.Quotient.mkₐ K (Ideal.span {c.coords (MvPolynomial.X 0)}))

theorem hyperplaneTestInclusion_isOver (c : EtaleChart K T (N + 1)) :
    (hyperplaneTestInclusion c).IsOver (Spec (CommRingCat.of K)) :=
  specAlgebraHom_isOver c.isAffine _

attribute [local instance] hyperplaneTestInclusion_isOver

variable (c : EtaleChart K T (N + 1)) (f : T ⟶ specFibreProduct K B Y)
  [f.IsOver (Spec (CommRingCat.of K))] (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B)
  (w : Γ(T, c.U))
  (hw : modelChartAlgHom (K := K) (f ≫ specFibreProductFst K B Y) c.U (φ (MvPolynomial.X 0)) =
    c.coords (MvPolynomial.X 0) * w)

/-- The map B → Γ(T, c.U)/(y_0) of the strict transform. -/
noncomputable def hyperplaneTestAlgHom : B →ₐ[K] hyperplaneTestRing c :=
  (Ideal.Quotient.mkₐ K (Ideal.span {c.coords (MvPolynomial.X 0)})).comp
    (modelChartAlgHom (K := K) (f ≫ specFibreProductFst K B Y) c.U)

include hw in
/-- It kills the first coordinate of B. -/
theorem hyperplaneTestAlgHom_ker (a : B) (ha : a ∈ Ideal.span {φ (MvPolynomial.X 0)}) :
    hyperplaneTestAlgHom c f a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  simp only [hyperplaneTestAlgHom, AlgHom.comp_apply, map_mul, hw, Ideal.Quotient.mkₐ_eq_mk]
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

/-- The induced map B/(u_0) → Γ(T, c.U)/(y_0). -/
noncomputable def hyperplaneTestQuotientAlgHom :
    (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) →ₐ[K] hyperplaneTestRing c :=
  Ideal.Quotient.liftₐ _ (hyperplaneTestAlgHom c f) (hyperplaneTestAlgHom_ker c f φ w hw)

theorem hyperplaneTestQuotientAlgHom_mk (a : B) :
    hyperplaneTestQuotientAlgHom c f φ w hw (Ideal.Quotient.mk _ a) = hyperplaneTestAlgHom c f a :=
  rfl

/-- The inclusion followed by f and the first projection is the spectrum of the map of
functions. -/
theorem hyperplaneTestInclusion_comp_fst :
    hyperplaneTestInclusion c ≫ f ≫ specFibreProductFst K B Y =
      Spec.map (CommRingCat.ofHom (hyperplaneTestAlgHom c f).toRingHom) := by
  rw [hyperplaneTestInclusion, specAlgebraHom, Category.assoc,
    fromSpec_comp_eq_SpecMap (f ≫ specFibreProductFst K B Y) c.isAffine, ← Spec.map_comp]
  rfl

theorem hyperplaneTestInclusion_comp_over :
    hyperplaneTestInclusion c ≫ f ≫ specFibreProductSnd K B Y ≫ (Y ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (hyperplaneTestRing c))) := by
  have h1 : specFibreProductSnd K B Y ≫ (Y ↘ Spec (CommRingCat.of K)) =
      specFibreProduct K B Y ↘ Spec (CommRingCat.of K) := pullback.condition.symm
  rw [h1, HomIsOver.comp_over, HomIsOver.comp_over]
  rfl

/-- **The test model of the hyperplane**: Spec(Γ(T, c.U)/(y_0)) → Spec(B/(u_0)) ×_K Y. -/
noncomputable def hyperplaneTestMap :
    Spec (CommRingCat.of (hyperplaneTestRing c)) ⟶
      specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y :=
  pullback.lift (Spec.map (CommRingCat.ofHom (hyperplaneTestQuotientAlgHom c f φ w hw).toRingHom))
    (hyperplaneTestInclusion c ≫ f ≫ specFibreProductSnd K B Y) (by
      rw [Category.assoc, Category.assoc, hyperplaneTestInclusion_comp_over]
      change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext k
      exact (hyperplaneTestQuotientAlgHom c f φ w hw).commutes k)

theorem hyperplaneTestMap_snd :
    hyperplaneTestMap c f φ w hw ≫ specFibreProductSnd K _ Y =
      hyperplaneTestInclusion c ≫ f ≫ specFibreProductSnd K B Y :=
  pullback.lift_snd _ _ _

theorem hyperplaneTestMap_fst :
    hyperplaneTestMap c f φ w hw ≫ specFibreProductFst K _ Y =
      Spec.map (CommRingCat.ofHom (hyperplaneTestQuotientAlgHom c f φ w hw).toRingHom) :=
  pullback.lift_fst _ _ _

/-- **The commutative square** of the strict transform: the inclusion followed by f is the test
map followed by the map of fibre products. -/
theorem hyperplaneTestMap_comm :
    hyperplaneTestInclusion c ≫ f =
      hyperplaneTestMap c f φ w hw ≫
        specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) := by
  apply pullback.hom_ext
  · change (hyperplaneTestInclusion c ≫ f) ≫ specFibreProductFst K B Y = _
    rw [Category.assoc, hyperplaneTestInclusion_comp_fst, Category.assoc]
    change _ = hyperplaneTestMap c f φ w hw ≫
      specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
        specFibreProductFst K B Y
    rw [specFibreProductMap_fst, ← Category.assoc, hyperplaneTestMap_fst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  · change (hyperplaneTestInclusion c ≫ f) ≫ specFibreProductSnd K B Y = _
    rw [Category.assoc]
    change _ = hyperplaneTestMap c f φ w hw ≫
      specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
        specFibreProductSnd K B Y
    rw [specFibreProductMap_snd, hyperplaneTestMap_snd]

/-- The test map is a morphism over K. -/
theorem hyperplaneTestMap_isOver :
    (hyperplaneTestMap c f φ w hw).IsOver (Spec (CommRingCat.of K)) := by
  constructor
  change hyperplaneTestMap c f φ w hw ≫ specFibreProductFst K _ Y ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}))) = _
  rw [← Category.assoc, hyperplaneTestMap_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change _ = Spec.map (CommRingCat.ofHom (algebraMap K (hyperplaneTestRing c)))
  congr 2
  ext k
  exact (hyperplaneTestQuotientAlgHom c f φ w hw).commutes k

end TestModel

section Birational

variable {U T P H : Scheme.{u}} [IsIntegral U] [IsIntegral H]
  (ιU : U ⟶ T) (f : T ⟶ P) (σ : U ⟶ H) (ιH : H ⟶ P) (hsq : ιU ≫ f = σ ≫ ιH)

include hsq in
/-- **The generic point of the test model goes to the generic point of the hyperplane**, when the
image in P of the generic point of U specializes to the image of the generic point of H. -/
theorem genericPoint_eq_of_comm [IsClosedImmersion ιH]
    (hgen : f (ιU (genericPoint U)) ⤳ ιH (genericPoint H)) :
    σ (genericPoint U) = genericPoint H := by
  have h1 : ιH (σ (genericPoint U)) = f (ιU (genericPoint U)) := by
    have h := congrArg (fun g : U ⟶ P => g (genericPoint U)) hsq
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  have h2 : genericPoint H ⤳ σ (genericPoint U) :=
    (genericPoint_spec H).specializes (Set.mem_univ _)
  have h3 : ιH (genericPoint H) ⤳ ιH (σ (genericPoint U)) := h2.map ιH.continuous
  rw [h1] at h3
  have h4 : ιH (genericPoint H) = f (ιU (genericPoint U)) := (h3.antisymm hgen).eq
  exact (ιH.isClosedEmbedding.injective (h4.trans h1.symm)).symm

omit [IsIntegral U] in
/-- A morphism sending the generic point of U to the generic point of H is dominant. -/
theorem isDominant_of_genericPoint_eq [IrreducibleSpace U]
    (h : σ (genericPoint U) = genericPoint H) : IsDominant σ := by
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have hcl : closure ({genericPoint H} : Set H) = Set.univ := (genericPoint_spec H).def
  rw [← hcl]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint U, h⟩)

include hsq in
/-- **The test model is birational onto the hyperplane** when the stalk map of f at the image of
the generic point of U is bijective and ι_U is surjective on stalks: the function field map of
σ is then surjective, and injective as a map of fields. -/
theorem dominantFunctionFieldMap_bijective_of_comm [IsDominant σ] [SurjectiveOnStalks ιU]
    (hbij : Function.Bijective (f.stalkMap (ιU (genericPoint U)))) :
    Function.Bijective (dominantFunctionFieldMap σ).hom := by
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := ιU.stalkMap_surjective (genericPoint U) x
  obtain ⟨z, rfl⟩ := hbij.2 y
  have e1 : ιU.stalkMap (genericPoint U) (f.stalkMap (ιU (genericPoint U)) z) =
      (ιU ≫ f).stalkMap (genericPoint U) z := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hpt : σ (genericPoint U) = genericPoint H := dominant_map_genericPoint σ
  have key : ∀ a : H.presheaf.stalk (σ (genericPoint U)),
      ∃ b, (dominantFunctionFieldMap σ).hom b = σ.stalkMap (genericPoint U) a := by
    intro a
    refine ⟨H.presheaf.stalkSpecializes (specializes_of_eq hpt.symm) a, ?_⟩
    change σ.stalkMap (genericPoint U) (H.presheaf.stalkSpecializes
      (specializes_of_eq (dominant_map_genericPoint σ))
      (H.presheaf.stalkSpecializes (specializes_of_eq hpt.symm) a)) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp_apply]
    have hid : H.presheaf.stalkSpecializes ((specializes_of_eq (dominant_map_genericPoint σ)).trans
        (specializes_of_eq hpt.symm)) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl H.presheaf (σ (genericPoint U))
    rw [hid]
    rfl
  rw [e1, Scheme.Hom.stalkMap_congr_hom (ιU ≫ f) (σ ≫ ιH) hsq, Scheme.Hom.stalkMap_comp,
    CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact key _

end Birational

end MixedFujita
