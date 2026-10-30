/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltProductRestrictionStatements

/-!
The specialization of bad points in smooth families from the two restriction statements on the
product (step 15).

For the data of `KltFamilySpecializationStatement` (an affine open V of Y, a domain B with
formally étale coordinates, a family g in Γ(V) ⊗ B, a K-algebra map σ : Γ(V) → B and a dense set
of K-points of B over which the fibres are bad at σ(w)), the family is a family G of functions on
the inverse image U of V in P = Spec B ×_K Y (`specFibreProductSectionsEquiv`), whose restriction
to the fibre over w is (id ⊗ w)(g) (`specFibreProductFibre_appLE_tmul`). The K-point w of B and
the closed point σ(w) of V give the K-point (w ⊗ σ(w)) of Γ(U), the point (w, σ(w)) of P
(`specFibreProduct_primeIdealOf_fibre`). Then the argument of check 309 applies with the algebra
map Γ(U) → B, b ⊗ a ↦ b σ(a), in place of the section: Lemma 3 for the fixed family G on the
product in the weak model form, which holds for every pair
(`exists_ideal_modelThresholdWeakBadAt_of_affine`, so the product pair need not be shown klt),
gives an ideal I of Γ(U); by generic restriction the image of I in B vanishes on the dense set,
hence is zero; so (w₀, σ(w₀)) is weakly bad on P, and restriction to the fibre makes σ(w₀) bad
(`kltFamilySpecializationStatement_of_product`). Hence K-NF and F2 follow from the two restriction
statements (`kawamataNumericalFreeness_of_productRestriction`,
`linearEffectiveFreeness_of_productRestriction_of_basePointFree_of_ambro`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower
  specFibreProductSnd_isDominant specFibreProductSnd_isOver

section PrimeIdeals

variable {X Y : Scheme.{u}}

/-- Prime ideals of points of affine opens pull back along the maps of sections. -/
theorem appLE_mem_primeIdealOf_iff_of_affine (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (x : X) (hx : x ∈ U) (s : Γ(Y, V)) :
    f.appLE V U e s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      s ∈ (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal := by
  rw [← not_iff_not, ← mem_basicOpen_iff_notMem_primeIdealOf hU x hx,
    ← mem_basicOpen_iff_notMem_primeIdealOf hV (f x) (e hx), Scheme.basicOpen_appLE]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- Two points of an affine open with the same prime ideal are equal. -/
theorem eq_of_primeIdealOf_eq {U : X.Opens} (hU : IsAffineOpen U) {x x' : X} (hx : x ∈ U)
    (hx' : x' ∈ U)
    (h : ∀ s : Γ(X, U), s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      s ∈ (hU.primeIdealOf ⟨x', hx'⟩).asIdeal) : x = x' := by
  have h1 : hU.primeIdealOf ⟨x, hx⟩ = hU.primeIdealOf ⟨x', hx'⟩ :=
    PrimeSpectrum.ext (Ideal.ext h)
  have h2 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h3 := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  rw [h1] at h2
  exact h2.symm.trans h3

/-- Equal morphisms have equal maps of sections. -/
theorem appLE_eq_of_eq {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The identity restricts sections over an open to themselves. -/
theorem id_appLE_self (V : Y.Opens) (e : V ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    Scheme.Hom.appLE (𝟙 Y) V V e a = a := by
  change (𝟙 Γ(Y, V) ≫ Y.presheaf.map (homOfLE (le_refl V)).op) a = a
  rw [show (homOfLE (le_refl V)).op = 𝟙 (Opposite.op V) from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end PrimeIdeals

section Fibre

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

/-- The fibre over a K-point followed by the first projection is the K-point. -/
theorem specFibreProductFibre_fst (w : B →ₐ[K] K) :
    specFibreProductFibre (V := Y) w ≫ specFibreProductFst K B Y =
      (Y ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom) :=
  pullback.lift_fst _ _ _

/-- **The restriction of b ⊗ a to the fibre over w** is w(b) a. -/
theorem specFibreProductFibre_appLE_tmul (w : B →ₐ[K] K) {V : Y.Opens} (hV : IsAffineOpen V)
    (b : B) (a : Γ(Y, V)) :
    (specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V)
        (specFibreProductSectionsEquiv hV (b ⊗ₜ a)) = algebraMap K Γ(Y, V) (w b) * a := by
  rw [specFibreProductSectionsEquiv_tmul, map_mul]
  congr 1
  · change (specFibreProductFibre w).appLE _ V _
        (((specFibreProduct K B Y).baseRingToStructurePresheaf B).app (op _) b) =
      ((Y.baseRingToStructurePresheaf K).app (op V)) (w b)
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specFibreProductFst K B Y).appLE ⊤ _ le_top ≫
        (specFibreProductFibre w).appLE _ V _) b =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Y ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top)
        (w b)
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [specFibreProductFibre_fst, Scheme.Hom.comp_appLE]
    rw [← Category.assoc]
    erw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq (specFibreProductFibre_snd w)]
    exact id_appLE_self V _ a

end Fibre

section KPoints

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]

/-- The fibre over a K-point is a morphism over K. -/
theorem specFibreProductFibre_isOver (w : B →ₐ[K] K) :
    (specFibreProductFibre (V := Y) w).IsOver (Spec (CommRingCat.of K)) := by
  constructor
  change specFibreProductFibre w ≫ specFibreProductFst K B Y ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = Y ↘ Spec (CommRingCat.of K)
  rw [← Category.assoc, specFibreProductFibre_fst, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : w.toRingHom.comp (algebraMap K B) = RingHom.id K := by
    ext k
    exact w.commutes k
  rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

/-- The algebra map Γ(U) = B ⊗ Γ(V) → B, b ⊗ a ↦ b σ(a), of a K-algebra map σ : Γ(V) → B. -/
noncomputable def specFibreProductSectionMap {V : Y.Opens} (hV : IsAffineOpen V)
    (σS : Γ(Y, V) →ₐ[K] B) : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) →ₐ[K] B :=
  (Algebra.TensorProduct.lift (AlgHom.id K B) σS fun _ _ => Commute.all _ _).comp
    ((specFibreProductSectionsEquiv hV).symm.toAlgHom.restrictScalars K)

theorem specFibreProductSectionMap_tmul {V : Y.Opens} (hV : IsAffineOpen V)
    (σS : Γ(Y, V) →ₐ[K] B) (b : B) (a : Γ(Y, V)) :
    specFibreProductSectionMap hV σS (specFibreProductSectionsEquiv hV (b ⊗ₜ a)) = b * σS a := by
  simp [specFibreProductSectionMap]

end KPoints

section PointIdentification

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [Algebra K B]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] specFibreProductFibre_isOver

/-- **The point (w, y) of the product**: for a K-point w of B and a closed point y of an affine
open V given by the K-point w ∘ σ of Γ(V), a function on the inverse image of V vanishes at the
point (w, y) exactly when the K-point w ∘ s of the section map kills it. -/
theorem specFibreProduct_primeIdealOf_fibre {V : Y.Opens} (hV : IsAffineOpen V)
    (σS : Γ(Y, V) →ₐ[K] B) (w : B →ₐ[K] K) (y : Y) (hy : y ∈ V) (hyc : IsClosed ({y} : Set Y))
    (hmatch : ∀ a, w (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal)
    (hU : IsAffineOpen (specFibreProductSnd K B Y ⁻¹ᵁ V))
    (f : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) :
    w (specFibreProductSectionMap hV σS f) = 0 ↔
      f ∈ (hU.primeIdealOf ⟨specFibreProductFibre w y,
        specFibreProductFibre_le_preimage w V hy⟩).asIdeal := by
  classical
  have hFT : Algebra.FiniteType K Γ(Y, V) := sectionsBaseOpen_finiteType hV
  have hmax : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  -- the K-point of y is w ∘ σ
  have hψ : closedPointEvaluation (K := K) (hV.primeIdealOf ⟨y, hy⟩).asIdeal = w.comp σS := by
    apply algHom_eq_of_forall_eq_zero_iff
    intro a
    rw [closedPointEvaluation_eq_zero_iff (K := K), AlgHom.comp_apply, hmatch]
  -- the restriction to the fibre followed by the K-point of y is w ∘ s
  let ι := appLEAlgHom (K := K) (specFibreProductFibre (V := Y) w) (specFibreProductSnd K B Y ⁻¹ᵁ V)
    V (specFibreProductFibre_le_preimage w V)
  have hcomp : (w.comp σS).comp ι = w.comp (specFibreProductSectionMap hV σS) := by
    have hext : ((w.comp σS).comp ι).comp
        ((specFibreProductSectionsEquiv hV).toAlgHom.restrictScalars K) =
        (w.comp (specFibreProductSectionMap hV σS)).comp
          ((specFibreProductSectionsEquiv hV).toAlgHom.restrictScalars K) := by
      apply Algebra.TensorProduct.ext'
      intro b a
      change w (σS (ι (specFibreProductSectionsEquiv hV (b ⊗ₜ a)))) =
        w (specFibreProductSectionMap hV σS (specFibreProductSectionsEquiv hV (b ⊗ₜ a)))
      rw [specFibreProductSectionMap_tmul]
      change w (σS ((specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V)
        (specFibreProductSectionsEquiv hV (b ⊗ₜ a)))) = _
      rw [specFibreProductFibre_appLE_tmul, map_mul, map_mul, map_mul]
      simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    ext f'
    have h := congrArg (fun φ => φ ((specFibreProductSectionsEquiv hV).symm f')) hext
    simpa using h
  rw [← appLE_mem_primeIdealOf_iff_of_affine (specFibreProductFibre w) hV hU
    (specFibreProductFibre_le_preimage w V) y hy f, ← closedPointEvaluation_eq_zero_iff (K := K),
    hψ]
  change _ ↔ ((w.comp σS).comp ι) f = 0
  rw [hcomp]
  rfl

end PointIdentification

section ZeroFamily

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

omit [IsAlgClosed K] [IsLocallyNoetherian Y] in
/-- **Every closed point of a klt variety of positive dimension is bad for the zero family**: a
projective simple normal crossing model principalizing the ideal of the point has a member over
the point, whose log discrepancy is positive because the pair is klt. -/
theorem modelThresholdBadAt_zero_of_klt (hn : 1 ≤ n) (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (y : Y) (hy : IsClosed ({y} : Set Y)) {J : Type*} (M : ℕ) :
    ModelThresholdBadAt cY fY d D₀ y (fun _ : J => (0 : Y.functionField)) M := by
  classical
  -- the closed point is not the generic point
  have hgen : genericPoint Y ≠ y := by
    intro hgy
    have huniv : (Set.univ : Set Y) = {y} := by
      have h1 : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
      rw [← h1, hgy, hy.closure_eq]
    have : Subsingleton Y := ⟨fun a b => by
      have ha : a ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({y} : Set Y) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology Y
    rw [etaleChart_topologicalKrullDim (K := K) cY] at h0
    have h00 : (n : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h0
    have : n ≤ 0 := by exact_mod_cast h00
    omega
  -- a model principalizing the ideal of the point
  let Z : Closeds Y := ⟨{y}, hy⟩
  let 𝔟 : Unit → Y.IdealSheafData := fun _ => Scheme.IdealSheafData.vanishingIdeal Z
  have h𝔟 : ∀ j, genericPoint Y ∉ ((𝔟 j).support : Set Y) := by
    intro j hmem
    have hmem' : genericPoint Y ∈ (Z : Set Y) := by
      rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal Z]
      exact hmem
    exact hgen hmem'
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, -, -, -, h𝔟T, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n) cY fY d D₀
      (Empty.elim : Empty → CartierDivisor Y)
      (fun _ : Unit => (0 : CartierDivisor Y)) (fun _ => CartierDivisor.isEffective_zero) 𝔟 h𝔟
  obtain ⟨-, -, E, hE, hEI, hEsupp⟩ := h𝔟T ()
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n) t
  have hsupE : (ρ ⁻¹' ({y} : Set Y) : Set T) =
      ⋃ k ∈ {k | 0 < cartierCoefficient E (ξ k)}, closure ({ξ k} : Set T) := by
    rw [← effectiveCartier_support_eq_positive_member_union hnormT E hE ξ hEsupp, hEI,
      Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant ρ y
  have htmem : t ∈ (ρ ⁻¹' ({y} : Set Y) : Set T) := ht
  rw [hsupE] at htmem
  obtain ⟨k, hk, -⟩ := Set.mem_iUnion₂.mp htmem
  have hξk : ρ (ξ k) = y := by
    have hmem : ξ k ∈ (⋃ k ∈ {k | 0 < cartierCoefficient E (ξ k)},
        closure ({ξ k} : Set T)) :=
      Set.mem_iUnion₂.mpr ⟨k, hk, subset_closure (Set.mem_singleton _)⟩
    rw [← hsupE] at hmem
    exact hmem
  -- the member is a test prime through the point with positive log discrepancy
  have hpos := hklt T ρ hρ cT (ξ k) (hcoh k)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨T, hTi, inferInstance, hTo, hTs, ρ, hdom, hover, hρ, cT, ⟨ξ k, hcoh k⟩, ?_, ?_,
    fun j hj => absurd rfl hj⟩
  · change y ∈ closure ({ρ (ξ k)} : Set Y)
    rw [hξk]
    exact subset_closure (Set.mem_singleton _)
  · have h1 : ((0 : ℤ) : ℝ) < (d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ k) := by
      have : (0 : ℤ) < (d : ℤ) + cartierCoefficient
          (logDiscrepancyDivisor n ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ k) := by omega
      exact_mod_cast this
    exact div_pos (by simpa using h1) hdpos

end ZeroFamily

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty
  specFibreProductFibre_isOver

/-- **The specialization of bad points in smooth families from the statements on the product**:
generic restriction and restriction to fibres. -/
theorem kltFamilySpecializationStatement_of_product
    (hgen : KltProductGenericRestrictionStatement K)
    (hfib : KltProductFibreRestrictionStatement K) : KltFamilySpecializationStatement K := by
  classical
  intro Y _ _ _ _ _ _ n hn hnorm hcov cY fY d hd D₀ heff hklt V hV _ B _ _ _ _ e φ hφ J _ g M hM
    σS Dset hbad hdense w₀ y₀ hy₀ hyc₀ hmatch₀
  -- the product and the inverse image of V
  have : IsAffineHom (specFibreProductSnd K B Y) := MorphismProperty.pullback_snd _ _ inferInstance
  have hU : IsAffineOpen (specFibreProductSnd K B Y ⁻¹ᵁ V) := hV.preimage _
  have := specAlgebra_locallyOfFiniteType (K := K) (B := B)
  have : LocallyOfFiniteType (specFibreProductFst K B Y) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : LocallyOfFiniteType (specFibreProduct K B Y ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType (specFibreProductFst K B Y ≫
      (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)))
    infer_instance
  have : IsLocallyNoetherian (specFibreProduct K B Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (specFibreProduct K B Y ↘ Spec (CommRingCat.of K))
  have : QuasiCompact (specFibreProductFst K B Y) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsSeparated (specFibreProductFst K B Y) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (specFibreProduct K B Y ↘ Spec (CommRingCat.of K)) := by
    change QuasiCompact (specFibreProductFst K B Y ≫
      (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)))
    infer_instance
  have : IsSeparated (specFibreProduct K B Y ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated (specFibreProductFst K B Y ≫
      (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)))
    infer_instance
  -- the family on the product and its fibres
  let E := specFibreProductSectionsEquiv (K := K) (B := B) (T := Y) hV
  let G : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) := fun j =>
    E (Algebra.TensorProduct.comm K Γ(Y, V) B (g j))
  have hfibre : ∀ (w : B →ₐ[K] K) (t : Γ(Y, V) ⊗[K] B),
      (specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V)
        (E (Algebra.TensorProduct.comm K Γ(Y, V) B t)) = fibreAt w t := by
    intro w t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.comm_tmul, specFibreProductFibre_appLE_tmul, fibreAt_tmul,
        mul_comm]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]
  have hfibreG : ∀ w : B →ₐ[K] K, (fun j => Y.germToFunctionField V
      ((specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V) (G j))) =
      fun j => Y.germToFunctionField V (fibreAt w (g j)) := fun w => funext fun j => by
    rw [hfibre]
  -- the zero family
  by_cases hz : ∃ j, (specFibreProduct K B Y).germToFunctionField _ (G j) ≠ 0
  swap
  · push Not at hz
    have hg0 : ∀ j, fibreAt w₀ (g j) = 0 := by
      intro j
      have h1 : G j = 0 := (specFibreProduct K B Y).germToFunctionField_injective _
        ((hz j).trans (map_zero _).symm)
      have h2 : g j = 0 := by
        have h3 := congrArg (fun t => (Algebra.TensorProduct.comm K Γ(Y, V) B).symm (E.symm t)) h1
        simpa [G] using h3
      rw [h2, map_zero]
    have hfun : (fun j => Y.germToFunctionField V (fibreAt w₀ (g j))) =
        fun _ => (0 : Y.functionField) := funext fun j => by rw [hg0, map_zero]
    rw [hfun]
    exact modelThresholdBadAt_zero_of_klt hn cY fY hd D₀ hklt y₀ hyc₀ M
  -- Lemma 3 for the fixed family on the product, in the weak model form
  obtain ⟨I, hI⟩ := exists_ideal_modelThresholdWeakBadAt_of_affine
    (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit fY) hd (fibreProductPairDivisor D₀)
    _ hU G hz M hM
  obtain ⟨h, hh0, hgenh⟩ := hgen Y n hn hnorm hcov cY fY d hd D₀ heff hklt B e φ hφ V hV G M hM
    hz
  let s := specFibreProductSectionMap hV σS
  -- the points (w, y) of the product
  have hpoint : ∀ (w : B →ₐ[K] K) (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
      (∀ a, w (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) →
      IsClosed ({specFibreProductFibre w y} : Set (specFibreProduct K B Y)) ∧
        ∀ f, w (s f) = 0 ↔ f ∈ (hU.primeIdealOf ⟨specFibreProductFibre w y,
          specFibreProductFibre_le_preimage w V hy⟩).asIdeal := by
    intro w y hy hyc hm
    have hid := specFibreProduct_primeIdealOf_fibre hV σS w y hy hyc hm hU
    refine ⟨?_, hid⟩
    obtain ⟨x, hx, hxc, hxm⟩ := exists_closedPoint_of_algHom hU (w.comp s)
    have heq : x = specFibreProductFibre w y :=
      eq_of_primeIdealOf_eq hU hx (specFibreProductFibre_le_preimage w V hy) fun f => by
        rw [← hxm f, ← hid f]
        rfl
    rw [← heq]
    exact hxc
  -- the image of the ideal of the bad set vanishes on the dense set, hence is zero
  have hvanish : ∀ f ∈ I, s f = 0 := by
    intro f hf
    have hz' : h * s f = 0 := hdense _ fun w hw => by
      by_cases hwh : w h = 0
      · rw [map_mul, hwh, zero_mul]
      · obtain ⟨yw, hyw, hywc, hmw, hbw⟩ := hbad w hw
        rw [← hfibreG w] at hbw
        have hX := hgenh w hwh yw hyw hywc hbw
        obtain ⟨hxc, hxm⟩ := hpoint w yw hyw hywc hmw
        have hmem := (hI _ (specFibreProductFibre_le_preimage w V hyw) hxc).mp hX f hf
        rw [map_mul, (hxm f).mpr hmem, mul_zero]
    exact (mul_eq_zero.mp hz').resolve_left hh0
  -- the point over w₀ is bad on the product, hence on the fibre
  obtain ⟨hxc₀, hxm₀⟩ := hpoint w₀ y₀ hy₀ hyc₀ hmatch₀
  have hbadX := (hI _ (specFibreProductFibre_le_preimage w₀ V hy₀) hxc₀).mpr fun f hf =>
    (hxm₀ f).mp (by rw [hvanish f hf, map_zero])
  have hfin := hfib Y n hn hnorm hcov cY fY d hd D₀ heff hklt B e φ hφ V hV G M hM w₀ y₀ hy₀
    hyc₀ hbadX
  rwa [hfibreG] at hfin

/-- **K-NF from generic restriction and restriction to fibres for products** (Kawamata–Viehweg
vanishing is proved). -/
theorem kawamataNumericalFreeness_of_productRestriction
    (hgen : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductGenericRestrictionStatement K)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductFibreRestrictionStatement K) :
    KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_kltFamilySpecialization fun K _ _ _ =>
    kltFamilySpecializationStatement_of_product (hgen K) (hfib K)

/-- **F2 from generic restriction and restriction to fibres for products, the base point
free theorem for klt pairs and Ambro's canonical bundle formula for contractions to
lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_productRestriction_of_basePointFree_of_ambro
    (hgen : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductGenericRestrictionStatement K)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductFibreRestrictionStatement K)
    (hbpf : KltBasePointFreeStatement.{u}) (hamb : AmbroStrictDimensionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kltFamilySpecialization_of_basePointFree_of_ambro
    (fun K _ _ _ => kltFamilySpecializationStatement_of_product (hgen K) (hfib K)) hbpf hamb

end Assembly

end MixedFujita
