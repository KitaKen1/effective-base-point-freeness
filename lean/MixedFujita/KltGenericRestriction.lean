/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltSpecializationFromProduct
public import MixedFujita.KltFibreLogDiscrepancy

/-!
Generic restriction for the product of a klt pair with a smooth affine variety (step 15):
`KltProductGenericRestrictionStatement` holds (`kltProductGenericRestrictionStatement_holds`), so
K-NF and F2 follow from restriction to the fibres of products alone.

The proof is that of check 314 on the product P = Spec B ×_K Y of a klt pair on a possibly
singular Y. On the affine open U = π⁻¹(V) of P carry the pullback pair, take a projective simple
normal crossing model T of U principalizing the nonzero members of the family, and choose h ≠ 0
in B such that over D(h) every point of T has a fibre chart (generic smoothness of the strata),
the generic point of every fibre lies in the domain of a section of T → U near the generic point,
and the members stay nonzero on the fibres. For a K-point w with w(h) ≠ 0 and a bad test prime x
of Y at y, map the test model over V into the fibre of U over w; it lifts near x to T. At the
image of x take the fibre chart: the log discrepancy inequality along x for the pulled back pair
(`fibre_snc_logDiscrepancy_le`, with the product chart of P at the generic points) and the orders
of the members of the family give a member of the family with o_s > 0 that is bad; its centre
contains (w, y), so (w, y) is weakly bad on P.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra specAlgebraOver structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower
  specFibreProductSnd_isDominant specFibreProductSnd_isOver

section GermAppLE

/-- The germ of the pullback of a section along `appLE` is the stalk map of the germ. -/
theorem germ_appLE_eq_stalkMap_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (s : Γ(Y, U)) :
    X.presheaf.germ V x hx (f.appLE U V e s) =
      f.stalkMap x (Y.presheaf.germ U (f x) (e hx) s) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

end GermAppLE

section StalkCongr

/-- Equal morphisms pull back germs to the same rational functions. -/
theorem algebraMap_stalkMap_germ_of_eq {X Y : Scheme.{u}} [IsIntegral X] {f g : X ⟶ Y}
    (hfg : f = g) (x : X) (U : Y.Opens) (hf : f x ∈ U) (hg : g x ∈ U) (s : Γ(Y, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField
        (f.stalkMap x (Y.presheaf.germ U (f x) hf s)) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (g.stalkMap x (Y.presheaf.germ U (g x) hg s)) := by
  subst hfg
  rfl

/-- The rational function of the restriction of a section to a smaller open. -/
theorem germToFunctionField_appLE {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y) (U : Y.Opens)
    (V V' : X.Opens) [Nonempty V] [Nonempty V'] (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) :
    X.germToFunctionField V (f.appLE U V e s) = X.germToFunctionField V' (f.appLE U V' e' s) := by
  simp only [Scheme.germToFunctionField, Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply]

/-- The pullback of a germ along a composite with a dominant first factor, as a rational
function: the function field map of the first factor applied to the pulled back section. -/
theorem algebraMap_stalkMap_comp_germ {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (g : Y ⟶ Z) (x : X) (U : Z.Opens) (hx : (f ≫ g) x ∈ U)
    (s : Γ(Z, U)) [Nonempty (g ⁻¹ᵁ U)] :
    algebraMap (X.presheaf.stalk x) X.functionField
        ((f ≫ g).stalkMap x (Z.presheaf.germ U ((f ≫ g) x) hx s)) =
      (dominantFunctionFieldMap f).hom (Y.germToFunctionField (g ⁻¹ᵁ U) (g.app U s)) := by
  rw [Scheme.Hom.stalkMap_comp]
  change algebraMap (X.presheaf.stalk x) X.functionField
    (f.stalkMap x (g.stalkMap (f x) (Z.presheaf.germ U (g (f x)) hx s))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, ← dominantFunctionFieldMap_algebraMap,
    Scheme.algebraMap_germ_eq_germToFunctionField]

end StalkCongr

section FibreAt

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

/-- The restriction to the fibre over w of a function on the inverse image of an affine open V is
the fibre over w of the corresponding element of Γ(V) ⊗ B. -/
theorem specFibreProductFibre_appLE_eq_fibreAt (w : B →ₐ[K] K) {V : Y.Opens}
    (hV : IsAffineOpen V) (F : Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) :
    (specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V) F =
      fibreAt w ((Algebra.TensorProduct.comm K Γ(Y, V) B).symm
        ((specFibreProductSectionsEquiv hV).symm F)) := by
  have key : ∀ t : Γ(Y, V) ⊗[K] B, (specFibreProductFibre w).appLE _ V
      (specFibreProductFibre_le_preimage w V)
      (specFibreProductSectionsEquiv hV (Algebra.TensorProduct.comm K Γ(Y, V) B t)) =
        fibreAt w t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.comm_tmul, specFibreProductFibre_appLE_tmul, fibreAt_tmul,
        mul_comm]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]
  have h := key ((Algebra.TensorProduct.comm K Γ(Y, V) B).symm
    ((specFibreProductSectionsEquiv hV).symm F))
  simpa using h

end FibreAt

section GenericRestriction

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty
  specFibreProductFibre_isOver

set_option maxHeartbeats 6400000 in
/-- **Generic restriction for the product of a klt pair with a smooth affine variety.** -/
theorem kltProductGenericRestrictionStatement_holds : KltProductGenericRestrictionStatement K := by
  classical
  intro Y _ _ _ _ n hn hnorm hcov cY fY d hd D₀ heff hklt B _ _ _ _ e φ hφ V hV _ J _ g M hM
    hgz
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
  have : (specFibreProductFst K B Y).IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hUne : Nonempty (specFibreProductSnd K B Y ⁻¹ᵁ V) := specFibreProduct_preimage_nonempty V
  -- U as a scheme over K
  have : IsAffine (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme := hU
  let : (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) := ⟨(specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ ((specFibreProduct K B Y) ↘ Spec (CommRingCat.of K))⟩
  have : (specFibreProductSnd K B Y ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant (specFibreProductSnd K B Y ⁻¹ᵁ V).ι := ⟨(specFibreProductSnd K B Y ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : LocallyOfFiniteType ((specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (S := Spec (CommRingCat.of K))]
    infer_instance
  have : QuasiCompact ((specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated ((specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (specFibreProductSnd K B Y ⁻¹ᵁ V).ι
  -- the pairs on P and on U
  set cP := fibreProductEtaleChart (B := B) cY φ hφ with hcP
  set fP := fibreProductPairUnit (K := K) (B := B) fY with hfP
  set DP := fibreProductPairDivisor (K := K) (B := B) D₀ with hDP
  obtain ⟨cX⟩ : Nonempty (EtaleChart K (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme (n + e)) :=
    exists_etaleChart_on_integral_open_immersion (specFibreProductSnd K B Y ⁻¹ᵁ V).ι cP
  set fX : (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.functionFieldˣ := crepantPullbackFormUnit (specFibreProductSnd K B Y ⁻¹ᵁ V).ι hι cP fP cX with hfX
  set DX : CartierDivisor (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme := cartierPullback (specFibreProductSnd K B Y ⁻¹ᵁ V).ι DP with hDX
  -- the nonzero members and their divisors
  set gP : J → (specFibreProduct K B Y).functionField := fun j => (specFibreProduct K B Y).germToFunctionField (specFibreProductSnd K B Y ⁻¹ᵁ V) (g j) with hgP
  let J' := {j : J // gP j ≠ 0}
  have : Nonempty J' := by
    obtain ⟨j, hj⟩ := hgz
    exact ⟨⟨j, hj⟩⟩
  let uP : J' → (specFibreProduct K B Y).functionFieldˣ := fun j => Units.mk0 (gP j.1) j.2
  let A : J' → CartierDivisor (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme := fun j =>
    cartierPullback (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (principalCartierDivisor (specFibreProduct K B Y) (uP j))
  have hA : ∀ j, (A j).IsEffective := by
    intro j
    have : Nonempty (⊤ : (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    change (cartierPullback (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (principalCartierDivisor (specFibreProduct K B Y) (uP j))).IsEffective
    rw [cartierPullback_principal, CartierDivisor.isEffective_principalCartierDivisor_iff]
    refine ⟨(specFibreProductSnd K B Y ⁻¹ᵁ V).ι.appLE (specFibreProductSnd K B Y ⁻¹ᵁ V) ⊤ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι_preimage_self.ge (g j.1), ?_⟩
    rw [Units.coe_map]
    exact (dominantFunctionFieldMap_germ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (specFibreProductSnd K B Y ⁻¹ᵁ V) ⊤ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι_preimage_self.ge (g j.1)).symm
  -- a principalizing simple normal crossing model of U
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, -, -, -, -, -, Gc, hGc, hGcI, hGc0, hmin, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n + e) cX fX d DX
      (Empty.elim : Empty → CartierDivisor (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme) A hA
      (Empty.elim : Empty → (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.IdealSheafData) (fun j => j.elim)
  -- the model as a test model of P, and its discrepancy divisor
  have hρP := dominantFunctionFieldAlgHom_comp_bijective (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ρ hι hρ
  have hcompL : logDiscrepancyDivisor (n + e) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) hρP cP fP d DP cT etaleCharts_cover =
      logDiscrepancyDivisor (n + e) ρ hρ cX fX d DX cT etaleCharts_cover :=
    logDiscrepancyDivisor_comp (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ρ hι hρ cP fP d DP cX cT etaleCharts_cover
  have hsuppP : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (logDiscrepancyDivisor (n + e) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) hρP cP fP d DP cT
        etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    have h := hsupp z hz
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at h
    rw [hcompL]
    linarith
  -- generic fibre charts over D(h_fib)
  let φ' : B →+* Γ(T, ⊤) := ((ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y).appTop).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hφ' : ∀ k : K, φ' (algebraMap K B k) = Scheme.Modules.baseRingToGlobalSections K T k := by
    intro k
    have hbaseB : Scheme.Modules.baseRingToGlobalSections K (Spec (CommRingCat.of B)) k =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap K B k) := by
      rw [Scheme.Modules.baseRingToGlobalSections_apply]
      change (Spec.map (CommRingCat.ofHom (algebraMap K B))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k) = _
      rw [specMap_appTop_ΓSpecIso_inv]
      rfl
    rw [← scheme_appTop_baseRingToGlobalSections K
      (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y) k, hbaseB]
    rfl
  have : CompactSpace T := inferInstance
  obtain ⟨hfib, hfib0, hfibprop⟩ :=
    exists_generic_fibreCharts (n := n) (d := e) ξ hsnc B φ' hφ'
  -- a section of the model near the generic point, on a basic open D(F₀)
  obtain ⟨X₀, hηX₀, s₀, hs₀⟩ := exists_section_of_birational ρ hρ
  obtain ⟨F₀, hF₀le, hF₀η⟩ := hU.exists_basicOpen_le (V := (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ''ᵁ X₀)
    ⟨(specFibreProductSnd K B Y ⁻¹ᵁ V).ι (genericPoint (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme), ⟨_, hηX₀, rfl⟩⟩ (genericPoint (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme).2
  have hF₀ne : F₀ ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hF₀η
    exact hF₀η
  -- elements of Γ(V) ⊗ B
  set Eq := specFibreProductSectionsEquiv (K := K) (B := B) (T := Y) hV with hEq
  let tens : Γ(specFibreProduct K B Y, (specFibreProductSnd K B Y ⁻¹ᵁ V)) → Γ(Y, V) ⊗[K] B := fun F =>
    (Algebra.TensorProduct.comm K Γ(Y, V) B).symm (Eq.symm F)
  have htens_ne : ∀ F, F ≠ 0 → tens F ≠ 0 := by
    intro F hF h0
    apply hF
    have h1 := congrArg (fun t => Eq (Algebra.TensorProduct.comm K Γ(Y, V) B t)) h0
    simpa [tens] using h1
  obtain ⟨hiso, hiso0, hisoprop⟩ := exists_ne_zero_fibreAt (htens_ne F₀ hF₀ne)
  -- the members stay nonzero on the fibres
  have : Fintype J' := Fintype.ofFinite J'
  have hgne : ∀ j : J', g j.1 ≠ 0 := fun j h0 => j.2 (by simp [gP, h0])
  choose hnz hnz0 hnzprop using fun j : J' => exists_ne_zero_fibreAt (htens_ne _ (hgne j))
  refine ⟨hfib * hiso * ∏ j, hnz j, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hfib0 hiso0) (Finset.prod_ne_zero_iff.mpr fun j _ => hnz0 j)
  intro w hw y hy hyc hbad
  rw [map_mul, map_mul, map_prod] at hw
  have hwfib : w hfib ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hw)
  have hwiso : w hiso ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hw)
  have hwnz : ∀ j, w (hnz j) ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hw) j (Finset.mem_univ j)
  obtain ⟨Uu, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, x, hye, hApos, hineq⟩ := hbad
  -- the part of the test model over V
  have heV : σ (x : Uu) ∈ V := (specializes_iff_mem_closure.mpr hye).mem_open V.isOpen hy
  let U' : Uu.Opens := σ ⁻¹ᵁ V
  have : Nonempty U' := ⟨⟨(x : Uu), heV⟩⟩
  let : U'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U'.ι ≫ (Uu ↘ Spec (CommRingCat.of K))⟩
  have : U'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant U'.ι := ⟨U'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (U'.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := U'.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (U'.ι ≫ (Uu ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : Smooth (U'.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : IsDominant (σ ∣_ V) := isDominant_morphismRestrict_integral σ V
  have : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hsq : (σ ∣_ V) ≫ V.ι = U'.ι ≫ σ := morphismRestrict_ι σ V
  have hbij : Function.Bijective (U'.ι.stalkMap ⟨(x : Uu), heV⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let e' : CodimensionOnePoint U'.toScheme :=
    ⟨⟨(x : Uu), heV⟩, (coheight_eq_of_stalkMap_bijective U'.ι ⟨(x : Uu), heV⟩ hbij).trans
      x.property⟩
  -- the test model mapped into the fibre of U over w
  have hrange : Set.range (V.ι ≫ specFibreProductFibre (V := Y) w) ⊆ Set.range (specFibreProductSnd K B Y ⁻¹ᵁ V).ι := by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨_, specFibreProductFibre_le_preimage w V v.2⟩, rfl⟩
  let iV : V.toScheme ⟶ (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.lift (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (V.ι ≫ specFibreProductFibre (V := Y) w) hrange
  have hiV : iV ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι = V.ι ≫ specFibreProductFibre (V := Y) w :=
    IsOpenImmersion.lift_fac _ _ _
  have hiVs : iV ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductSnd K B Y = V.ι := by
    rw [← Category.assoc, hiV, Category.assoc, specFibreProductFibre_snd, Category.comp_id]
  have hiVf : iV ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y =
      V.ι ≫ (Y ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom) := by
    rw [← Category.assoc, hiV, Category.assoc, specFibreProductFibre_fst]
  let τ : U'.toScheme ⟶ (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme := (σ ∣_ V) ≫ iV
  have hτη : τ (genericPoint U'.toScheme) ∈ X₀ := by
    have h1 : (σ ∣_ V) (genericPoint U'.toScheme) = genericPoint V.toScheme :=
      dominant_map_genericPoint (σ ∣_ V)
    have h2 : V.ι (genericPoint V.toScheme) = genericPoint Y := dominant_map_genericPoint V.ι
    have h3 : (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (τ (genericPoint U'.toScheme)) =
        specFibreProductFibre (V := Y) w (genericPoint Y) := by
      change (iV ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ((σ ∣_ V) (genericPoint U'.toScheme)) = _
      rw [hiV, h1, Scheme.Hom.comp_apply, h2]
    have hne : (specFibreProductFibre (V := Y) w).appLE _ V
        (specFibreProductFibre_le_preimage w V) F₀ ≠ 0 := by
      rw [specFibreProductFibre_appLE_eq_fibreAt w hV]
      exact hisoprop w hwiso
    have hηV : genericPoint Y ∈ V := by
      rw [← h2]
      exact (genericPoint V.toScheme).2
    have hbo : genericPoint Y ∈ Y.basicOpen ((specFibreProductFibre (V := Y) w).appLE _ V
        (specFibreProductFibre_le_preimage w V) F₀) := by
      rw [Scheme.mem_basicOpen _ _ _ hηV]
      refine isUnit_iff_ne_zero.mpr fun h0 => hne ?_
      exact Scheme.germToFunctionField_injective Y V (h0.trans (map_zero _).symm)
    rw [Scheme.basicOpen_appLE] at hbo
    have hmem : (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (τ (genericPoint U'.toScheme)) ∈ (specFibreProduct K B Y).basicOpen F₀ := by
      rw [h3]
      exact hbo.2
    obtain ⟨z, hz, hzeq⟩ := hF₀le hmem
    have hz' : z = τ (genericPoint U'.toScheme) := (specFibreProductSnd K B Y ⁻¹ᵁ V).ι.isOpenEmbedding.injective hzeq
    rw [← hz']
    exact hz
  -- the lift to the model near x
  have : IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (e' : U'.toScheme)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) e'
  obtain ⟨W, heW, α, hα⟩ := exists_local_lift_of_section ρ X₀ s₀ hs₀ τ hτη (e' : U'.toScheme)
  have : Nonempty W := ⟨⟨(e' : U'.toScheme), heW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : W.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨W.ι ≫ (U'.toScheme ↘ Spec (CommRingCat.of K))⟩
  have : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U'.toScheme ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have hbijW : Function.Bijective (W.ι.stalkMap ⟨(e' : U'.toScheme), heW⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let eW : CodimensionOnePoint W.toScheme :=
    ⟨⟨(e' : U'.toScheme), heW⟩, (coheight_eq_of_stalkMap_bijective W.ι ⟨(e' : U'.toScheme), heW⟩
      hbijW).trans e'.property⟩
  -- the test map α ≫ (ρ ≫ ι) ≫ π is the restriction of σ, and α ≫ (ρ ≫ ι) ≫ fst is constant
  have heq : α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y = W.ι ≫ U'.ι ≫ σ := by
    have h1 : α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y =
        (α ≫ ρ) ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductSnd K B Y := by
      simp only [Category.assoc]
    rw [h1, hα]
    simp only [τ, Category.assoc, hiVs]
    rw [hsq]
  have hαfst : α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductFst K B Y =
      (W.toScheme ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom) := by
    have h1 : α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductFst K B Y =
        (α ≫ ρ) ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y := by
      simp only [Category.assoc]
    rw [h1, hα]
    simp only [τ, Category.assoc, hiVf]
    rw [← Category.assoc (σ ∣_ V) V.ι, hsq, Category.assoc, ← Category.assoc σ,
      HomIsOver.comp_over]
    rfl
  have : α.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    have h1 := congrArg (· ≫ (Y ↘ Spec (CommRingCat.of K))) heq
    simp only [Category.assoc, HomIsOver.comp_over] at h1
    exact h1
  -- the test map is birational
  have hU'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) U'.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion U'.ι
  have hWι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  have hσU' := dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι
  have hσW := dominantFunctionFieldAlgHom_comp_bijective (U'.ι ≫ σ) W.ι hσU' hWι
  have : IsDominant (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y) := by
    rw [heq]
    infer_instance
  have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K)
      (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y)) := by
    rw [dominantFunctionFieldAlgHom_congr_hom heq]
    exact hσW
  -- the points
  set t₀ : T := α (eW : W.toScheme) with ht₀
  have hρt₀ : ρ t₀ = τ (e' : U'.toScheme) := by
    change (α ≫ ρ) (eW : W.toScheme) = _
    rw [hα]
    rfl
  set p₀ : specFibreProduct K B Y := specFibreProductFibre (V := Y) w y with hp₀
  have hτp : (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (ρ t₀) ⤳ p₀ := by
    rw [hρt₀]
    have h1 : (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (τ (e' : U'.toScheme)) = specFibreProductFibre (V := Y) w (σ (x : Uu)) := by
      change (iV ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ((σ ∣_ V) (e' : U'.toScheme)) = _
      rw [hiV, Scheme.Hom.comp_apply]
      congr 1
      rw [← Scheme.Hom.comp_apply, hsq]
      rfl
    rw [h1]
    exact (specializes_iff_mem_closure.mpr hye).map (specFibreProductFibre (V := Y) w).continuous
  -- the functions of B pulled back to T are units at t₀ when w does not kill them
  have hunit_of : ∀ c : B, w c ≠ 0 → IsUnit (T.presheaf.germ ⊤ t₀ trivial (φ' c)) := by
    intro c hc
    rw [← Scheme.mem_basicOpen_top]
    have h1 : T.basicOpen (φ' c) = (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y) ⁻¹ᵁ
        (Spec (CommRingCat.of B)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv c) := by
      rw [Scheme.preimage_basicOpen_top]
      rfl
    rw [h1]
    have hαf' : α ≫ ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y =
        (W.toScheme ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom) := by
      simpa only [Category.assoc] using hαfst
    have h2 : (eW : W.toScheme) ∈ (α ≫ ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y) ⁻¹ᵁ
        (Spec (CommRingCat.of B)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv c) := by
      have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).inv
          ((CommRingCat.ofHom w.toRingHom) c)) := (IsUnit.mk0 (w c) hc).map _
      rw [hαf', Scheme.Hom.comp_preimage, Scheme.preimage_basicOpen_top,
        specMap_appTop_ΓSpecIso_inv, Scheme.basicOpen_of_isUnit _ hu]
      trivial
    exact h2
  -- the fibre chart at t₀
  have hu'et : (MvPolynomial.aeval (R := K) (fun l =>
      algebraMap B (Localization.Away hfib) (φ (MvPolynomial.X l)))).toRingHom.FormallyEtale := by
    have hloc : (IsScalarTower.toAlgHom K B (Localization.Away hfib)).toRingHom.FormallyEtale := by
      have : Algebra.FormallyEtale B (Localization.Away hfib) :=
        Algebra.FormallyEtale.of_isLocalization (Submonoid.powers hfib)
      exact RingHom.formallyEtale_algebraMap.mpr this
    have heq' : MvPolynomial.aeval (R := K) (fun l =>
        algebraMap B (Localization.Away hfib) (φ (MvPolynomial.X l))) =
          (IsScalarTower.toAlgHom K B (Localization.Away hfib)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro l
      simp
    rw [heq']
    exact formallyEtale_comp _ hloc _ hφ
  obtain ⟨F, hF, σF, hFsnc, hσF, hFcoord⟩ :=
    hfibprop t₀ (hunit_of hfib hwfib) (fun l => φ (MvPolynomial.X l)) hfib
      (hunit_of hfib hwfib) hu'et
  -- the conditions at the generic points for the product chart
  have hspecT : α (genericPoint W.toScheme) ⤳ t₀ :=
    ((genericPoint_spec W.toScheme).specializes (Set.mem_univ _)).map α.continuous
  have hFη : α (genericPoint W.toScheme) ∈ F.U := hspecT.mem_open F.U.isOpen hF
  have hYη : (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y) (genericPoint W.toScheme) ∈ cY.U := by
    rw [dominant_map_genericPoint]
    exact ((genericPoint_spec Y).mem_open_set_iff cY.U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty cY.U))
  have hPη : (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (α (genericPoint W.toScheme)) ∈
      specFibreProductSnd K B Y ⁻¹ᵁ cY.U := hYη
  have hFgen : ∀ l : Fin e, etaleChartStalkCoords F _ hFη (MvPolynomial.X (Fin.natAdd n l)) =
      T.presheaf.germ ⊤ (α (genericPoint W.toScheme)) trivial (φ' (φ (MvPolynomial.X l))) := by
    intro l
    have h1 := congrArg (fun z => T.presheaf.stalkSpecializes hspecT z) (hFcoord l)
    simp only [TopCat.Presheaf.germ_stalkSpecializes_apply] at h1
    rw [← h1]
    change T.presheaf.germ F.U _ hFη (F.coords (MvPolynomial.X (Fin.natAdd n l))) =
      T.presheaf.stalkSpecializes hspecT (T.presheaf.germ F.U t₀ hF
        (F.coords (MvPolynomial.X (Fin.natAdd n l))))
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hP1 : ∀ i : Fin n, schemeStalkMapAlgHom (K := K)
      (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y) (genericPoint W.toScheme)
        (etaleChartStalkCoords cY _ hYη (MvPolynomial.X i)) =
      schemeStalkMapAlgHom (K := K) α (genericPoint W.toScheme) (schemeStalkMapAlgHom (K := K)
        (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (α (genericPoint W.toScheme)) (etaleChartStalkCoords cP _ hPη
          (MvPolynomial.X (Fin.castAdd e i)))) := by
    intro i
    have hc : etaleChartStalkCoords cP _ hPη (MvPolynomial.X (Fin.castAdd e i)) =
        (specFibreProductSnd K B Y).stalkMap _ (etaleChartStalkCoords cY _ hYη (MvPolynomial.X i)) := by
      change (specFibreProduct K B Y).presheaf.germ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) _ hPη
          (fibreProductCoords cY φ (MvPolynomial.X (Fin.castAdd e i))) =
        (specFibreProductSnd K B Y).stalkMap _ (Y.presheaf.germ cY.U _ hYη
          (cY.coords (MvPolynomial.X i)))
      rw [fibreProductCoords_X_castAdd, specFibreProductSectionsEquiv_tmul, map_one, one_mul,
        germ_appLE_eq_stalkMap_germ]
      rfl
    rw [hc, schemeStalkMapAlgHom_apply, schemeStalkMapAlgHom_apply, schemeStalkMapAlgHom_apply,
      Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    rfl
  have hP2 : ∀ l : Fin e, schemeStalkMapAlgHom (K := K) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (α (genericPoint W.toScheme))
      (etaleChartStalkCoords cP _ hPη (MvPolynomial.X (Fin.natAdd n l))) =
      etaleChartStalkCoords F _ hFη (MvPolynomial.X (Fin.natAdd n l)) := by
    intro l
    rw [hFgen l]
    change schemeStalkMapAlgHom (K := K) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) _
      ((specFibreProduct K B Y).presheaf.germ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) _ hPη
        (fibreProductCoords cY φ (MvPolynomial.X (Fin.natAdd n l)))) = _
    rw [fibreProductCoords_X_natAdd, specFibreProductSectionsEquiv_tmul, map_one, mul_one]
    change schemeStalkMapAlgHom (K := K) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) _
      ((specFibreProduct K B Y).presheaf.germ (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) _ hPη
        (((specFibreProduct K B Y).baseRingToStructurePresheaf B).app
          (op (specFibreProductSnd K B Y ⁻¹ᵁ cY.U))
          (φ (MvPolynomial.X l)))) = _
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.comp_apply,
      germ_appLE_eq_stalkMap_germ, schemeStalkMapAlgHom_apply]
    have h := stalkMap_germ_top (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ≫ specFibreProductFst K B Y)
      (α (genericPoint W.toScheme)) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ (MvPolynomial.X l)))
    simp only [Scheme.Hom.stalkMap_comp, CommRingCat.comp_apply] at h ⊢
    exact h
  have hP3 : ∀ l : Fin e, ∃ κ : K, schemeStalkMapAlgHom (K := K) α (genericPoint W.toScheme)
      (etaleChartStalkCoords F _ hFη (MvPolynomial.X (Fin.natAdd n l))) = algebraMap K _ κ := by
    intro l
    refine ⟨w (φ (MvPolynomial.X l)), ?_⟩
    rw [hFgen l, schemeStalkMapAlgHom_apply, stalkMap_germ_top]
    have hs : α.appTop (φ' (φ (MvPolynomial.X l))) =
        Scheme.Modules.baseRingToGlobalSections K W.toScheme (w (φ (MvPolynomial.X l))) := by
      change (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductFst K B Y).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ (MvPolynomial.X l))) = _
      rw [hαfst, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMap_appTop_ΓSpecIso_inv,
        Scheme.Modules.baseRingToGlobalSections_apply]
      rfl
    rw [hs]
    rfl
  -- the log discrepancy inequality along x
  obtain ⟨cW₀, -⟩ : ∃ c : EtaleChart K W.toScheme n, (eW : W.toScheme) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
      Opens.mem_top _)
  have hcore := fibre_snc_logDiscrepancy_le α (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) hρP (specFibreProductSnd K B Y) hσ' cP
    cT cY cW₀ fY d D₀ ξ hinj hcoh hsnc hsuppP eW F hF σF hFsnc hσF hFη hPη hYη hP1 hP2 hP3
  obtain ⟨cU'₀, -⟩ : ∃ c : EtaleChart K U'.toScheme n, (e' : U'.toScheme) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := U'.toScheme) (n := n)).symm ▸
      Opens.mem_top _)
  have hlogW : cartierCoefficient (logDiscrepancyDivisor n
      (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y) hσ' cY fY d D₀ cW₀ etaleCharts_cover)
        (eW : W.toScheme) =
      cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover)
        (x : Uu) := by
    rw [logDiscrepancyDivisor_congr_hom heq hσ' hσW,
      logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective (U'.ι ≫ σ) W.ι hσU' hWι cY
        fY d D₀ cU'₀ cW₀ eW e'.property hbijW]
    exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ U'.ι hσ hU'ι cY fY d
      D₀ cU cU'₀ e' x.property hbij
  rw [hlogW] at hcore
  -- the members of the family along x
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + e) _
  have : Smooth (W.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (Uu ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have : IsDiscreteValuationRing (W.toScheme.presheaf.stalk (eW : W.toScheme)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eW
  have : IsDiscreteValuationRing (Uu.presheaf.stalk (U'.ι (e' : U'.toScheme))) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨U'.ι (e' : U'.toScheme), x.property⟩ : CodimensionOnePoint Uu)
  have : IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (W.ι (eW : W.toScheme))) :=
    ‹IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (e' : U'.toScheme))›
  let gU : J' → Γ((specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme, ⊤) := fun j => (specFibreProductSnd K B Y ⁻¹ᵁ V).ι.appLE (specFibreProductSnd K B Y ⁻¹ᵁ V) ⊤ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι_preimage_self.ge (g j.1)
  let q : J' → T.presheaf.stalk t₀ := fun j => T.presheaf.germ ⊤ t₀ trivial (ρ.appTop (gU j))
  have hαι : α ≫ ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι = (W.ι ≫ U'.ι ≫ σ) ≫ specFibreProductFibre (V := Y) w := by
    rw [← Category.assoc α ρ, hα]
    simp only [τ, Category.assoc]
    rw [hiV, ← Category.assoc (σ ∣_ V) V.ι, hsq]
    simp only [Category.assoc]
  have hqval : ∀ j : J', algebraMap (W.toScheme.presheaf.stalk (eW : W.toScheme))
      W.toScheme.functionField (α.stalkMap (eW : W.toScheme) (q j)) =
        dominantFunctionFieldAlgHom (K := K) (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y)
          (Y.germToFunctionField V ((specFibreProductFibre (V := Y) w).appLE _ V
            (specFibreProductFibre_le_preimage w V) (g j.1))) := by
    intro j
    have hmem : (α ≫ ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (eW : W.toScheme) ∈ (specFibreProductSnd K B Y ⁻¹ᵁ V) := ((α ≫ ρ) (eW : W.toScheme)).2
    have h1 : α.stalkMap (eW : W.toScheme) (q j) = (α ≫ ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι).stalkMap (eW : W.toScheme)
        ((specFibreProduct K B Y).presheaf.germ (specFibreProductSnd K B Y ⁻¹ᵁ V) _ hmem (g j.1)) := by
      change α.stalkMap _ (T.presheaf.germ ⊤ t₀ trivial
        (ρ.appTop ((specFibreProductSnd K B Y ⁻¹ᵁ V).ι.appLE (specFibreProductSnd K B Y ⁻¹ᵁ V) ⊤ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι_preimage_self.ge (g j.1)))) = _
      rw [← stalkMap_germ_top, germ_appLE_eq_stalkMap_germ, Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_comp]
      rfl
    have hmem' : ((W.ι ≫ U'.ι ≫ σ) ≫ specFibreProductFibre (V := Y) w) (eW : W.toScheme) ∈
        (specFibreProductSnd K B Y ⁻¹ᵁ V) := hαι ▸ hmem
    have : Nonempty (specFibreProductFibre (V := Y) w ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V)) :=
      ⟨⟨_, specFibreProductFibre_le_preimage w V (genericPoint V.toScheme).2⟩⟩
    rw [h1, algebraMap_stalkMap_germ_of_eq hαι _ (specFibreProductSnd K B Y ⁻¹ᵁ V) hmem hmem' (g j.1),
      algebraMap_stalkMap_comp_germ, dominantFunctionFieldAlgHom_congr_hom heq]
    change _ = (dominantFunctionFieldMap (W.ι ≫ U'.ι ≫ σ)).hom _
    congr 1
    rw [Scheme.Hom.app_eq_appLE]
    exact germToFunctionField_appLE _ _ _ _ _ _ _
  have hordj : ∀ j : J', Uu.ord ((dominantFunctionFieldMap σ).hom (Y.germToFunctionField V
      ((specFibreProductFibre (V := Y) w).appLE _ V (specFibreProductFibre_le_preimage w V)
        (g j.1)))) (x : Uu) = fibreOrd α (eW : W.toScheme) (q j) := by
    intro j
    unfold fibreOrd
    rw [hqval j, dominantFunctionFieldAlgHom_congr_hom heq, dominantFunctionFieldAlgHom_comp,
      AlgHom.comp_apply, dominantFunctionFieldAlgHom_comp, AlgHom.comp_apply]
    exact ((scheme_ord_pullback_of_stalkMap_bijective W.ι eW e'.property hbijW _).trans
      (scheme_ord_pullback_of_stalkMap_bijective U'.ι e' x.property hbij
        (dominantFunctionFieldAlgHom (K := K) σ _))).symm
  have hfibne : ∀ j : J', Y.germToFunctionField V ((specFibreProductFibre (V := Y) w).appLE _ V
      (specFibreProductFibre_le_preimage w V) (g j.1)) ≠ 0 := by
    intro j h2
    have h3 : (specFibreProductFibre (V := Y) w).appLE _ V (specFibreProductFibre_le_preimage w V)
        (g j.1) = 0 := Scheme.germToFunctionField_injective Y V (h2.trans (map_zero _).symm)
    rw [specFibreProductFibre_appLE_eq_fibreAt w hV] at h3
    exact hnzprop j w (hwnz j) h3
  have hqne : ∀ j : J', α.stalkMap (eW : W.toScheme) (q j) ≠ 0 := by
    intro j h0
    have h1 := hqval j
    rw [h0, map_zero] at h1
    exact hfibne j ((map_eq_zero_iff _ (dominantFunctionFieldAlgHom (K := K)
      (α ≫ (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) ≫ specFibreProductSnd K B Y)).toRingHom.injective).mp h1.symm)
  have hqT : ∀ j : J', algebraMap (T.presheaf.stalk t₀) T.functionField (q j) ≠ 0 := by
    intro j h0
    apply hqne j
    rw [(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h0, map_zero]
  have : Nonempty (⊤ : (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have hAq : ∀ j : J', (cartierPullback ρ (A j)).IsLocalEquationAt t₀ (Units.mk0 _ (hqT j)) := by
    intro j
    have hloc0 : (A j).IsLocalEquationAt (ρ t₀)
        (Units.map (dominantFunctionFieldMap (specFibreProductSnd K B Y ⁻¹ᵁ V).ι).hom.toMonoidHom (uP j)) :=
      cartierPullback_isLocalEquationAt (specFibreProductSnd K B Y ⁻¹ᵁ V).ι _ (ρ t₀)
        (CartierDivisor.isLocalEquationAt_principalCartierDivisor _ (uP j))
    have h1 := cartierPullback_isLocalEquationAt ρ (A j) t₀ hloc0
    have h2 : Units.mk0 _ (hqT j) = Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (Units.map (dominantFunctionFieldMap (specFibreProductSnd K B Y ⁻¹ᵁ V).ι).hom.toMonoidHom (uP j)) := by
      apply Units.ext
      rw [Units.val_mk0, Units.coe_map, Units.coe_map]
      change _ = (dominantFunctionFieldMap ρ).hom ((dominantFunctionFieldMap (specFibreProductSnd K B Y ⁻¹ᵁ V).ι).hom
        ((specFibreProduct K B Y).germToFunctionField (specFibreProductSnd K B Y ⁻¹ᵁ V) (g j.1)))
      rw [dominantFunctionFieldMap_germ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (specFibreProductSnd K B Y ⁻¹ᵁ V) ⊤ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι_preimage_self.ge (g j.1),
        ← (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.algebraMap_germ_eq_germToFunctionField
          (show ρ t₀ ∈ (⊤ : (specFibreProductSnd K B Y ⁻¹ᵁ V).toScheme.Opens) from trivial),
        dominantFunctionFieldMap_algebraMap, stalkMap_germ_top]
    rw [h2]
    exact h1
  -- a member of the family realising the principalized ideal at t₀
  obtain ⟨j₁, f₁, hGcf, hAf⟩ :=
    exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ A hA Gc hGc
      hGcI t₀
  obtain ⟨u₁, hu₁⟩ := hAf.exists_unit_mul_eq (hAq j₁)
  have hGcq : Gc.IsLocalEquationAt t₀ (Units.mk0 _ (hqT j₁)) :=
    isLocalEquationAt_of_eq_unit_mul hGcf u₁ hu₁.symm
  have hnormT : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have hGsum := fibreOrd_snc_local_equation_of_ne_zero α eW hnormT F hF ξ hinj hcoh σF hFsnc Gc
    hGc0 (fun i => cartierCoefficient_nonneg_of_isEffective Gc hGc (ξ i)) _ (hqT j₁) hGcq
    (hqne j₁)
  -- the weighted inequality
  set crep : Fin r → ℤ := fun s =>
    cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover) (ξ s)
    with hcrep
  set G : Fin r → ℤ := fun s => cartierCoefficient Gc (ξ s) with hG
  set o : Fin r → ℤ := fun s => fibreSNCOrder α (eW : W.toScheme) F hF σF s with hodef
  set logY : ℤ := cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
    etaleCharts_cover) (x : Uu) with hlogY
  have hL : ∀ s, cartierCoefficient (logDiscrepancyDivisor (n + e) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) hρP cP fP d DP cT
      etaleCharts_cover) (ξ s) = - crep s := by
    intro s
    rw [hcompL]
    change _ = - cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover)
      (ξ s)
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, neg_neg]
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hb := hineq j₁.1 (hfibne j₁)
  rw [hordj j₁, hGsum] at hb
  have hbZ : (M : ℤ) * ((d : ℤ) + logY) ≤ (d : ℤ) * ∑ s, G s * o s := by
    have hb' : (M : ℝ) * (((d : ℝ) + (logY : ℝ)) / d) ≤ ((∑ s, G s * o s : ℤ) : ℝ) := hb
    have h1 : (M : ℝ) * (((d : ℝ) + (logY : ℝ)) / d) * d =
        (M : ℝ) * ((d : ℝ) + (logY : ℝ)) := by
      field_simp
    have h2 : (M : ℝ) * ((d : ℝ) + (logY : ℝ)) ≤ (d : ℝ) * ((∑ s, G s * o s : ℤ) : ℝ) := by
      rw [← h1]
      nlinarith
    exact_mod_cast h2
  have hAZ : 0 < (d : ℤ) + logY := by
    have : (0 : ℝ) < ((d : ℝ) + (logY : ℝ)) / d := hApos
    have h2 : (0 : ℝ) < (d : ℝ) + (logY : ℝ) := by
      by_contra hneg
      push Not at hneg
      have : ((d : ℝ) + (logY : ℝ)) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hdR.le
      linarith
    exact_mod_cast h2
  have hdisc : (d : ℤ) * ∑ s, o s - ∑ s, crep s * o s ≤ (d : ℤ) + logY := by
    have h := hcore
    have hL' : ∀ s, cartierCoefficient (logDiscrepancyDivisor (n + e) (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) hρP cP
        (Units.map (dominantFunctionFieldMap (specFibreProductSnd K B Y)).hom.toMonoidHom fY) d
        (cartierPullback (specFibreProductSnd K B Y) D₀) cT etaleCharts_cover) (ξ s) = - crep s :=
      hL
    simp only [hL'] at h
    have hneg : ∑ s, -crep s * o s = - ∑ s, crep s * o s := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hneg] at h
    linarith
  have hsum : (M : ℤ) * ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s ≤
      ∑ s, ((d : ℤ) * G s) * o s := by
    have h1 : ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s =
        (d : ℤ) * ∑ s, o s - ∑ s, crep s * o s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h2 : ∑ s, ((d : ℤ) * G s) * o s = (d : ℤ) * ∑ s, G s * o s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [h1, h2]
    have hM0 : (0 : ℤ) ≤ M := by positivity
    exact (mul_le_mul_of_nonneg_left hdisc hM0).trans hbZ
  have hpos : 0 < ∑ s, ((d : ℤ) * G s) * o s := by
    have h2 : ∑ s, ((d : ℤ) * G s) * o s = (d : ℤ) * ∑ s, G s * o s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [h2]
    have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    nlinarith
  obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge
    (fun s => fibreSNCOrder_nonneg α (eW : W.toScheme) F hF σF s) hsum hpos
  have hts : t₀ ∈ closure ({ξ s} : Set T) := by
    by_contra hnot
    exact hos.ne' (fibreSNCOrder_eq_zero_of_notMem_closure α (eW : W.toScheme) F hF ξ σF hFsnc s
      hnot)
  -- the bad member is a weakly bad test prime of P through (w, y)
  refine ⟨T, hTi, inferInstance, hTo, hTs, ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι, inferInstance, inferInstance, hρP, cT,
    ⟨ξ s, hcoh s⟩, ?_, ?_⟩
  · have h1 : (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι) (ξ s) ⤳ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (ρ t₀) :=
      (specializes_iff_mem_closure.mpr hts).map (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι).continuous
    exact specializes_iff_mem_closure.mp (h1.trans hτp)
  · intro j hj
    have hordT : T.ord ((dominantFunctionFieldMap (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι)).hom (gP j)) (ξ s) =
        cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := by
      change _ = cartierCoefficient (cartierPullback ρ
        (cartierPullback (specFibreProductSnd K B Y ⁻¹ᵁ V).ι (principalCartierDivisor (specFibreProduct K B Y) (uP ⟨j, hj⟩))))
          (ξ s)
      rw [← cartierPullback_comp (specFibreProductSnd K B Y ⁻¹ᵁ V).ι ρ, cartierPullback_principal, cartierCoefficient_principal]
      rfl
    have hmin1 := (hmin (ξ s)).1 ⟨j, hj⟩
    have hsZ : (M : ℤ) * (1 + ((d : ℤ) - 1 - crep s)) ≤ (d : ℤ) * G s := hs
    have hG1 : G s ≤ cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := hmin1
    rw [hL s]
    have hfinZ : (M : ℤ) * ((d : ℤ) - crep s) ≤
        (d : ℤ) * T.ord ((dominantFunctionFieldMap (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι)).hom (gP j)) (ξ s) := by
      rw [hordT]
      nlinarith
    have hfinR : (M : ℝ) * ((d : ℝ) - (crep s : ℝ)) ≤
        (d : ℝ) * ((T.ord ((dominantFunctionFieldMap (ρ ≫ (specFibreProductSnd K B Y ⁻¹ᵁ V).ι)).hom (gP j)) (ξ s) : ℤ) : ℝ) := by
      exact_mod_cast hfinZ
    have key : (M : ℝ) * (((d : ℝ) + ((-crep s : ℤ) : ℝ)) / d) =
        ((M : ℝ) * ((d : ℝ) - (crep s : ℝ))) / d := by
      push_cast
      ring
    rw [key, div_le_iff₀ hdR]
    linarith

/-- **K-NF from restriction to the fibres of products** (Kawamata–Viehweg vanishing and generic
restriction are proved). -/
theorem kawamataNumericalFreeness_of_productFibreRestriction
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductFibreRestrictionStatement K) :
    KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_productRestriction
    (fun _ _ _ _ => kltProductGenericRestrictionStatement_holds) hfib

/-- **F2 from restriction to the fibres of products, the base point free theorem for klt pairs
and Ambro's canonical bundle formula for contractions to lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_productFibreRestriction_of_basePointFree_of_ambro
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltProductFibreRestrictionStatement K)
    (hbpf : KltBasePointFreeStatement.{u}) (hamb : AmbroStrictDimensionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_productRestriction_of_basePointFree_of_ambro
    (fun _ _ _ _ => kltProductGenericRestrictionStatement_holds) hfib hbpf hamb

end GenericRestriction

end MixedFujita
