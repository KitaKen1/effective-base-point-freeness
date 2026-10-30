/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHyperplaneTestModel
public import MixedFujita.SNCBoundaryLocalProduct
public import MixedFujita.NormalCartierLocalUnits
public import MixedFujita.SNCCoordinateOrders
public import MixedFujita.KltProductPairProperties
public import MixedFujita.EtaleChartPolynomialMaps

/-!
Adjunction along the strict transform of a hyperplane of the product (step 15, the klt restriction
theorem).

Let ρ : T → P = Spec B ×_K Y be a smooth model of the product pair with SNC family ξ, c an SNC
chart of T at a point t' in which the strict transform ξ_{s₀} of the hyperplane u_0 = 0 is the
hyperplane y_0 = 0 and another member ξ_j is y_1 = 0, and U = Spec(Γ(T, c.U)/(y_0)) the test model
of H = Spec(B/(u_0)) ×_K Y (`hyperplaneTestMap`). The helpers below are the pieces of the
computation of the log discrepancy of U → H along the component e of ξ_j ∩ U through t':

* the generic point of U goes to the strict transform, and residues of chart sections are their
  classes (`hyperplaneTestInclusion_genericPoint`, `hyperplaneTest_residue_germ`);
* a unit of the function field of an integral scheme is the germ of a unit section
  (`exists_unit_section_germ`);
* the combination λ₁ λ₂^{−d} y_0^d of local equations of two divisors supported on the family,
  with coefficients 0 and 1 along ξ_{s₀}, is a stalk unit times a monomial in the other component
  equations (`snc_local_equation_combination`).
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

section Generic

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  {N : ℕ} (c : EtaleChart K T (N + 1)) [(Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime]

attribute [local instance] specAlgebraOver hyperplaneTestInclusion_isOver

omit [IsIntegral T] in
/-- The generic point of the test model goes to the point of T whose prime in Γ(T, c.U) is
(y_0). -/
theorem hyperplaneTestInclusion_genericPoint (ζ : T) (hζ : ζ ∈ c.U)
    (hprime : Ideal.span {c.coords (MvPolynomial.X 0)} =
      (c.isAffine.primeIdealOf ⟨ζ, hζ⟩).asIdeal) :
    hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))) = ζ := by
  apply specAlgebraHom_apply_of_comap c.isAffine _ _ ζ hζ
  rw [genericPoint_eq_bot_of_affine]
  change (⊥ : Ideal (hyperplaneTestRing c)).comap (Ideal.Quotient.mkₐ K _) = _
  rw [← RingHom.ker_eq_comap_bot, ← hprime]
  exact Ideal.mk_ker

omit [IsIntegral T] in
/-- **Residues of chart sections**: the image in the function field of the test model of the germ
of a section s of Γ(T, c.U) at the image of the generic point is the class of s. -/
theorem hyperplaneTest_residue_germ (s : Γ(T, c.U))
    (h : hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))) ∈
      c.U) :
    stalkFunctionFieldAlgHom (K := K) (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
        (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c) _
          (T.presheaf.germ c.U _ h s)) =
      (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv
          (Ideal.Quotient.mk _ s)) := by
  have : Nonempty (hyperplaneTestInclusion c ⁻¹ᵁ c.U) :=
    ⟨⟨genericPoint _, h⟩⟩
  rw [stalkFunctionFieldAlgHom_stalkMap_germ]
  have hle : (⊤ : (Spec (CommRingCat.of (hyperplaneTestRing c))).Opens) ≤
      hyperplaneTestInclusion c ⁻¹ᵁ c.U := specAlgebraHom_top_le c.isAffine _
  have he : (hyperplaneTestInclusion c).appLE c.U ⊤ hle s =
      (Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.map (homOfLE hle).op
        ((hyperplaneTestInclusion c).app c.U s) := rfl
  have h2 := specAlgebraHom_appLE c.isAffine
    (Ideal.Quotient.mkₐ K (Ideal.span {c.coords (MvPolynomial.X 0)})) s
  change (hyperplaneTestInclusion c).appLE c.U ⊤ hle s = _ at h2
  rw [← germToFunctionField_restrict _ hle, ← he, h2]
  rfl

end Generic

section Units

variable {X : Scheme.{u}} [IsIntegral X]

/-- A unit of the function field of an integral scheme is the germ of a unit section over a
nonempty open. -/
theorem exists_unit_section_germ (f : X.functionFieldˣ) :
    ∃ (W : X.Opens) (_ : Nonempty W) (a : Γ(X, W)ˣ),
      X.germToFunctionField W (a : Γ(X, W)) = (f : X.functionField) := by
  obtain ⟨U₁, hU₁, a₁, ha₁⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) (f : X.functionField)
  obtain ⟨U₂, hU₂, a₂, ha₂⟩ := X.presheaf.exists_germ_eq (x := genericPoint X)
    ((f⁻¹ : X.functionFieldˣ) : X.functionField)
  let W := U₁ ⊓ U₂
  have hW : genericPoint X ∈ W := ⟨hU₁, hU₂⟩
  have : Nonempty W := ⟨⟨genericPoint X, hW⟩⟩
  have : Nonempty U₁ := ⟨⟨genericPoint X, hU₁⟩⟩
  have : Nonempty U₂ := ⟨⟨genericPoint X, hU₂⟩⟩
  let b₁ := X.presheaf.map (homOfLE (inf_le_left : W ≤ U₁)).op a₁
  let b₂ := X.presheaf.map (homOfLE (inf_le_right : W ≤ U₂)).op a₂
  have hb₁ : X.germToFunctionField W b₁ = (f : X.functionField) := by
    rw [germToFunctionField_restrict]
    exact ha₁
  have hb₂ : X.germToFunctionField W b₂ = ((f⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [germToFunctionField_restrict]
    exact ha₂
  have hprod : b₁ * b₂ = 1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul, hb₁, hb₂, map_one, Units.mul_inv]
  exact ⟨W, inferInstance, ⟨b₁, b₂, hprod, (mul_comm b₂ b₁).trans hprod⟩, hb₁⟩

end Units

section Combination

variable {K : Type u} [Field K] {n : ℕ} {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]

/-- **The combination of two local products**: for divisors D₁, D₂ supported on an SNC family,
local equations λ₁, λ₂ of them at a point t of an SNC chart c and a member ξ_{s₀},
λ₁ λ₂^{−d} g_{s₀}^d is a stalk unit at t times the product of the component equations g_i with
exponents b₁ − d b₂ (+ d at s₀); when ξ_{s₀} has coefficients 0 in D₁ and 1 in D₂ the exponent at
s₀ vanishes. -/
theorem snc_local_equation_combination
    [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (c : EtaleChart K T (n + 1)) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (σ : Fin r → Option (Fin (n + 1)))
    (hc : IsSNCChart c ξ σ)
    (D₁ D₂ : CartierDivisor T)
    (h₁ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient D₁ (z : T) = 0)
    (h₂ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient D₂ (z : T) = 0)
    (t : T) (ht : t ∈ c.U) {lam₁ lam₂ : T.functionFieldˣ} (hlam₁ : D₁.IsLocalEquationAt t lam₁)
    (hlam₂ : D₂.IsLocalEquationAt t lam₂) (s₀ : Fin r) (d : ℕ) :
    ∃ v : (T.presheaf.stalk t)ˣ,
      ((lam₁ * (lam₂ ^ d)⁻¹ * sncChartComponentEquation c σ s₀ ^ d : T.functionFieldˣ) :
          T.functionField) =
        algebraMap (T.presheaf.stalk t) T.functionField v *
          ((∏ i, sncChartComponentEquation c σ i ^
            (cartierCoefficient D₁ (ξ i) - (d : ℤ) * cartierCoefficient D₂ (ξ i) +
              if i = s₀ then (d : ℤ) else 0) : T.functionFieldˣ) : T.functionField) := by
  classical
  obtain ⟨f₁, hf₁, u₁, hu₁⟩ := normal_isSNCChart_boundary_local_product hnorm D₁ c ξ hinj hξ σ hc
    h₁ t ht
  obtain ⟨f₂, hf₂, u₂, hu₂⟩ := normal_isSNCChart_boundary_local_product hnorm D₂ c ξ hinj hξ σ hc
    h₂ t ht
  obtain ⟨v₁, hv₁⟩ := hlam₁.exists_unit_mul_eq hf₁
  obtain ⟨v₂, hv₂⟩ := hlam₂.exists_unit_mul_eq hf₂
  let φs : (T.presheaf.stalk t)ˣ →* T.functionFieldˣ :=
    Units.map (algebraMap (T.presheaf.stalk t) T.functionField).toMonoidHom
  have hφs : ∀ x, ((φs x : T.functionFieldˣ) : T.functionField) =
      algebraMap (T.presheaf.stalk t) T.functionField x := fun x => rfl
  refine ⟨v₁ * u₁ * (v₂ * u₂)⁻¹ ^ d, ?_⟩
  -- the identities as units of the function field
  have e₁ : lam₁ = φs (v₁ * u₁) * ∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D₁ (ξ i) := by
    apply Units.ext
    rw [Units.val_mul, ← hv₁, hu₁, map_mul, Units.val_mul]
    rw [hφs, hφs]
    ring
  have e₂ : lam₂ = φs (v₂ * u₂) * ∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D₂ (ξ i) := by
    apply Units.ext
    rw [Units.val_mul, ← hv₂, hu₂, map_mul, Units.val_mul]
    rw [hφs, hφs]
    ring
  have hprod : (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D₁ (ξ i)) *
      ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D₂ (ξ i)) ^ d)⁻¹ *
        sncChartComponentEquation c σ s₀ ^ d =
      ∏ i, sncChartComponentEquation c σ i ^
        (cartierCoefficient D₁ (ξ i) - (d : ℤ) * cartierCoefficient D₂ (ξ i) +
          if i = s₀ then (d : ℤ) else 0) := by
    have hs : sncChartComponentEquation c σ s₀ ^ d =
        ∏ i, sncChartComponentEquation c σ i ^ (if i = s₀ then (d : ℤ) else 0) := by
      rw [Finset.prod_eq_single s₀]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ s₀) h
    rw [hs, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  have key : lam₁ * (lam₂ ^ d)⁻¹ * sncChartComponentEquation c σ s₀ ^ d =
      φs (v₁ * u₁ * (v₂ * u₂)⁻¹ ^ d) *
        ∏ i, sncChartComponentEquation c σ i ^
          (cartierCoefficient D₁ (ξ i) - (d : ℤ) * cartierCoefficient D₂ (ξ i) +
            if i = s₀ then (d : ℤ) else 0) := by
    rw [← hprod, e₁, e₂]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul,
      map_inv, map_pow]
    ring
  rw [key, Units.val_mul]
  rfl

end Combination

end MixedFujita
