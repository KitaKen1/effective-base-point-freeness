/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialSGAFrameComparison
public import MixedFujita.InvertibleIdealCartier

/-! Regular ideal generators with the prescribed transition units construct
both the effective Cartier divisor and its negative-sheaf SGA representation.
This records precisely the local comparison required for Rees twisting bundles;
no Cartier representative or sheaf isomorphism is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsIntegral X] (L : X.LineBundle) [∀ i, Nonempty (L.U i)]
  (I : X.IdealSheafData) (hAffine : ∀ i, IsAffineOpen (L.U i))
  (a : ∀ i, Γ(X, L.U i)) (ha : ∀ i, a i ≠ 0)
  (hI : ∀ i, I.ideal ⟨L.U i, hAffine i⟩ = Ideal.span {a i})
  (hcompat : ∀ i j, X.presheaf.map (homOfLE inf_le_right).op (a j) =
    (L.g i j : Γ(X, L.U i ⊓ L.U j)) * X.presheaf.map (homOfLE inf_le_left).op (a i))

omit [IsIntegral X] [∀ i, Nonempty (L.U i)] in
include hcompat in
theorem regularGenerator_reverse_transition (i j : L.ι) :
    X.presheaf.map (homOfLE inf_le_left).op (a i) =
      (((L.g i j)⁻¹ : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) *
        X.presheaf.map (homOfLE inf_le_right).op (a j) := by
  rw [hcompat, ← mul_assoc, Units.inv_mul, one_mul]

include hAffine ha hI hcompat in
theorem exists_effectiveCartier_sga_of_generators :
    ∃ (E : CartierDivisor X) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = I ∧ Nonempty ((-E).sheaf ≅ L.toModules 1) := by
  obtain ⟨E, ⟨hEloc, hE⟩, -⟩ := cartier_existsUnique_effective_of_regularEquations X
    L.U L.iSup_eq_top a ha (fun i j => ⟨(L.g i j)⁻¹,
      regularGenerator_reverse_transition L a hcompat i j⟩)
  have hEq (i : L.ι) : rationalUnitClass X (L.U i)
      (Additive.ofMul (regularEquationRationalUnit X (L.U i) (a i) (ha i))) = E |_ L.U i :=
    (hEloc i).symm
  refine ⟨E, hE, ?_, ?_⟩
  · apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i => ⟨L.U i, hAffine i⟩) L.iSup_eq_top
    intro i
    rw [hI i]
    apply SetLike.coe_injective
    ext s
    rw [← effectiveCartierIdealSheaf_affine_image]
    exact (negativeCartierToUnit_range_iff X E hE (L.U i) s).trans
      (negativeCartier_regularSection_mem_iff X E (L.U i) (a i) (ha i) (hEq i) s)
  · let u (i : L.ι) := (regularEquationRationalUnit X (L.U i) (a i) (ha i))⁻¹
    have hu (i : L.ι) : rationalUnitClass X (L.U i) (Additive.ofMul (u i)) = (-E) |_ L.U i :=
      cartierNegative_regularEquation_restrict E (L.U i) (a i) (ha i) (hEq i)
    let e := fun i => cartierOpenFrameIso (-E) (L.U i) (u i) (hu i)
    refine ⟨moduleFramesCompatibleSGAIso L (-E).sheaf e ?_⟩
    intro i j
    apply cartierEquationFrameTransitionUnit_eq (-E) L.U u hu i j (L.g i j)
    let := integral_opens_inter_nonempty X (L.U i) (L.U j)
    have hw := regularEquationRationalUnit_eq_of_overlap X (a i) (ha i) (a j) (ha j)
      (L.g i j)⁻¹ (regularGenerator_reverse_transition L a hcompat i j)
    dsimp only [u]
    rw [hw]
    simp only [map_inv, mul_inv_rev, inv_inv, mul_comm]

end MixedFujita
