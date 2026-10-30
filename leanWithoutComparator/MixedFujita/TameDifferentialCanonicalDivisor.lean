/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
public import TauCeti.FieldTheory.FunctionField.Different.Tame

@[expose] public section

namespace MixedFujita

open TauCeti AlgebraicGeometry
open scoped IntermediateField

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem different_coeff_eq_ramificationIdx_sub_one_charZero
    {K F L : Type*} [Field K] [CharZero K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (hF : IsFunctionField K F) (P : Place K L) :
    (Divisor.different K L hF).coeff P = (Place.ramificationIdx F P : ℤ) - 1 := by
  have h := (Divisor.coeff_different_add_one_eq_ramificationIdx_iff hF P).mpr
    (P.isTame_of_charZero K F)
  omega

variable {K : Type u} [Field K] {F : Type v} [Field F]
  [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

noncomputable def ratFuncCotraceCanonicalDivisor (hF : IsFunctionField K F)
    (hk : IsIntegrallyClosedIn K F) : Divisor K F :=
  weilDifferentialDivisor hF hk
    (weilDifferentialCotrace K F (IsFunctionField.ratFunc K) hF
      ⟨ratFuncWeilDifferential K, ratFuncWeilDifferential_mem K⟩).2
    (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF)

theorem ratFuncCotraceCanonicalDivisor_coeff_charZero [CharZero K]
    (hF : IsFunctionField K F) (hk : IsIntegrallyClosedIn K F) (P : Place K F) :
    (ratFuncCotraceCanonicalDivisor hF hk).coeff P =
      (Place.ramificationIdx (RatFunc K) P : ℤ) - 1 -
        2 * max (-P.ord (algebraMap (RatFunc K) F RatFunc.X)) 0 := by
  rw [ratFuncCotraceCanonicalDivisor,
    weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential,
    WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, Divisor.coeff_poles,
    different_coeff_eq_ramificationIdx_sub_one_charZero]
  simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_ofClass]
  ring

theorem ratFuncCotraceCanonicalDivisor_coeff_at_infty [CharZero K]
    (hF : IsFunctionField K F) (hk : IsIntegrallyClosedIn K F) (P : Place K F)
    (hP : P.restrict K (RatFunc K) = Place.infty K) :
    P.ord (algebraMap (RatFunc K) F RatFunc.X) = -(Place.ramificationIdx (RatFunc K) P : ℤ) ∧
      (ratFuncCotraceCanonicalDivisor hF hk).coeff P =
        -(Place.ramificationIdx (RatFunc K) P : ℤ) - 1 := by
  have hord : P.ord (algebraMap (RatFunc K) F RatFunc.X) =
      -(Place.ramificationIdx (RatFunc K) P : ℤ) := by
    rw [Place.ord_algebraMap_restrict K (RatFunc K), hP, Place.ord_infty]
    simp
  refine ⟨hord, ?_⟩
  rw [ratFuncCotraceCanonicalDivisor_coeff_charZero, hord, neg_neg,
    max_eq_left (Int.natCast_nonneg _)]
  ring

theorem ratFuncCotraceCanonicalDivisor_coeff_at_finite [CharZero K]
    (hF : IsFunctionField K F) (hk : IsIntegrallyClosedIn K F) (P : Place K F) (a : K)
    (hP : P.restrict K (RatFunc K) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a)) :
    P.ord (algebraMap (RatFunc K) F (RatFunc.X - algebraMap K (RatFunc K) a)) =
        (Place.ramificationIdx (RatFunc K) P : ℤ) ∧
      (ratFuncCotraceCanonicalDivisor hF hk).coeff P =
        (Place.ramificationIdx (RatFunc K) P : ℤ) - 1 := by
  have hord : (Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a)).ord
      (RatFunc.X - algebraMap K (RatFunc K) a) = 1 := by
    rw [show (RatFunc.X - algebraMap K (RatFunc K) a : RatFunc K) =
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a) by simp,
      Place.ord_adicOfIrreducible_algebraMap_irreducible
        (Polynomial.irreducible_X_sub_C a) (Polynomial.irreducible_X_sub_C a)]
    simp
  have hnonneg : 0 ≤ P.ord (algebraMap (RatFunc K) F RatFunc.X) := by
    rw [Place.ord_algebraMap_restrict K (RatFunc K), hP, Place.ord_adicOfIrreducible_X]
    split_ifs <;> positivity
  refine ⟨?_, ?_⟩
  · rw [Place.ord_algebraMap_restrict K (RatFunc K), hP, hord, mul_one]
  · rw [ratFuncCotraceCanonicalDivisor_coeff_charZero,
      max_eq_right (neg_nonpos.mpr hnonneg), mul_zero, sub_zero]

/-- The explicitly constructed cotrace divisor represents the intrinsic canonical class. -/
theorem ratFuncCotraceCanonicalDivisor_class
    (hF : IsFunctionField K F) (hk : IsIntegrallyClosedIn K F) :
    (Place.orderSystem hF).divisorClass (ratFuncCotraceCanonicalDivisor hF hk) =
      canonicalClass hF hk := by
  exact divisorClass_weilDifferentialDivisor hF hk _ _

end MixedFujita
