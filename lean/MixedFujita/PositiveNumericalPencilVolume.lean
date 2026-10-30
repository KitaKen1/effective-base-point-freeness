/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefMixedEulerMonotonicity
public import MixedFujita.CartierNumericalDimension

/-! 正の元数値次元からnef-ample pencil体積の線形増大。 See reports/check-252-positive-numerical-concentration-ample-independence.json for the verified scope. Finite Taylor boxes and actual ample Hilbert limits construct actual high-order effective concentration divisors at every closed point in all high powers. Positive original mixed-intersection numerical dimension gives the explicit ample pencil parameter. Original nef numerical dimension is ample-independent without semiampleness. Smooth original klt BPF data construct normalized high-order cuts without an initial L section or KV. Initial and restricted nonvanishing, singular-source local smooth-point extension, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- Positive ORIGINAL mixed-intersection numerical dimension gives a linear
lower bound for every ample-pencil diagonal. No Iitaka equality or section
nonvanishing for L is supplied. -/
theorem positive_numerical_dimension_nef_pencil_diagonal_ge_parameter
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L H) (l : ℕ) (hl : 1 ≤ l) :
    (l : ℤ) ≤ cartierMixedEulerDifference K (List.replicate n (l • L + H)) 0 := by
  let k := cartierNumericalDimension K n hdim L H
  have hk : k ≤ n := cartierNumericalDimension_le_dim K n hdim L H
  have hkpos : 1 ≤ k := hν
  obtain ⟨hklt, hpositive⟩ := (cartierNumericalDimension_isGreatest K n hdim hn L H hH).1
  change 0 < cartierMixedEulerDifference K
    (List.replicate k L ++ List.replicate (n - k) H) 0 at hpositive
  have hC : 1 ≤ cartierMixedEulerDifference K
      (List.replicate k L ++ List.replicate (n - k) H) 0 := by omega
  have hlpow : l ≤ l ^ k := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    rw [hs, pow_succ]
    have hpow : 1 ≤ l ^ s := one_le_pow₀ hl
    nlinarith
  have hlpowZ : (l : ℤ) ≤ (l : ℤ) ^ k := by exact_mod_cast hlpow
  have hselected := proper_nef_diagonal_ge_scaled_selected_mixed_power K n hdim hn L H hL hH k hk l 0
  exact hlpowZ.trans ((le_mul_of_one_le_right (pow_nonneg (Int.natCast_nonneg l) k) hC).trans hselected)

end MixedFujita
