/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionDivisor
public import MixedFujita.CartierSectionPowers

/-! 実摂動随伴を元正倍数・自然数nef余り・主因子に分解。 See reports/check-249-original-BPF-adjoint-all-multiples-stable-restriction.json for the verified scope. Original BPF positivity internally supplies all sufficiently large perturbed-adjoint nef-big conditions, with an explicit coarse natural degree bound. A fixed nonempty reduced W inside the complete base locus has usual-KV-based actual H1 vanishing and restriction surjectivity for every large original multiple. For a supplied stable nonempty power base and an actual initial seed, all high power restricted section spaces on W are zero. Initial and restricted-section nonvanishing, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

/-- A coarse NATURAL degree bound yields an exact actual Cartier decomposition:
positive original adjoint + nef natural tail + a concrete principal shift.
No real division or denominator rounding is needed. -/
theorem high_power_perturbed_adjoint_decomposition
    {X : Scheme.{u}} [IsIntegral X] (L D : CartierDivisor X)
    (d a₀ a q N m j : ℕ) (hq : 1 ≤ q) (hj : a₀ + a * m ≤ j)
    (t : Γ((N • (m • L)).sheaf, ⊤)) (ht : t ≠ 0) :
    ((q * N) * d) • (j • L) -
        ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • (m • L)) t ht) =
      (q * N) • ((d * a₀) • L - D) +
        (d * N * (q * (j - a₀) - a * m)) • L +
        principalCartierDivisor X ((cartierSectionUnit (N • (m • L)) t ht) ^ (d * a))⁻¹ := by
  have hja : a₀ ≤ j := by omega
  have hgap : a * m ≤ j - a₀ := by omega
  have hbudget : a * m ≤ q * (j - a₀) := by nlinarith
  have hJ : j = a₀ + (j - a₀) := (Nat.add_sub_of_le hja).symm
  have hQ : q * (j - a₀) = a * m + (q * (j - a₀) - a * m) :=
    (Nat.add_sub_of_le hbudget).symm
  have hnat : ((q * N) * d) * j = (q * N) * (d * a₀) + (d * a) * (N * m) +
      d * N * (q * (j - a₀) - a * m) := by
    calc
      ((q * N) * d) * j = d * N * (q * a₀ + q * (j - a₀)) := by
        conv_lhs => rw [hJ]
        ring
      _ = d * N * (q * a₀ + (a * m + (q * (j - a₀) - a * m))) := by conv_lhs => rw [hQ]
      _ = _ := by ring
  rw [principalCartierDivisor_inv, principalCartierDivisor_power, cartierSectionZeroDivisor]
  simp only [nsmul_add, nsmul_sub, smul_smul]
  rw [hnat, add_nsmul, add_nsmul]
  abel

end MixedFujita
