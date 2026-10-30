/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.HighPowerPerturbedAdjointDecomposition
public import MixedFujita.ProperNormalBigAddNef
public import MixedFujita.ProperCartierCohomology
public import MixedFujita.CartierBigOperations
public import MixedFujita.CartierNefDefinition

/-! 元BPF仮定から全大倍数の摂動随伴nef-bigを内部供給。 See reports/check-249-original-BPF-adjoint-all-multiples-stable-restriction.json for the verified scope. Original BPF positivity internally supplies all sufficiently large perturbed-adjoint nef-big conditions, with an explicit coarse natural degree bound. A fixed nonempty reduced W inside the complete base locus has usual-KV-based actual H1 vanishing and restriction surjectivity for every large original multiple. For a supplied stable nonempty power base and an actual initial seed, all high power restricted section spaces on W are zero. Initial and restricted-section nonvanishing, usual KV, klt BPF and full F1/F2 remain unproved. -/

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
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra





/-- ORIGINAL BPF positivity supplies BOTH perturbed-adjoint nefness and bigness
for every degree above the explicit coarse bound. Proper cohomology internally
supplies finiteness for big multiples; no positivity or H0 finiteness input is added. -/
theorem original_bpf_perturbed_adjoint_nef_big_of_degree_bound
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (L D : CartierDivisor X) (hL : CartierIsNef K L)
    (d a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D))
    (a q N m j : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hj : a₀ + a * m ≤ j)
    (t : Γ((N • (m • L)).sheaf, ⊤)) (ht : t ≠ 0) :
    CartierIsNef K (((q * N) * d) • (j • L) -
      ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)) ∧
    CartierIsBig K (((q * N) * d) • (j • L) -
      ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)) := by
  rw [high_power_perturbed_adjoint_decomposition L D d a₀ a q N m j hq hj t ht]
  have hqn : 1 ≤ q * N := Nat.mul_pos (by omega) (by omega)
  have htail := cartierIsNef_nsmul hL (d * N * (q * (j - a₀) - a * m))
  have hfin (k : ℕ) : FiniteDimensional K Γ((k • ((d * a₀) • L - D)).sheaf, ⊤) :=
    proper_cartier_sections_finite K _
  have hmulti := cartierIsBig_nsmul hbig (q * N) hqn hfin
  constructor
  · exact (cartierIsNef_add_principal_iff _).mpr
      (cartierIsNef_add (cartierIsNef_nsmul hnef (q * N)) htail)
  · exact cartierIsBig_add_principal
      (proper_normal_cartierIsBig_add_of_isNef K n hdim hn hnorm _ _ hmulti htail) _

end MixedFujita
