/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NaturalGeneratorUnitReflection
public import MixedFujita.AmpleIdealExteriorGeneration

/-! 全高次ample有限切断族の共通零点集合=実中心台。 See reports/check-261-exact-center-base-canonical-pullback.json for the verified scope. Tracking GLOBAL1 proves exact compatibility of canonical section homs and NATURAL global pullback. Mathlib biproduct formulas identify exterior finite-free pullback with canonical generation by the SAME naturally pulled family. Actual stalk maps reflect unit coefficients without target integrality. ALL high original ample powers have an actual ambient finite family naturally zero on the actual closed center with common ZERO SET exactly its support and a unit coefficient at every point off support. Adding the fixed concentrated lift gives restriction vector (fixed,0,...,0) and exact common zero set. Multiplying a nonzero parameter polynomial by X_0 ensures first coefficient nonzero over an infinite field. Actual SNC exterior-LC Bertini geometry, linear-combination scalar/concentration preservation, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- ALL high original ample powers have a finite actual ambient Cartier
family whose common zero locus is EXACTLY the actual closed center support,
with all NATURAL restrictions zero and a unit generator at EVERY point outside.
No ideal invertibility, reducedness/integrality/normality of the center,
basepointfree certificate or KV is supplied. -/
theorem ample_ideal_finite_sections_common_zero_locus_exact_support
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (I : X.IdealSheafData) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (k : ℕ) (s : Fin k → Γ((b • A).sheaf, ⊤)),
      (∀ i, modulePullbackGlobalSections I.subschemeι (b • A).sheaf (s i) = 0) ∧
      (∀ x : X, x ∉ I.support → ∃ i, IsUnit (cartierLocalCoefficient (b • A) x
        (Classical.choose ((b • A).exists_isLocalEquationAt x))
        (Classical.choose_spec ((b • A).exists_isLocalEquationAt x)) (s i))) ∧
      ∀ x : X, (∀ i, x ∈ cartierSectionZeroLocus (b • A) (s i)) ↔ x ∈ I.support := by
  classical
  let U : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨b₀, hb₀⟩ := ample_ideal_sections_natural_zero_and_complement_finite_free_epi A hA I
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨k, s, hzero, hepi⟩ := hb₀ b hb
  have hpull : Epi (biproduct.desc (fun i => CohomologyAux.homOfSection
      ((Scheme.Modules.pullback U.ι).obj (b • A).sheaf)
      (modulePullbackGlobalSections U.ι (b • A).sheaf (s i)))) := by
    rw [← modulePullbackUnitBiproductIso_inv_map_global_generator_desc]
    exact hepi
  let := hpull
  have hunit (x : X) (hx : x ∉ I.support) : ∃ i, IsUnit (cartierLocalCoefficient (b • A) x
      (Classical.choose ((b • A).exists_isLocalEquationAt x))
      (Classical.choose_spec ((b • A).exists_isLocalEquationAt x)) (s i)) :=
    natural_pulled_Cartier_generators_unit_at_image U.ι (b • A) k s ⟨x, hx⟩
  refine ⟨k, s, hzero, hunit, fun x => ⟨?_, ?_⟩⟩
  · intro hall
    by_contra hx
    obtain ⟨i, hi⟩ := hunit x hx
    exact hall i ((mem_cartierSectionNonvanishingOpen_iff_localCoefficient (b • A) (s i) x _
      (Classical.choose_spec ((b • A).exists_isLocalEquationAt x))).mpr hi)
  · intro hx i
    have hx' : x ∈ (I.support : Set X) := hx
    rw [← I.range_subschemeι] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact Cartier_natural_pullback_zero_image_mem_zero_locus I.subschemeι (b • A) (s i) (hzero i) y

end MixedFujita
