/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FixedPartOriginalZeroDivisorIdentity
public import MixedFujita.BoundaryAvoidingFirstBertiniParameter
public import MixedFujita.PrincipalizedExteriorLCCoefficients
public import MixedFujita.PrincipalizedOriginalFiniteSystem
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.CartierSectionBaseIdeal
public import SGA.Foundations.Cohomology.Devissage

/-! 実SNC主化を内部化する元有限族の中心外lc摂動。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The ORIGINAL finite subsystem of an lc pair has a SAME-coefficient
combination with first coefficient nonzero and lc perturbation outside any
closed set containing its actual base. The proper SNC principalizing model,
corresponding residual system and boundary-avoiding Bertini cut are internal.
No original klt hypothesis, normality or vanishing theorem is assumed. -/
theorem exists_original_finite_combination_lc_outside_base
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    (P : CartierDivisor X) (k : ℕ) (s : Fin (k + 1) → Γ(P.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (Z : Closeds X) (hbase : ((cartierSectionBaseIdeal P s hs).support : Set X) ⊆ Z)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ a : Fin (k + 1) → K, a 0 ≠ 0 ∧
      ∃ ht : (∑ i, a i • s i) ≠ 0,
        ∀ x : X, x ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d)
          (j • D + cartierSectionZeroDivisor P (∑ i, a i • s i) ht) := by
  classical
  let A (i : Fin (k + 1)) := cartierSectionZeroDivisor P (s i) (hs i)
  have hA (i : Fin (k + 1)) : (A i).IsEffective := cartierSectionZeroDivisor_isEffective P (s i) (hs i)
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, _, hρ, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, _, _, _, _, _, F, hF, hFI, hFsupp, _, _⟩ :=
    exists_projective_snc_model_principalizing_sum c f d D
      (fun i : PEmpty.{1} => i.elim) A hA (fun i : PEmpty.{1} => i.elim) (fun i => i.elim)
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  have : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨t, ht, hinc, _, _, hfree⟩ :=
    principalized_original_finite_system_exists_residual_basePointFree ρ P s hs F hF hFI
  obtain ⟨a, ha0, hat, q, η, hηinj, hη, hsnc', hdis, hcoeff⟩ :=
    residual_first_nonzero_boundary_compatible_snc_parameter (cartierPullback ρ P - F) k t hfree ξ hsnc
  let u := ∑ i, a i • s i
  let v := ∑ i, a i • t i
  let ι := cartierEffectiveInclusion (cartierPullback ρ P) F hF
  have hi : Scheme.Modules.Hom.app ι ⊤ v = cartierDominantPullbackSection ρ P u :=
    residual_original_linear_combination_inclusion ρ P s F hF t hinc a
  let : Mono ι := cartierEffectiveInclusion_mono (cartierPullback ρ P) F hF
  have hv : Scheme.Modules.Hom.app ι ⊤ v ≠ 0 :=
    (map_ne_zero_iff _ (CohomologyAux.app_injective_of_mono ι ⊤)).mpr hat
  have hu : u ≠ 0 := by
    intro hz
    apply hv
    rw [hi, hz]
    exact (cartierDominantPullbackLinear ρ K P).map_zero
  have hzero : cartierPullback ρ (cartierSectionZeroDivisor P u hu) =
      F + cartierSectionZeroDivisor (cartierPullback ρ P - F) v hat := by
    rw [← cartierDominantPullbackSection_zeroDivisor ρ P u hu]
    exact cartier_fixed_part_inclusion_zeroDivisor (cartierPullback ρ P) F hF v hat _
      (cartierDominantPullbackSection_ne_zero ρ P u hu) hi
  refine ⟨a, ha0, hu, ?_⟩
  exact logCanonical_exterior_of_principalized_reduced_snc_cut ρ hρ c f d hd D hlc cT ξ η
    hinj hηinj hξ hη hsnc' hdis hsupp (cartierSectionBaseIdeal P s hs) F hF hFI hFsupp
    (cartierSectionZeroDivisor P u hu) _ hzero hcoeff Z hbase j hj

end MixedFujita
