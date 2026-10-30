/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSmoothCurvePointDivisor
public import MixedFujita.ProperCurveSerreVanishing
public import MixedFujita.NormalCartierSectionLifting
public import MixedFujita.KltIsolationGeneration
public import MixedFujita.ThresholdModelLifting

/-! 固有smooth曲線のdeg D≥2gから実大域生成。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_globallyGenerated_of_degree_ge_two_genus
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : 2 * (Module.finrank K (Scheme.Modules.Cohomology
        (0 : CartierDivisor X).sheaf 1) : ℤ) ≤
      properCurveCartierDegree (K := K) hX D) : CartierIsGloballyGenerated D := by
  classical
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  have hnorm (z : X) : IsIntegrallyClosed (X.presheaf.stalk z) :=
    smooth_stalk_isIntegrallyClosed (K := K) z
  apply cartierIsGloballyGenerated_of_forall_isClosed
  intro x hx
  obtain ⟨E, hE, hdeg, hcoef⟩ :=
    properSmoothCurve_exists_degree_one_point_divisor (K := K) hX x hx
  have hx1 : coheight x = 1 := by
    have h := geometricSmoothScheme_closedPoint_stalk_dimension (K := K) 1 hX x hx
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  let ξ : CodimensionOnePoint X := ⟨x, hx1⟩
  have hvan : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf 1) := by
    apply properSmoothCurve_cohomology_subsingleton_of_degree_gt_two_genus_sub_two_isAlgClosed
      (K := K) hX (D - E) (q := 0)
    change 2 * (Module.finrank K (Scheme.Modules.Cohomology
      (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 <
      CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) (D - E)
    rw [map_sub]
    change 2 * (Module.finrank K (Scheme.Modules.Cohomology
      (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 <
      properCurveCartierDegree (K := K) hX D - properCurveCartierDegree (K := K) hX E
    omega
  obtain ⟨g, f, u, hg, hf, hu⟩ := exists_section_generating_of_lifting hnorm hnorm (𝟙 X)
    (dominantFunctionFieldMap_id_bijective (X := X)) D 0 E hE
    (by simpa only [cartierPullback_id, add_zero] using hvan)
    ({x} : Set X) hx
    (by intro z hz; rw [hcoef, ite_eq_right (by simpa using hz)])
    ⊤ (fun _ _ => trivial)
    (by intro z _; simp only [cartierCoefficient_zero]; rfl)
    (by intro z _; simp only [cartierCoefficient_zero]; rfl)
    ξ rfl (by rw [hcoef]; simp only [ξ, ↓reduceIte, le_refl])
    (by simp only [cartierCoefficient_zero]) (by intro z hz; simpa using hz)
  refine ⟨f, hf, CartierDivisor.sectionMk _ hg, ?_⟩
  exact isUnit_cartierLocalCoefficient_sectionMk D x g hg f hf u hu

end MixedFujita
