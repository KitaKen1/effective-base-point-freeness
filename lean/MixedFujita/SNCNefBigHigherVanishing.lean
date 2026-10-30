/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCPrincipalizationAmplePerturbation
public import Hironaka.Scheme.BlowUpSequence.NowhereDenseSupport

/-! Nef-and-big higher vanishing on a smooth projective SNC model, for a
finite Cartier presentation of the boundary. Kodaira's lemma, actual BMO₁
principalization, supported ample correction and all-degree descent supply
all geometric and cohomological inputs. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Signed finite-SNC roundup has vanishing in every positive degree when
its adjoint is nef and big on a positive-dimensional smooth projective scheme.
No ample perturbation, admissible resolution or cohomology vanishing is assumed. -/
theorem snc_projective_nef_big_roundup_higher_vanishing
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.Over (Spec (.of k))]
    (n : ℕ) (hn : 1 ≤ n) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (cX : EtaleChart k X n)
    (D : DivisorFamily X) (hD : D.IsSnc)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i)
    (b : D.ι → ℤ) (d : ℕ) (hd : 1 ≤ d) (Q H : CartierDivisor X)
    (hH : CartierIsAmpleProj k H)
    (hnef : CartierIsNef k (d • (Q - smoothCanonicalDivisor cX) - ∑ i, b i • P i))
    (hbig : CartierIsBig k (d • (Q - smoothCanonicalDivisor cX) - ∑ i, b i • P i))
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology
      (Q + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).sheaf q) := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := k) x
  let B := ∑ i, b i • P i
  let N := d • (Q - smoothCanonicalDivisor cX) - B
  obtain ⟨j, hj, u, hu⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj
    (etaleChart_topologicalKrullDim cX) hn hnorm cX N H hbig hH
  let F := cartierSectionZeroDivisor (j • N - H) u hu
  have hF : F.IsEffective := cartierSectionZeroDivisor_isEffective _ _ _
  let I := effectiveCartierIdealSheaf F hF
  have hI : IsNonzeroEverywhere I := isNonzeroEverywhere_of_isNowhereDense_support I
    (isNowhereDense_of_isClosed_of_genericPoint_notMem I.support.isClosed
      (genericPoint_notMem_support_effectiveCartierIdealSheaf F hF))
  let T : AlgebraicGeometry.Triple k :=
    ⟨AlgScheme.of (k := k) X, ⟨n, by
      change SmoothOfRelativeDimension n (X ↘ Spec (.of k))
      infer_instance⟩, I, hI, D, hD⟩
  let hTs : SmoothOfRelativeDimension n T.X.hom := by
    change SmoothOfRelativeDimension n (X ↘ Spec (.of k))
    infer_instance
  let hTp : IsProper T.X.hom := by
    change IsProper (X ↘ Spec (.of k))
    infer_instance
  let : T.X.left.Over (Spec (.of k)) := AlgScheme.over T.X
  let : SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k)) := hTs
  let : IsProper (T.X.left ↘ Spec (.of k)) := hTp
  let S := sncMarkedPrincipalizationSequence T
  obtain ⟨_, _, hY, hYo, hYN, hYs, hdom, hover, hπ, cY, D', P', hP', b',
      _, _, hB, _, hround, ⟨r, ξ, hinj, hξ, hsnc, hatlas, hctrl⟩, hcoho⟩ :=
    @snc_principalization_exists_supported_cohomology_descent k _ _ T
      (inferInstanceAs (IsIntegral X)) n hTs P hP hPI b d hd cX
  let : IsIntegral S.last := hY
  let : S.last.Over (Spec (.of k)) := hYo
  let : IsNoetherian S.last := hYN
  let : SmoothOfRelativeDimension n (S.last ↘ Spec (.of k)) := hYs
  let : IsDominant S.composite := hdom
  let : S.composite.IsOver (Spec (.of k)) := hover
  let : IsProper S.composite := S.isProper_composite
  let : IsProper (S.last ↘ Spec (.of k)) := by
    rw [← HomIsOver.comp_over (f := S.composite)]
    infer_instance
  let C := ∑ i, b' i • P' i
  let E := ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i
  let w := (isUnit_chartRelativeJacobianDet_of_bijective S.composite hπ cX cY).unit
  let Q₀ := cartierPullback S.composite Q - principalCartierDivisor S.last w
  have hC : C = cartierPullback S.composite B - (d : ℤ) •
      birationalRelativeCanonicalDivisor n S.composite hπ
        cX etaleCharts_cover cY etaleCharts_cover := hB
  have hE : ∀ t : CodimensionOnePoint S.last, cartierCoefficient E t =
      ⌈-((cartierCoefficient C t : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hC]
    exact hround t
  have hadj : d • (Q₀ - smoothCanonicalDivisor cY) - C =
      cartierPullback S.composite N := by
    rw [hC]
    dsimp only [N, Q₀, w]
    rw [cartierPullback_sub, cartierPullback_nsmul, cartierPullback_sub]
    unfold birationalRelativeCanonicalDivisor relativeCanonicalDivisor smoothCanonicalDivisor
    module
  obtain ⟨c, G, hc, hG, hG0, hampG⟩ :=
    snc_principalization_exists_supported_ample_correction T H hH
  let J := c • cartierPullback S.composite F + G
  have hJ : J.IsEffective :=
    (cartier_nsmul_isEffective _ (cartierPullback_isEffective S.composite F hF) c).add hG
  have hCsupp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
      cartierCoefficient C t = 0 := fun t ht => (hctrl t ht).1
  have hJsupp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
      cartierCoefficient J t = 0 := by
    intro t ht
    have hF0 : cartierCoefficient (cartierPullback S.composite F) t = 0 := by
      apply cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf _
        (cartierPullback_isEffective S.composite F hF)
      rw [effectiveCartierIdealSheaf_cartierPullback S.composite F hF]
      exact fun hi => (hctrl t ht).2.1 ((mem_support_comap_iff_apply I S.composite t).mp hi)
    have hGzero := hG0 t (fun h => ht ((hatlas t).mpr h))
    dsimp only [J]
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, hF0, hGzero, mul_zero, add_zero]
  obtain ⟨s₀, hs₀, hvan⟩ := snc_effective_perturbation_roundup_higher_vanishing k n cY ξ
    hinj hξ hsnc C E Q₀ J d hd hJ hCsupp hJsupp hE
  let s := j * c * s₀
  have hjc : 1 ≤ j * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hs : s₀ ≤ s := by dsimp only [s]; nlinarith
  have hseq : s = j * c * (s₀ - 1) + j * c := by
    dsimp only [s]
    have he : s₀ - 1 + 1 = s₀ := by omega
    nlinarith
  let v := (Units.map (dominantFunctionFieldMap S.composite).hom.toMonoidHom
    (cartierSectionUnit (j • N - H) u hu) ^ c)⁻¹
  have hpF : cartierPullback S.composite F = j • cartierPullback S.composite N -
      cartierPullback S.composite H + principalCartierDivisor S.last
        (Units.map (dominantFunctionFieldMap S.composite).hom.toMonoidHom
          (cartierSectionUnit (j • N - H) u hu)) := by
    dsimp only [F, cartierSectionZeroDivisor]
    rw [cartierPullback_add, cartierPullback_sub, cartierPullback_nsmul,
      cartierPullback_principal]
  have hid : (d * s) • (Q₀ - smoothCanonicalDivisor cY) - (s • C + J) =
      (j * c * (s₀ - 1)) • cartierPullback S.composite N +
        (cartierPullback S.composite (c • H) - G) + principalCartierDivisor S.last v := by
    calc
      _ = s • (d • (Q₀ - smoothCanonicalDivisor cY) - C) - J := by module
      _ = s • cartierPullback S.composite N - J := by rw [hadj]
      _ = _ := ?_
    dsimp only [J, v]
    rw [hpF, principalCartierDivisor_inv, principalCartierDivisor_power,
      cartierPullback_nsmul, hseq]
    module
  have hamp : CartierIsAmpleProj k
      ((d * s) • (Q₀ - smoothCanonicalDivisor cY) - (s • C + J)) := by
    rw [hid]
    apply cartierIsAmpleProj_add_principalCartierDivisor
    exact proper_nef_add_ample_isAmpleProj k _ _
      (cartierIsNef_nsmul (cartierIsNef_cartierPullback_of_dominant S.composite hnef) _) hampG
  let : Subsingleton (Scheme.Modules.Cohomology (Q₀ + E).sheaf q) := (hvan s hs).2 hamp q hq
  have he : (Q₀ + E) + principalCartierDivisor S.last w = cartierPullback S.composite Q + E := by
    dsimp only [Q₀]
    abel
  let e : (Q₀ + E).sheaf ≅ (cartierPullback S.composite Q + E).sheaf :=
    (cartierSheafPrincipalShiftIso (Q₀ + E) w).symm ≪≫ eqToIso (congrArg CartierDivisor.sheaf he)
  have hsource : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback S.composite Q + E).sheaf q) :=
    (actualCohomologyLinearEquivOfIso e q).symm.subsingleton
  exact ((hcoho Q).2.2.2 q).2.mp hsource

end MixedFujita
