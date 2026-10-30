/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCTransverseEquationChart
public import MixedFujita.SNCEffectiveCartierTransverseChart

/-!
An actual effective Cartier cut has the new etale coordinate itself as its
local Cartier equation, not only its support as a coordinate zero set.
This retains the multiplicity needed for the coefficient-one lc bound.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [PerfectField K] {n r : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- An effective Cartier cut supplies its own regular equation and an actual adapted joint SNC chart. -/
theorem exists_sncChartWith_localEquation_effectiveCartier_of_transverse_stalk
    (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) (H : CartierDivisor X) (hH : H.IsEffective)
    (x : X) (hxH : x ∈ (effectiveCartierIdealSheaf H hH).support)
    (a : X.presheaf.stalk x)
    (hHa : (effectiveCartierIdealSheaf H hH).stalkIdeal x = Ideal.span {a})
    (htrans : a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      (sncActiveStratumIdeal (sncDivisorFamilyOfPoints ξ) x).stalkIdeal x) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (j : Fin n),
      x ∈ c.U ∧ IsSNCChartWith c ξ σ ((effectiveCartierIdealSheaf H hH).support : Set X) (some j) ∧
        H.IsLocalEquationAt x (etaleChartCoordinateRationalUnit c j) := by
  classical
  obtain ⟨c₀, σ, hx₀, hc₀⟩ := hξ x
  obtain ⟨U, hxU, hne, b₀, hb₀, hEq₀⟩ := exists_affineOpen_regularEquation_of_isEffective H hH x
  obtain ⟨h, hle, hxh⟩ := c₀.isAffine.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx₀
  let c := etaleChartBasicOpen c₀ h ⟨⟨x, hxh⟩⟩
  have hxc : x ∈ c.U := hxh
  have hc : IsSNCChart c ξ σ := isSNCChart_basicOpen hc₀ h _
  have hcle : c.U ≤ U.1 := hle
  letI : Nonempty c.U := ⟨⟨x, hxc⟩⟩
  let b : Γ(X, c.U) := X.presheaf.map (homOfLE hcle).op b₀
  obtain ⟨hb, hEq⟩ := regularEquation_restrict H hcle b₀ hb₀ hEq₀
  have hI := effectiveCartierIdealSheaf_ideal_eq_span H hH ⟨c.U, c.isAffine⟩ b hb hEq
  have hIb : (effectiveCartierIdealSheaf H hH).stalkIdeal x =
      Ideal.span {X.presheaf.germ c.U x hxc b} := by
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ ⟨c.U, c.isAffine⟩ hxc,
      hI, Ideal.map_span, Set.image_singleton]
  have hbm : X.presheaf.germ c.U x hxc b ∈ maximalIdeal (X.presheaf.stalk x) := by
    apply (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp hxH
    rw [hIb]
    exact Ideal.mem_span_singleton_self _
  have hbt := notMem_ideal_of_span_singleton_eq
    (maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      (sncActiveStratumIdeal (sncDivisorFamilyOfPoints ξ) x).stalkIdeal x)
    a (X.presheaf.germ c.U x hxc b) (hHa.symm.trans hIb) htrans
  have hZb : ∀ z ∈ c.U, z ∈ ((effectiveCartierIdealSheaf H hH).support : Set X) ↔
      z ∉ X.basicOpen b := by
    have hs := (effectiveCartierIdealSheaf H hH).coe_support_inter ⟨c.U, c.isAffine⟩
    rw [hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at hs
    intro z hz
    constructor
    · intro hzH
      have hm : z ∈ ((effectiveCartierIdealSheaf H hH).support : Set X) ∩ c.U := ⟨hzH, hz⟩
      rw [hs] at hm
      exact hm.1
    · intro hzb
      have hm : z ∈ ((X.basicOpen b : Set X)ᶜ ∩ c.U) := ⟨hzb, hz⟩
      rw [← hs] at hm
      exact hm.1
  obtain ⟨c', σ', j, hx', hc', hgeq⟩ := exists_sncChartWith_equation_of_active_stratum_transverse_germ
    c ξ σ hc ((effectiveCartierIdealSheaf H hH).support : Set X) b x hxc hbm hbt hZb
  refine ⟨c', σ', j, hx', hc', ?_⟩
  have heq : etaleChartCoordinateRationalUnit c' j = regularEquationRationalUnit X c.U b hb :=
    Units.ext hgeq
  rw [heq]
  exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxc

/-- Actual base-prime Cartier pullbacks have joint etale SNC charts without any supplied source equation. -/
theorem exists_sncChartWith_localEquation_cartierPullback_of_base_uniformizer
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : X ⟶ Y) [IsDominant q] (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ)
    (V : Y.Opens) (htrans : SNCStrataUniformizerTransverseOn q (sncDivisorFamilyOfPoints ξ) V)
    (x : X) (hxV : q x ∈ V) (hcoh : Order.coheight (q x) = 1)
    (H : CartierDivisor Y) (hH : H.IsEffective) (fH : Y.functionFieldˣ)
    (hfH : H.IsLocalEquationAt (q x) fH) (a : Y.presheaf.stalk (q x))
    (ha : algebraMap (Y.presheaf.stalk (q x)) Y.functionField a = (fH : Y.functionField))
    (hairred : Irreducible a) :
    let hG := cartierPullback_effective_of_effective q H hH
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (j : Fin n),
      x ∈ c.U ∧ IsSNCChartWith c ξ σ
        ((effectiveCartierIdealSheaf (cartierPullback q H) hG).support : Set X) (some j) ∧
          (cartierPullback q H).IsLocalEquationAt x (etaleChartCoordinateRationalUnit c j) := by
  classical
  let G := cartierPullback q H
  let hG := cartierPullback_effective_of_effective q H hH
  let fG := Units.map (dominantFunctionFieldMap q).hom.toMonoidHom fH
  have hgf : G.IsLocalEquationAt x fG := cartierPullback_isLocalEquationAt q H x hfH
  have hmap : algebraMap (X.presheaf.stalk x) X.functionField ((q.stalkMap x).hom a) =
      (fG : X.functionField) := by
    rw [← dominantFunctionFieldMap_algebraMap q x a, ha]
    rfl
  have hI := effectiveCartier_stalkIdeal_eq_span_of_localEquation G hG x fG hgf
    ((q.stalkMap x).hom a) hmap
  have ham : a ∈ maximalIdeal (Y.presheaf.stalk (q x)) := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff] using hairred.not_isUnit
  have hmapm := map_nonunit (q.stalkMap x).hom a ham
  have hxG : x ∈ (effectiveCartierIdealSheaf G hG).support := by
    apply (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mpr
    rw [hI]
    exact Ideal.span_le.mpr (by rintro b rfl; exact hmapm)
  apply exists_sncChartWith_localEquation_effectiveCartier_of_transverse_stalk ξ hξ G hG x hxG
    ((q.stalkMap x).hom a) hI
  apply sncStratum_uniformizer_transverse_at_mem_support q (sncDivisorFamilyOfPoints ξ) V htrans
    (Finset.univ.filter fun i => x ∈ ((sncDivisorFamilyOfPoints ξ).component i).support) x
    (sncActiveStratumIdeal_mem_support (sncDivisorFamilyOfPoints ξ) x) hxV hcoh a hairred

end MixedFujita
