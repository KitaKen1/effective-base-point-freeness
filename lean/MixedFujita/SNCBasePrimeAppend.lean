/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryTransverseAppend
public import MixedFujita.SNCStrataUniformizerTransversality
public import MixedFujita.SectionBaseStalkMembership
public import MixedFujita.NormalEffectiveCartierPrime

/-!
At an actual point over a base prime in the constructed transverse open, append
the actual pulled-back uniformizer cut to the existing SNC boundary. For an
effective Cartier base divisor with an irreducible regular local equation,
construct the actual pullback ideal and its generator internally. No source
ideal-generator comparison or appended-SNC certificate is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The point belongs to the actual intersection of every boundary component passing through it. -/
theorem sncActiveStratumIdeal_mem_support {X : Scheme.{u}} (E : Scheme.DivisorFamily X) (x : X) :
    x ∈ (sncActiveStratumIdeal E x).support := by
  classical
  rw [sncActiveStratumIdeal, sncStratumIdeal, Scheme.IdealSheafData.support_iSup]
  change x ∈ (⨅ i, (⨆ (_ : i ∈ Finset.univ.filter fun i => x ∈ (E.component i).support),
    E.component i).support : Closeds X)
  simp only [Scheme.IdealSheafData.support_iSup, Closeds.mem_iInf]
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- The proved all-stratum transversality applies at each actual ambient point of a closed stratum. -/
theorem sncStratum_uniformizer_transverse_at_mem_support
    {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Scheme.DivisorFamily X) (V : Y.Opens)
    (htrans : SNCStrataUniformizerTransverseOn g E V) (s : Finset E.ι)
    (x : X) (hx : x ∈ (sncStratumIdeal E s).support) (hxV : g x ∈ V)
    (hcoh : Order.coheight (g x) = 1)
    (a : Y.presheaf.stalk (g x)) (ha : Irreducible a) :
    (g.stalkMap x).hom a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ (sncStratumIdeal E s).stalkIdeal x := by
  obtain ⟨w, rfl⟩ := (sncStratumIdeal E s).exists_subschemeι_eq hx
  exact htrans s w hxV hcoh a ha

/-- Append the actual pullback cut of a base uniformizer in SNC position at the original point. -/
theorem exists_isSncAt_append_of_base_prime_uniformizer
    {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Scheme.DivisorFamily X) (H : X.IdealSheafData)
    (hE : E.IsSnc) (V : Y.Opens) (htrans : SNCStrataUniformizerTransverseOn g E V)
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] (hxV : g x ∈ V)
    (hcoh : Order.coheight (g x) = 1) (a : Y.presheaf.stalk (g x)) (ha : Irreducible a)
    (hH : H.stalkIdeal x = Ideal.span {(g.stalkMap x).hom a}) :
    ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x), (E.append H).IsSncAt x z := by
  classical
  have hat : (g.stalkMap x).hom a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      (sncActiveStratumIdeal E x).stalkIdeal x := by
    apply sncStratum_uniformizer_transverse_at_mem_support g E V htrans
      (Finset.univ.filter fun i => x ∈ (E.component i).support) x
      (sncActiveStratumIdeal_mem_support E x) hxV hcoh a ha
  have ham : a ∈ maximalIdeal (Y.presheaf.stalk (g x)) := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff] using ha.not_isUnit
  have hmapm := map_nonunit (g.stalkMap x).hom a ham
  exact exists_isSncAt_append_of_transverse_principal_cut E H x (hE.2 x)
    (fun _ => ⟨(g.stalkMap x).hom a, hH, hmapm, hat⟩)

/-- An actual effective Cartier pullback supplies its own source ideal equation for the SNC append. -/
theorem exists_isSncAt_append_cartierPullback_of_uniformizer_localEquation
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsDominant g] (E : Scheme.DivisorFamily X) (hE : E.IsSnc)
    (V : Y.Opens) (htrans : SNCStrataUniformizerTransverseOn g E V)
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] (hxV : g x ∈ V)
    (hcoh : Order.coheight (g x) = 1)
    (H : CartierDivisor Y) (hH : H.IsEffective) (f : Y.functionFieldˣ)
    (hf : H.IsLocalEquationAt (g x) f) (a : Y.presheaf.stalk (g x))
    (ha : algebraMap (Y.presheaf.stalk (g x)) Y.functionField a = (f : Y.functionField))
    (hairred : Irreducible a) :
    let hG := cartierPullback_effective_of_effective g H hH
    ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x),
      (E.append (effectiveCartierIdealSheaf (cartierPullback g H) hG)).IsSncAt x z := by
  let G := cartierPullback g H
  let hG := cartierPullback_effective_of_effective g H hH
  let fG := Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f
  have hgf : G.IsLocalEquationAt x fG := cartierPullback_isLocalEquationAt g H x hf
  have hmap : algebraMap (X.presheaf.stalk x) X.functionField ((g.stalkMap x).hom a) =
      (fG : X.functionField) := by
    rw [← dominantFunctionFieldMap_algebraMap g x a, ha]
    rfl
  have hI := effectiveCartier_stalkIdeal_eq_span_of_localEquation G hG x fG hgf
    ((g.stalkMap x).hom a) hmap
  exact exists_isSncAt_append_of_base_prime_uniformizer g E (effectiveCartierIdealSheaf G hG)
    hE V htrans x hxV hcoh a hairred hI

end MixedFujita
