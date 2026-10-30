/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltChartInteriorProfile
public import MixedFujita.KltModelCoefficientBound

/-!
The fibre test prime (step 17R-2, section 7 of the manuscript relative to f).

Let f : X → Y be dominant, x a point of X and Fc a fibre chart at x: an étale chart of X with
m + k coordinates whose last k coordinates are, at x, the pullbacks of the coordinates of an étale
chart of Y centred at f(x). The monomial valuation with weight zero on the first m coordinates and
one on the last k (`fibreChartWeight`) is the order along the generic fibre direction. Its
extraction on the toric chart of Fc (`exists_toric_extraction_model`) is a prime divisor e of a
smooth birational model σ : U → X with

* x in the closure of σ(e) and f(σ(e)) = f(x): the base coordinates have order one along e, so
  none of them is a unit at f(σ(e)), which is then f(x) (`exists_fibre_extraction_prime`);
* log discrepancy k for the pair when x lies in the reference chart of the pair and the boundary
  vanishes at x: the Jacobian has order k − 1 along e in the chart Fc, hence in every chart of X
  at σ(e) (`ord_chartRelativeJacobianDet_eq_of_mem`);
* the coefficient along e of the pullback of the zero divisor of a section t of a divisor of Y at
  least the vanishing order of t at f(x) (`exists_fibre_test_prime`).

Hence a tuple of sections of a divisor of X whose zero divisors are the pullbacks of the zero
divisors of sections t_i on Y has a profile datum at x with objective at most that of the
ordinary-point test of the t_i at f(x) with log discrepancy k = dim Y
(`rel_exists_sncWeightProfile_le_of_fibre_point`), and Lemma 1 on X bounds the vanishing orders
at f(x) of such sections by C j k (`rel_vanishingOrder_le_of_fibre_point`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Weight

/-- The weights of the fibre valuation on a fibre chart: zero on the first m coordinates and one
on the last k. -/
def fibreChartWeight (m k : ℕ) : Fin (m + k) → ℕ := fun a => if m ≤ (a : ℕ) then 1 else 0

theorem fibreChartWeight_natAdd (m k : ℕ) (l : Fin k) :
    fibreChartWeight m k (Fin.natAdd m l) = 1 := by
  simp [fibreChartWeight]

theorem fibreChartWeight_castAdd (m k : ℕ) (i : Fin m) :
    fibreChartWeight m k (Fin.castAdd k i) = 0 := by
  simp [fibreChartWeight, i.isLt]

theorem fibreChartWeight_sum (m k : ℕ) : ∑ a, (fibreChartWeight m k a : ℤ) = k := by
  rw [Fin.sum_univ_add]
  simp only [fibreChartWeight_castAdd, fibreChartWeight_natAdd]
  simp

theorem exists_natAdd_of_fibreChartWeight_ne_zero (m k : ℕ) {a : Fin (m + k)}
    (ha : fibreChartWeight m k a ≠ 0) : ∃ l : Fin k, a = Fin.natAdd m l := by
  have hma : m ≤ (a : ℕ) := by
    by_contra h
    exact ha (by simp [fibreChartWeight, h])
  exact ⟨⟨a - m, by omega⟩, Fin.ext (by simp; omega)⟩

end Weight

section Jacobian

variable {K : Type u} [Field K] {n : ℕ} {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  [X.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian U]

/-- Along a point of a birational model over the overlap of two charts of X, the orders of the
Jacobian determinants of the model with respect to the two charts agree: the canonical equation of
one chart relative to the other is a unit on the overlap. -/
theorem ord_chartRelativeJacobianDet_eq_of_mem (σ : U ⟶ X) [IsDominant σ]
    [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (c₁ c₂ : EtaleChart K X n) (cU : EtaleChart K U n) (e : U) (h₁ : σ e ∈ c₁.U)
    (h₂ : σ e ∈ c₂.U) :
    U.ord (chartRelativeJacobianDet σ c₁ cU) e = U.ord (chartRelativeJacobianDet σ c₂ cU) e := by
  have hchange := chartRelativeJacobianDet_change σ c₁ c₂ cU cU
  have hone : (etaleChartCanonicalEquation cU cU : U.functionField) = 1 := by
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
  rw [hone, mul_one] at hchange
  -- the canonical equation of c₂ relative to c₁ is a unit on the overlap
  obtain ⟨w, hw⟩ := etaleChartCanonicalEquation_transition c₁ c₂ c₁
  have hone₁ : etaleChartCanonicalEquation c₁ c₁ = 1 := by
    apply Units.ext
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
    rfl
  rw [hone₁, mul_one] at hw
  have hV : σ e ∈ c₂.U ⊓ c₁.U := ⟨h₂, h₁⟩
  have := integral_opens_inter_nonempty X c₂.U c₁.U
  have hzero : U.ord (dominantFunctionFieldAlgHom (K := K) σ
      (etaleChartCanonicalEquation c₁ c₂ : X.functionField)) e = 0 := by
    rw [hw, Units.coe_map]
    change U.ord ((dominantFunctionFieldMap σ).hom
      (X.germToFunctionField (c₂.U ⊓ c₁.U) (w : Γ(X, c₂.U ⊓ c₁.U)))) e = 0
    rw [← X.algebraMap_germ_eq_germToFunctionField hV, dominantFunctionFieldMap_algebraMap]
    exact scheme_ord_stalk_unit e
      ((w.isUnit.map (X.presheaf.germ (c₂.U ⊓ c₁.U) (σ e) hV).hom).map (σ.stalkMap e).hom).unit
  have hne₁ : dominantFunctionFieldAlgHom (K := K) σ
      (etaleChartCanonicalEquation c₁ c₂ : X.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  have hne₂ : chartRelativeJacobianDet σ c₂ cU ≠ 0 :=
    (isUnit_chartRelativeJacobianDet_of_bijective σ hσ c₂ cU).ne_zero
  rw [← hchange, U.ord_mul hne₁ hne₂, hzero, zero_add]

end Jacobian

section FibrePrime

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The extraction of the fibre valuation of a fibre chart at x: a prime divisor e of a smooth
birational model σ : U → X with x in the closure of σ(e), f(σ(e)) = f(x), and Jacobian of order
k − 1 along e in the fibre chart. -/
theorem exists_fibre_extraction_prime {m k : ℕ} (hk : 1 ≤ k) (f : X ⟶ Y) [IsDominant f]
    (Fc : EtaleChart K X (m + k)) (x : X) (hx : x ∈ Fc.U)
    (cY : EtaleChart K Y k) (hy : f x ∈ cY.U) (β : Y.presheaf.stalk (f x) →ₐ[K] K)
    (hfib : ∀ l : Fin k, etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) =
      f.stalkMap x (Y.presheaf.germ cY.U (f x) hy
        ((etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords
          (MvPolynomial.X l)))) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension (m + k) (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (_ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U (m + k)) (e : U),
      Order.coheight e = 1 ∧ e ∈ cU.U ∧ x ∈ closure ({σ e} : Set X) ∧ f (σ e) = f x ∧
      U.ord (chartRelativeJacobianDet σ Fc cU) e = (k : ℤ) - 1 := by
  set γ : Fin k → Γ(Y, cY.U) := fun l =>
    (etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords (MvPolynomial.X l)
    with hγ
  have hw : fibreChartWeight m k ≠ 0 := fun h => by
    have h1 := congrFun h (Fin.natAdd m ⟨0, hk⟩)
    rw [fibreChartWeight_natAdd] at h1
    exact one_ne_zero h1
  have hwx : ∀ a, fibreChartWeight m k a ≠ 0 →
      ¬ IsUnit (X.presheaf.germ Fc.U x hx (Fc.coords (MvPolynomial.X a))) := by
    intro a ha hunit
    obtain ⟨l, rfl⟩ := exists_natAdd_of_fibreChartWeight_ne_zero m k ha
    have h1 : X.presheaf.germ Fc.U x hx (Fc.coords (MvPolynomial.X (Fin.natAdd m l))) =
        etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) := rfl
    rw [h1, hfib l] at hunit
    exact etaleChartCentered_germ_not_isUnit cY (f x) hy β l
      ((isUnit_map_iff (f.stalkMap x).hom _).mp hunit)
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, he, hecU, hxe,
    hord, hjac⟩ := exists_toric_extraction_model Fc x hx (fibreChartWeight m k) hw hwx
  have hw' : ∀ a, w' a = fibreChartWeight m k a := by
    have hg1 : g = 1 := by
      have h := hgw (Fin.natAdd m ⟨0, hk⟩)
      rw [fibreChartWeight_natAdd] at h
      exact Nat.eq_one_of_mul_eq_one_right h.symm
    intro a
    rw [hgw a, hg1, one_mul]
  -- the coordinates of the fibre chart are the pullbacks of the base coordinates
  have hcoord : ∀ l : Fin k,
      etaleChartFunctionFieldCoords Fc (MvPolynomial.X (Fin.natAdd m l)) =
        (dominantFunctionFieldMap f).hom (Y.germToFunctionField cY.U (γ l)) := by
    intro l
    rw [← etaleChart_stalkFunctionField_comp_stalkCoords Fc x hx, AlgHom.comp_apply, hfib l]
    change algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x _) = _
    rw [← dominantFunctionFieldMap_algebraMap, Scheme.algebraMap_germ_eq_germToFunctionField]
  have hsp : σ e ⤳ x := specializes_iff_mem_closure.mpr hxe
  have hfsp : f (σ e) ⤳ f x := hsp.map f.continuous
  have hmem : f (σ e) ∈ cY.U := hfsp.mem_open cY.U.isOpen hy
  have hfe : f (σ e) = f x := by
    refine etaleChartCentered_eq_of_specializes cY (f x) hy β (f (σ e)) hfsp hmem
      fun l hunit => ?_
    have h1 := hord (Fin.natAdd m l)
    rw [hw', fibreChartWeight_natAdd, hcoord l] at h1
    have h0 : U.ord (dominantFunctionFieldAlgHom (K := K) σ
        ((dominantFunctionFieldMap f).hom (Y.germToFunctionField cY.U (γ l)))) e = 0 := by
      change U.ord ((dominantFunctionFieldMap σ).hom ((dominantFunctionFieldMap f).hom
        (Y.germToFunctionField cY.U (γ l)))) e = 0
      rw [← Y.algebraMap_germ_eq_germToFunctionField hmem, dominantFunctionFieldMap_algebraMap,
        dominantFunctionFieldMap_algebraMap]
      exact scheme_ord_stalk_unit e
        ((hunit.map (f.stalkMap (σ e)).hom).map (σ.stalkMap e).hom).unit
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hecU, hxe, hfe, ?_⟩
  rw [hjac]
  simp only [hw']
  rw [fibreChartWeight_sum]

/-- The fibre test prime at a boundary-free point of the reference chart: normalized log
discrepancy k for the pair, and coefficients of pulled back zero divisors of sections on Y at
least their vanishing orders at f(x). -/
theorem exists_fibre_test_prime {m k : ℕ} (hk : 1 ≤ k) (f : X ⟶ Y) [IsDominant f]
    (cX : EtaleChart K X (m + k)) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ : CartierDivisor X) (x : X) (hxX : x ∈ cX.U) (hD : D₀.IsLocalEquationAt x (fX ^ d))
    (Fc : EtaleChart K X (m + k)) (hx : x ∈ Fc.U)
    (cY : EtaleChart K Y k) (hy : f x ∈ cY.U) (β : Y.presheaf.stalk (f x) →ₐ[K] K)
    (hfib : ∀ l : Fin k, etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) =
      f.stalkMap x (Y.presheaf.germ cY.U (f x) hy
        ((etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords
          (MvPolynomial.X l)))) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension (m + k) (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U (m + k)) (e : CodimensionOnePoint U),
      x ∈ closure ({σ (e : U)} : Set X) ∧
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor (m + k) σ hσ cX fX d D₀ cU
        etaleCharts_cover) (e : U)) / d = k ∧
      ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cX fX d D₀ cU
        etaleCharts_cover) (e : U)) / d = k ∧
      ∀ (E : CartierDivisor Y) (t : Γ(E.sheaf, ⊤)) (ht : t ≠ 0),
        ((cartierSectionVanishingOrder E (f x) t).toNat : ℝ) ≤
          (cartierCoefficient (cartierPullback σ (cartierPullback f
            (cartierSectionZeroDivisor E t ht))) (e : U) : ℝ) := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hecU, hxe, hfe, hjac⟩ :=
    exists_fibre_extraction_prime hk f Fc x hx cY hy β hfib
  have hsp : σ e ⤳ x := specializes_iff_mem_closure.mpr hxe
  have heX : σ e ∈ cX.U := hsp.mem_open cX.U.isOpen hxX
  have heF : σ e ∈ Fc.U := hsp.mem_open Fc.U.isOpen hx
  -- the boundary vanishes at the generization σ(e) of x
  have hDe : D₀.IsLocalEquationAt (σ e) (fX ^ d) := by
    obtain ⟨V, hV, hcls⟩ := CartierDivisor.isLocalEquationAt_iff.mp hD
    have : Nonempty V := ⟨⟨x, hV⟩⟩
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hcls (hsp.mem_open V.isOpen hV)
  have hA := logDiscrepancyDivisor_coefficient_of_local_boundary_zero σ hσ cX fX d D₀ cU e hecU
    hDe
  rw [ord_chartRelativeJacobianDet_eq_of_mem σ hσ cX Fc cU e heX heF, hjac] at hA
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hAnorm : ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor (m + k) σ hσ cX fX d D₀ cU
      etaleCharts_cover) e) / d = k := by
    rw [hA]
    push_cast
    field_simp
    ring
  have hAnorm' : ((d : ℝ) - cartierCoefficient (crepantBoundaryCartier σ hσ cX fX d D₀ cU
      etaleCharts_cover) e) / d = k := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hA]
    push_cast
    field_simp
    ring
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, ⟨e, he⟩, hxe, hAnorm, hAnorm', ?_⟩
  intro E t ht
  have hsm : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (m + k) _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint U)
  have hv := cartierPullback_sectionZeroDivisor_coefficient_ge_vanishingOrder (σ ≫ f) E t ht
    (⟨e, he⟩ : CodimensionOnePoint U)
  change ((cartierSectionVanishingOrder E ((σ ≫ f) e) t).toNat : ℤ) ≤
    cartierCoefficient (cartierPullback (σ ≫ f) (cartierSectionZeroDivisor E t ht)) e at hv
  rw [Scheme.Hom.comp_apply, hfe, cartierPullback_comp] at hv
  exact_mod_cast hv

variable [IsLocallyNoetherian X] [CharZero K] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A tuple of sections of a divisor of X whose zero divisors are the pullbacks of the zero
divisors of sections t_i of a divisor of Y has a profile datum at a boundary-free point x of the
reference chart with a fibre chart, with objective at most the ordinary-point objective of the t_i
at f(x) with log discrepancy k. -/
theorem rel_exists_sncWeightProfile_le_of_fibre_point {m k : ℕ} (hk : 1 ≤ k) (f : X ⟶ Y)
    [IsDominant f] (cX : EtaleChart K X (m + k)) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor X) (E : CartierDivisor Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0) (t : Fin N → Γ(E.sheaf, ⊤)) (ht : ∀ i, t i ≠ 0)
    (hst : ∀ i, cartierSectionZeroDivisor D (s i) (hs i) =
      cartierPullback f (cartierSectionZeroDivisor E (t i) (ht i)))
    (x : X) (hxX : x ∈ cX.U) (hD : D₀.IsLocalEquationAt x (fX ^ d))
    (Fc : EtaleChart K X (m + k)) (hx : x ∈ Fc.U)
    (cY : EtaleChart K Y k) (hy : f x ∈ cY.U) (β : Y.presheaf.stalk (f x) →ₐ[K] K)
    (hfib : ∀ l : Fin k, etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) =
      f.stalkMap x (Y.presheaf.germ cY.U (f x) hy
        ((etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords
          (MvPolynomial.X l))))
    {τ j lam : ℝ} (hτ : 0 < τ) (hj : 0 < j) (hlam : 0 ≤ lam) :
    ∃ p ∈ sncWeightProfiles cX fX d D₀ D x s,
      (∑ i, Real.exp (p.1 / τ - p.2 i / j)) ≤
        ∑ i, Real.exp (lam * k / τ -
          lam * ((cartierSectionVanishingOrder E (f x) (t i)).toNat : ℝ) / j) := by
  obtain ⟨X', hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX', r, ξ, hinj, hξ, hsnc,
    hBsupp, hGsupp⟩ := exists_proper_snc_model_with cX fX d D₀
      (fun i => cartierSectionZeroDivisor D (s i) (hs i))
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hAnorm, -, hv⟩ :=
    exists_fibre_test_prime hk f cX fX d hd D₀ x hxX hD Fc hx cY hy β hfib
  obtain ⟨w, hw0, hwΦ, hle⟩ := exists_sncWeight_objective_le_of_test_prime π hπ cX fX d hd D₀
    cX' ξ hinj hξ hsnc hBsupp (fun i => cartierSectionZeroDivisor D (s i) (hs i)) hGsupp
    σ hσ cU e x hxe hτ j lam hlam
  have hbound : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX d D₀ cX' etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) τ j w ≤
      ∑ i, Real.exp (lam * k / τ -
        lam * ((cartierSectionVanishingOrder E (f x) (t i)).toNat : ℝ) / j) := by
    refine hle.trans (Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_)
    rw [hAnorm]
    have hv' := hv E (t i) (ht i)
    rw [← hst i] at hv'
    exact sub_le_sub_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' hlam) hj.le) _
  exact ⟨(∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX d D₀ cX' etaleCharts_cover) (ξ k)) / d),
    fun i => ∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)),
    ⟨hs, X', hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX', r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hwΦ, rfl, fun i => rfl⟩, hbound⟩

variable [IsAlgClosed K]

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))] in
/-- Lemma 1 on X at fibre test primes: the vanishing orders at f(x) of sections on Y whose
pullbacks are sections of j L are at most C j k, uniformly in the boundary-free point x of the
reference chart with a fibre chart. -/
theorem rel_vanishingOrder_le_of_fibre_point {m k : ℕ} (hk : 1 ≤ k) (f : X ⟶ Y) [IsDominant f]
    (cX : EtaleChart K X (m + k)) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ L : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : X) (_ : x ∈ cX.U) (_ : D₀.IsLocalEquationAt x (fX ^ d))
      (Fc : EtaleChart K X (m + k)) (hx : x ∈ Fc.U)
      (cY : EtaleChart K Y k) (hy : f x ∈ cY.U) (β : Y.presheaf.stalk (f x) →ₐ[K] K),
      (∀ l : Fin k, etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) =
        f.stalkMap x (Y.presheaf.germ cY.U (f x) hy
          ((etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords
            (MvPolynomial.X l)))) →
      ∀ (j : ℕ), 1 ≤ j → ∀ (E : CartierDivisor Y) (t : Γ(E.sheaf, ⊤)) (ht : t ≠ 0)
        (s : Γ((j • L).sheaf, ⊤)) (hs : s ≠ 0),
        cartierSectionZeroDivisor (j • L) s hs =
          cartierPullback f (cartierSectionZeroDivisor E t ht) →
        ((cartierSectionVanishingOrder E (f x) t).toNat : ℝ) ≤ (C : ℝ) * j * k := by
  obtain ⟨C, hC, hc⟩ := klt_model_coefficient_le (by omega : 1 ≤ m + k) cX fX d hd D₀ L hklt hH
  refine ⟨C, hC, ?_⟩
  intro x hxX hD Fc hx cY hy β hfib j hj E t ht s hs hst
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, -, -, hAnorm', hv⟩ :=
    exists_fibre_test_prime hk f cX fX d hd D₀ x hxX hD Fc hx cY hy β hfib
  have hbound := (hc U σ hσ cU e j hj s hs).2
  rw [hAnorm', hst] at hbound
  exact (hv E t ht).trans hbound

end FibrePrime

end MixedFujita
