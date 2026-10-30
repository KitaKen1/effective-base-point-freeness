/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCNefBigHigherVanishing
public import MixedFujita.SNCPointDivisorFamily

/-! Nef-and-big higher vanishing in the original prime-point SNC interface.
The finite Cartier presentation required by principalization is constructed,
and zero-dimensional schemes are handled by Grothendieck vanishing. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- On a normal scheme, a Cartier divisor supported on the listed prime points
is the corresponding integral combination of their Cartier representatives. -/
theorem cartierDivisor_eq_snc_component_sum_of_support
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (F : Fin r → CartierDivisor X)
    (hF : ∀ i (t : CodimensionOnePoint X),
      cartierCoefficient (F i) t = if (t : X) = ξ i then 1 else 0)
    (B : CartierDivisor X)
    (hsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient B t = 0) :
    B = ∑ i, cartierCoefficient B (ξ i) • F i := by
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm
  intro t
  rcases cartierCoefficient_member_combination ξ hinj F hF
      (fun i => cartierCoefficient B (ξ i)) t with ⟨i, hi, he⟩ | ⟨hi, he⟩
  · rw [he, hi]
  · rw [he, hsupp t hi]

/-- Signed SNC roundup has nef-and-big vanishing in every positive degree,
with the component Cartier presentation supplied internally. This includes
dimension zero and assumes no vanishing or resolution certificate. -/
theorem signed_snc_roundup_nef_big_higher_vanishing_of_charZero
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (H : CartierDivisor X) (hH : CartierIsAmpleProj k H)
    (cX : EtaleChart k X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily k n ξ) (B E Q : CartierDivisor X) (d : ℕ) (hd : 1 ≤ d)
    (hsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient B t = 0)
    (hE : ∀ t : CodimensionOnePoint X, cartierCoefficient E t =
      ⌈-((cartierCoefficient B t : ℝ) / (d : ℝ))⌉)
    (hnef : CartierIsNef k (d • (Q - smoothCanonicalDivisor cX) - B))
    (hbig : CartierIsBig k (d • (Q - smoothCanonicalDivisor cX) - B))
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology (Q + E).sheaf q) := by
  by_cases hn : n = 0
  · apply actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt
    rw [etaleChart_topologicalKrullDim cX, hn]
    exact_mod_cast (show 0 < q by omega)
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := k) x
  obtain ⟨F, hF, hFI, hFc⟩ := exists_snc_component_cartier (K := k) ξ hξ hsnc
  have hBsum := cartierDivisor_eq_snc_component_sum_of_support hnorm ξ hinj F hFc B hsupp
  have hEsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient E t = 0 := by
    intro t ht
    rw [hE t, hsupp t ht]
    norm_num
  have hEsum : E = ∑ i, ⌈-((cartierCoefficient B (ξ i) : ℝ) / (d : ℝ))⌉ • F i := by
    rw [cartierDivisor_eq_snc_component_sum_of_support hnorm ξ hinj F hFc E hEsupp]
    exact Finset.sum_congr rfl fun i _ => by rw [hE ⟨ξ i, hξ i⟩]
  have hsum (a : Fin r → ℤ) :
      (∑ i : ULift.{u} (Fin r), a i.down • F i.down) = ∑ i, a i • F i :=
    Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)
  have hBU : (∑ i : (sncDivisorFamilyOfPoints ξ).ι,
      cartierCoefficient B (ξ i.down) • F i.down) = B :=
    (hsum _).trans hBsum.symm
  have hEU : (∑ i : (sncDivisorFamilyOfPoints ξ).ι,
      ⌈-((cartierCoefficient B (ξ i.down) : ℝ) / (d : ℝ))⌉ • F i.down) = E :=
    (hsum _).trans hEsum.symm
  have hv := snc_projective_nef_big_roundup_higher_vanishing k n (by omega) cX
    (sncDivisorFamilyOfPoints ξ) (sncDivisorFamilyOfPoints_isSnc ξ hsnc)
    (fun i => F i.down) (fun i => hF i.down) (fun i => hFI i.down)
    (fun i => cartierCoefficient B (ξ i.down)) d hd Q H hH
    (by simpa only [hBU] using hnef)
    (by simpa only [hBU] using hbig) q hq
  simpa only [hEU] using hv

/-- Fractional SNC boundaries give the usual nef-and-big vanishing statement
in any positive degree, using only prime-point coefficients for the components. -/
theorem snc_projective_fractional_nef_big_higher_vanishing
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (H : CartierDivisor X) (hH : CartierIsAmpleProj k H)
    (cX : EtaleChart k X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily k n ξ) (F : Fin r → CartierDivisor X)
    (hF : ∀ i (t : CodimensionOnePoint X),
      cartierCoefficient (F i) t = if (t : X) = ξ i then 1 else 0)
    (Q : CartierDivisor X) (d : ℕ) (hd : 1 ≤ d) (a : Fin r → ℕ) (ha : ∀ i, a i < d)
    (hnef : CartierIsNef k (d • (Q - smoothCanonicalDivisor cX) - ∑ i, a i • F i))
    (hbig : CartierIsBig k (d • (Q - smoothCanonicalDivisor cX) - ∑ i, a i • F i))
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology Q.sheaf q) := by
  let : IsNoetherian X := properOverField_scheme_isNoetherian (K := k) (X := X)
  let B := ∑ i, a i • F i
  have hcoeff (t : CodimensionOnePoint X) :=
    cartierCoefficient_member_combination ξ hinj F hF (fun i => (a i : ℤ)) t
  simp only [natCast_zsmul] at hcoeff
  have hsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient B t = 0 := by
    intro t ht
    rcases hcoeff t with ⟨i, hi, _⟩ | ⟨_, he⟩
    · exact (ht ⟨i, hi.symm⟩).elim
    · exact he
  have hround : ∀ t : CodimensionOnePoint X, cartierCoefficient (0 : CartierDivisor X) t =
      ⌈-((cartierCoefficient B t : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [cartierCoefficient_zero]
    rcases hcoeff t with ⟨i, _, he⟩ | ⟨_, he⟩
    · change 0 = ⌈-((cartierCoefficient (∑ i, a i • F i) t : ℝ) / (d : ℝ))⌉
      rw [he, Int.ceil_neg, Int.floor_eq_zero_iff.mpr ?_, neg_zero]
      constructor
      · positivity
      · exact (div_lt_one (by exact_mod_cast (show 0 < d by omega))).mpr
          (by exact_mod_cast ha i)
    · change 0 = ⌈-((cartierCoefficient (∑ i, a i • F i) t : ℝ) / (d : ℝ))⌉
      rw [he]
      norm_num
  simpa only [add_zero] using signed_snc_roundup_nef_big_higher_vanishing_of_charZero
    k H hH cX ξ hinj hξ hsnc B 0 Q d hd hsupp hround hnef hbig q hq

end MixedFujita
