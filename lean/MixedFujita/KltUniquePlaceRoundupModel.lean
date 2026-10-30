/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCTwoPairAmpleModel
public import MixedFujita.RationalThresholdTieBreak
public import MixedFujita.SNCComponentCartier
public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.KltConnectednessBoundary
public import MixedFujita.KltStableBaseLocusCenter
public import MixedFujita.TwistedCartierApproximation
public import MixedFujita.CrepantSNCBasePointLogCanonical

/-!
A unique log canonical place with round-up data over an isolated log canonical centre (step 16,
the tie-breaking of the base point free theorem, after Kollár–Mori 3.3).

Let (X, Δ) be a klt anchor, (X, Δ₃) log canonical whose non-klt locus is W = closure {η}, D nef
with a D − (K_X + Δ) nef and all large j D − (K_X + Δ₃) ample. On the SNC model with a supported
ample correction p*(c A) − G (`exists_snc_two_pair_model_with_supported_ample`) put, for a small
ε = 1/M and the threshold s = u/v of `exists_rational_threshold_tie_break`,
  Θ = (1 − s) Θ₀ + s Θ₃ + ε G − δ Σ_{i ∈ J ∖ i₀} Eᵢ,
where Θ₀, Θ₃ are the crepant boundaries, J the indices where the interpolated coefficient reaches
1 and δ = 1/M' a further small perturbation. Then Θ has coefficient exactly 1 at one SNC
component S = E_{i₀}, lying over W, and coefficients < 1 elsewhere; with B = d Θ the round-up
E − S = ⌈−B/d⌉ has E effective and exceptional; and d (p*(b D) − K_T) − B is ample for all large b.
This is the input of `original_basepoint_removed_of_usual_KV_snc_roundup_cut`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- **A unique log canonical place over an isolated centre, with round-up data.** -/
theorem klt_isolated_center_exists_unique_place_roundup_model
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ)
    (r : ℕ) (hr : 1 ≤ r) (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D')
    (d₃ : ℕ) (hd₃ : 1 ≤ d₃) (D₃ : CartierDivisor X)
    (heff₃ : LogPairBoundaryEffective c₀ f₀ d₃ D₃) (hlc₃ : LogPairIsLogCanonical c₀ f₀ d₃ D₃)
    (η : X) (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c₀ f₀ d₃ D₃) ↔ x ∈ closure {η})
    (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnefa : CartierIsNef K ((r * a) • D - D'))
    (b₃ : ℕ) (hamp₃ : ∀ j : ℕ, b₃ ≤ j → CartierIsAmpleProj K ((d₃ * j) • D - D₃)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (_ : IsProper (T ↘ Spec (CommRingCat.of K)))
      (p : T ⟶ X) (_ : IsDominant p) (_ : p.IsOver (Spec (CommRingCat.of K))) (_ : IsProper p)
      (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
      (cT : EtaleChart K T n) (R : ℕ) (ξ : Fin R → T) (i₀ : Fin R)
      (B E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective) (dT b₀ : ℕ),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∃ J : CartierDivisor T, CartierIsAmpleProj K J) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0) ∧
      cartierCoefficient E (ξ i₀) = 0 ∧
      effectiveCartierIdealSheaf S hS = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T) ∧
      (∀ z : CodimensionOnePoint T, cartierCoefficient S (z : T) = if (z : T) = ξ i₀ then 1 else 0) ∧
      1 ≤ dT ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient B (t : T) : ℝ) / (dT : ℝ))⌉) ∧
      cartierCoefficient B (ξ i₀) = dT ∧
      p (ξ i₀) ∈ closure {η} ∧
      ∀ b : ℕ, b₀ ≤ b →
        CartierIsAmpleProj K (dT • (cartierPullback p (b • D) - smoothCanonicalDivisor cT) - B) := by
  -- the model with a supported ample correction
  obtain ⟨T, hTi, hTo, hTN, hTs, hTp, p, hpdom, hpover, hpprop, hp, cT, R, ξ, c, G, hinj, hξ,
    hsnc, hC₀supp, hC₃supp, hc, hGeff, hGsupp, hAmp⟩ :=
    exists_snc_two_pair_model_with_supported_ample K hdim hn hnorm c₀ f₀ r d₃ D' D₃ A hA
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hTp
  let := hpdom
  let := hpover
  let := hpprop
  set C₀ := crepantBoundaryCartier p hp c₀ f₀ r D' cT etaleCharts_cover with hC₀def
  set C₃ := crepantBoundaryCartier p hp c₀ f₀ d₃ D₃ cT etaleCharts_cover with hC₃def
  -- the components of the SNC family as Cartier divisors
  obtain ⟨Ec, hEc, hEcI, hEcoef⟩ := exists_snc_component_cartier (K := K) (n := n) ξ hξ hsnc
  have hEc' : ∀ (i : Fin R) (t : T), Order.coheight t = 1 →
      cartierCoefficient (Ec i) t = if t = ξ i then 1 else 0 :=
    fun i t ht => hEcoef i ⟨t, ht⟩
  -- the normalized coefficients on the family
  let θ₀ : Fin R → ℚ := fun i => (cartierCoefficient C₀ (ξ i) : ℚ) / r
  let θ₃ : Fin R → ℚ := fun i => (cartierCoefficient C₃ (ξ i) : ℚ) / d₃
  let gq : Fin R → ℚ := fun i => (cartierCoefficient G (ξ i) : ℚ)
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr
  have hd₃0 : (0 : ℚ) < d₃ := by exact_mod_cast hd₃
  have hθ₀ : ∀ i, θ₀ i < 1 := by
    intro i
    have h := logPairIsKlt_crepantBoundary_coefficient_lt p hp c₀ f₀ r D' hklt cT ⟨ξ i, hξ i⟩
    simp only [θ₀]
    rw [div_lt_one hr0]
    exact_mod_cast h
  have hθ₃ : ∀ i, θ₃ i ≤ 1 := by
    intro i
    have h := logPairIsLogCanonical_crepantBoundary_coefficient_le p hp c₀ f₀ d₃ D₃ hlc₃ cT
      ⟨ξ i, hξ i⟩
    simp only [θ₃]
    rw [div_le_one hd₃0]
    exact_mod_cast h
  have hgq : ∀ i, 0 ≤ gq i := fun i => by
    simp only [gq]
    exact_mod_cast cartierCoefficient_nonneg_of_isEffective G hGeff (ξ i)
  have hsncCrit := fun (x : X) => logPairIsKltOverBasePoint_iff_crepant_snc_coefficients p hp
    (𝟙 X) x c₀ f₀ d₃ hd₃ D₃ cT ξ hinj hξ hsnc hC₃supp
  have hL : ∃ i, θ₃ i = 1 := by
    have hnk := (hNK η).mpr (subset_closure rfl)
    rw [hsncCrit η] at hnk
    push_neg at hnk
    obtain ⟨i, -, hi⟩ := hnk
    have hle := logPairIsLogCanonical_crepantBoundary_coefficient_le p hp c₀ f₀ d₃ D₃ hlc₃ cT
      ⟨ξ i, hξ i⟩
    refine ⟨i, ?_⟩
    simp only [θ₃]
    have heq : cartierCoefficient C₃ (ξ i) = d₃ := le_antisymm hle hi
    rw [heq]
    push_cast
    exact div_self hd₃0.ne'
  -- the parameters
  have hA₃ : CartierIsAmpleProj K ((d₃ * b₃) • D - D₃) := hamp₃ b₃ le_rfl
  obtain ⟨k₃, hk₃, hk₃nef⟩ := exists_nsmul_sub_isNef hA₃ A
  obtain ⟨M₀, hM₀⟩ := exists_rational_threshold_tie_break θ₀ θ₃ gq hθ₀ hθ₃ hgq hL
  set M := max M₀ (2 * k₃ * d₃ * c) + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hMM₀ : M₀ ≤ M := by omega
  have hMk : 2 * k₃ * d₃ * c ≤ M := by omega
  obtain ⟨u, v, J, hu, huv, hv2u, hJne, hJL, hcoef⟩ := hM₀ M hMM₀
  obtain ⟨i₀, hi₀⟩ := hJne
  set F := ∑ i ∈ J.erase i₀, Ec i with hFdef
  set Amp := cartierPullback p (c • A) - G with hAmpdef
  obtain ⟨k₁, hk₁, hk₁nef⟩ := exists_nsmul_sub_isNef hAmp (-F)
  set M' := M * (k₁ + 1) with hM'def
  set dT := r * d₃ * v * M' with hdTdef
  set α := r * d₃ * v * (k₁ + 1) with hαdef
  set β := r * d₃ * v with hβdef
  set B := (d₃ * (v - u) * M') • C₀ + (r * u * M') • C₃ + α • G - β • F with hBdef
  have hv1 : 1 ≤ v := le_trans hu huv
  have hdT1 : 1 ≤ dT := by
    rw [hdTdef, hM'def]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the coefficients of F and of B on the family
  have hFcoef : ∀ (t : T), Order.coheight t = 1 →
      cartierCoefficient F t = ∑ i ∈ J.erase i₀, (if t = ξ i then 1 else 0) := by
    intro t ht
    rw [hFdef, cartierCoefficient_sum]
    exact Finset.sum_congr rfl fun i _ => hEc' i t ht
  have hFξ : ∀ j, cartierCoefficient F (ξ j) = if j ∈ J.erase i₀ then 1 else 0 := by
    intro j
    rw [hFcoef (ξ j) (hξ j)]
    simp only [hinj.eq_iff]
    rw [Finset.sum_ite_eq]
  have hFoff : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient F t = 0 := by
    intro t ht
    rw [hFcoef t t.property]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    exact fun h => ht ⟨i, h.symm⟩
  have hBξ : ∀ j, cartierCoefficient B (ξ j) =
      ((d₃ * (v - u) * M' : ℕ) : ℤ) * cartierCoefficient C₀ (ξ j) +
        ((r * u * M' : ℕ) : ℤ) * cartierCoefficient C₃ (ξ j) +
        (α : ℤ) * cartierCoefficient G (ξ j) - (β : ℤ) * (if j ∈ J.erase i₀ then 1 else 0) := by
    intro j
    rw [hBdef, cartierCoefficient_sub, cartierCoefficient_add, cartierCoefficient_add,
      cartierCoefficient_nsmul, cartierCoefficient_nsmul, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul, hFξ]
  have hBoff : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient B (t : T) = 0 := by
    intro t ht
    rw [hBdef, cartierCoefficient_sub, cartierCoefficient_add, cartierCoefficient_add,
      cartierCoefficient_nsmul, cartierCoefficient_nsmul, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul, hC₀supp t ht, hC₃supp t ht, hGsupp t ht, hFoff t ht]
    simp
  -- the normalized coefficient of B
  set y : Fin R → ℚ := fun j => (cartierCoefficient B (ξ j) : ℚ) / dT with hydef
  have hdT0 : (0 : ℚ) < dT := by exact_mod_cast hdT1
  have hM'pos : (0 : ℚ) < M' := by
    rw [hM'def]
    push_cast
    positivity
  have hyc : ∀ j, y j = ((1 - (u : ℚ) / v) * θ₀ j + ((u : ℚ) / v) * θ₃ j + gq j / M) -
      (if j ∈ J.erase i₀ then 1 else 0) / M' := by
    intro j
    simp only [hydef, θ₀, θ₃, gq]
    rw [hBξ j]
    have hvq : (0 : ℚ) < v := by exact_mod_cast hv1
    have hMq : (0 : ℚ) < M := by exact_mod_cast hM1
    rw [hdTdef, hαdef, hβdef, hM'def]
    split_ifs <;> push_cast [Nat.cast_sub huv] <;> field_simp <;> ring
  have hy₀ : y i₀ = 1 := by
    rw [hyc i₀, if_neg (Finset.notMem_erase i₀ J), zero_div, sub_zero]
    exact ((hcoef i₀).2).mpr hi₀
  have hyJ : ∀ j ∈ J, j ≠ i₀ → y j = 1 - 1 / M' := by
    intro j hj hji
    rw [hyc j, if_pos (Finset.mem_erase.mpr ⟨hji, hj⟩), ((hcoef j).2).mpr hj]
  have hynot : ∀ j, j ∉ J → y j < 1 := by
    intro j hj
    rw [hyc j, if_neg (fun h => hj (Finset.mem_of_mem_erase h)), zero_div, sub_zero]
    exact lt_of_le_of_ne (hcoef j).1 (fun h => hj (((hcoef j).2).mp h))
  have hylt : ∀ j, j ≠ i₀ → y j < 1 := by
    intro j hji
    by_cases hj : j ∈ J
    · rw [hyJ j hj hji]
      have : 0 < 1 / (M' : ℚ) := by positivity
      linarith
    · exact hynot j hj
  -- the round-up coefficients
  set e : Fin R → ℤ := fun j => ⌈-(y j)⌉ + (if j = i₀ then 1 else 0) with hedef
  have he₀ : e i₀ = 0 := by
    simp only [hedef, if_pos rfl, hy₀]
    norm_num
  have henn : ∀ j, 0 ≤ e j := by
    intro j
    by_cases hji : j = i₀
    · rw [hji, he₀]
    · simp only [hedef, if_neg hji, add_zero]
      have h := hylt j hji
      have : (-1 : ℚ) < -(y j) := by linarith
      have h2 : (-1 : ℤ) < ⌈-(y j)⌉ := by
        have := Int.lt_ceil.mpr this
        exact_mod_cast this
      omega
  set E := ∑ j, (e j).toNat • Ec j with hEdef
  set S := Ec i₀ with hSdef
  have hEeff : E.IsEffective := by
    rw [hEdef]
    exact Finset.sum_induction _ (fun D : CartierDivisor T => D.IsEffective)
      (fun _ _ h1 h2 => h1.add h2) CartierDivisor.isEffective_zero
      (fun j _ => nsmul_isEffective_of_isEffective (hEc j) _)
  have hEcoefξ : ∀ (t : T), Order.coheight t = 1 →
      cartierCoefficient E t = ∑ j, ((e j).toNat : ℤ) * (if t = ξ j then 1 else 0) := by
    intro t ht
    rw [hEdef, cartierCoefficient_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [cartierCoefficient_nsmul, hEc' j t ht]
  have hEξ : ∀ k, cartierCoefficient E (ξ k) = e k := by
    intro k
    rw [hEcoefξ (ξ k) (hξ k)]
    simp only [hinj.eq_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k), Int.toNat_of_nonneg (henn k)]
  have hEoff : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient E (t : T) = 0 := by
    intro t ht
    rw [hEcoefξ t t.property]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => ht ⟨j, h.symm⟩), mul_zero]
  have hyR : ∀ j, ((cartierCoefficient B (ξ j) : ℝ) / (dT : ℝ)) = ((y j : ℚ) : ℝ) := by
    intro j
    simp only [hydef]
    push_cast
    rfl
  refine ⟨T, hTi, hTo, hTN, hTs, hTp, p, hpdom, hpover, hpprop, hp, cT, R, ξ, i₀, B, E, S, hEeff,
    hEc i₀, dT, max a b₃, hinj, hξ, hsnc, ⟨Amp, hAmp⟩, ?_, by rw [hEξ, he₀], hEcI i₀,
    fun z => hEcoef i₀ z, hdT1, hBoff, ?_, ?_, ?_, ?_⟩
  · -- E is exceptional
    intro t hpt
    by_cases ht : (t : T) ∈ Set.range ξ
    · obtain ⟨k, hk⟩ := ht
      have hpk : Order.coheight (p (ξ k)) = 1 := by rw [hk]; exact hpt
      rw [← hk, hEξ k]
      by_cases hk0 : k = i₀
      · rw [hk0, he₀]
      · have hyk : 0 ≤ y k := by
          by_cases hkJ : k ∈ J
          · rw [hyJ k hkJ hk0]
            have : 1 / (M' : ℚ) ≤ 1 := by
              rw [div_le_one hM'pos]
              rw [hM'def]
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
            linarith
          · rw [hyc k, if_neg (fun h => hkJ (Finset.mem_of_mem_erase h)), zero_div, sub_zero]
            have h0 : 0 ≤ θ₀ k := by
              simp only [θ₀]
              have := crepantBoundaryCartier_coefficient_nonneg_of_coheight p hp c₀ f₀ r D' cT
                hnorm hcov heff ⟨ξ k, hξ k⟩ hpk
              positivity
            have h3 : 0 ≤ θ₃ k := by
              simp only [θ₃]
              have := crepantBoundaryCartier_coefficient_nonneg_of_coheight p hp c₀ f₀ d₃ D₃ cT
                hnorm hcov heff₃ ⟨ξ k, hξ k⟩ hpk
              positivity
            have hs0 : 0 ≤ (u : ℚ) / v := by positivity
            have hs1 : (u : ℚ) / v ≤ 1 := by
              rw [div_le_one (by exact_mod_cast hv1)]
              exact_mod_cast huv
            have hgM : 0 ≤ gq k / M := by
              have := hgq k
              positivity
            nlinarith
        have hle : ⌈-(y k)⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
        have := henn k
        simp only [hedef, if_neg hk0, add_zero] at this ⊢
        omega
    · exact hEoff t ht
  · -- the round-up
    intro t
    by_cases ht : (t : T) ∈ Set.range ξ
    · obtain ⟨k, hk⟩ := ht
      have hSk : cartierCoefficient S (ξ k) = if k = i₀ then 1 else 0 := by
        simp only [hSdef, hEc' i₀ (ξ k) (hξ k), hinj.eq_iff]
      rw [← hk, cartierCoefficient_sub, hEξ k, hSk, hyR k, ← Rat.cast_neg, Rat.ceil_cast]
      simp only [hedef]
      split_ifs <;> ring
    · have hSt : cartierCoefficient S (t : T) = 0 := by
        rw [hSdef, hEc' i₀ t t.property, if_neg (fun h => ht ⟨i₀, h.symm⟩)]
      rw [cartierCoefficient_sub, hEoff t ht, hSt, hBoff t ht]
      simp
  · -- the coefficient of the place
    have h := hy₀
    simp only [hydef] at h
    have hdT0 : (dT : ℚ) ≠ 0 := hdT0.ne'
    rw [div_eq_one_iff_eq hdT0] at h
    exact_mod_cast h
  · -- the place lies over the centre
    apply (hNK _).mp
    intro hk
    rw [hsncCrit] at hk
    have h := hk i₀ (by simp only [Category.comp_id]; exact subset_closure rfl)
    have h3 : θ₃ i₀ = 1 := hJL i₀ hi₀
    simp only [θ₃] at h3
    rw [div_eq_one_iff_eq hd₃0.ne'] at h3
    have h3' : cartierCoefficient C₃ (ξ i₀) = d₃ := by exact_mod_cast h3
    have h' : cartierCoefficient C₃ (ξ i₀) < d₃ := h
    omega
  · -- the ample adjoints
    intro b hb
    obtain ⟨ba, hba⟩ : ∃ ba, b = a + ba := ⟨b - a, by omega⟩
    obtain ⟨bb, hbb⟩ : ∃ bb, b = b₃ + bb := ⟨b - b₃, by omega⟩
    set x₀ := d₃ * (v - u) * M' with hx₀def
    set x₃ := r * u * M' with hx₃def
    have hdTsum : x₀ * r + x₃ * d₃ = dT := by
      rw [hx₀def, hx₃def, hdTdef, hβdef]
      have : v = (v - u) + u := (Nat.sub_add_cancel huv).symm
      conv_rhs => rw [this]
      ring
    -- the pulled form and the crepant boundaries
    set PF := pullbackFormDivisor p hp c₀ f₀ cT etaleCharts_cover with hPFdef
    obtain ⟨φ, hφ⟩ : ∃ φ : T.functionFieldˣ,
        PF = smoothCanonicalDivisor cT + principalCartierDivisor T φ := ⟨_, rfl⟩
    have hC₀ : C₀ = cartierPullback p D' - r • PF := by
      rw [← crepantBoundaryCartier_recombine p hp c₀ f₀ r D' cT etaleCharts_cover]
      abel
    have hC₃ : C₃ = cartierPullback p D₃ - d₃ • PF := by
      rw [← crepantBoundaryCartier_recombine p hp c₀ f₀ d₃ D₃ cT etaleCharts_cover]
      abel
    -- the divisor on X
    set NX := (dT * b) • D - x₀ • D' - x₃ • D₃ - (α * c) • A with hNXdef
    have hT : dT • (cartierPullback p (b • D) - smoothCanonicalDivisor cT) - B =
        (cartierPullback p NX + (α • Amp + β • F)) + principalCartierDivisor T (φ ^ dT) := by
      rw [hBdef, hC₀, hC₃, hφ, hAmpdef, hNXdef, principalCartierDivisor_power]
      simp only [cartierPullback_sub, cartierPullback_nsmul]
      rw [← hdTsum]
      module
    -- its nefness
    have hnat : dT * b = x₀ * (r * a) + x₀ * (r * ba) + x₃ * (d₃ * b₃) + x₃ * (d₃ * bb) := by
      rw [← hdTsum]
      have e1 : x₀ * r * b = x₀ * (r * a) + x₀ * (r * ba) := by rw [hba]; ring
      have e2 : x₃ * d₃ * b = x₃ * (d₃ * b₃) + x₃ * (d₃ * bb) := by rw [hbb]; ring
      rw [add_mul, e1, e2]
      ring
    obtain ⟨w, hw⟩ : ∃ w, u * M = w + k₃ * d₃ * v * c := by
      refine ⟨u * M - k₃ * d₃ * v * c, ?_⟩
      have h1 : k₃ * d₃ * v * c ≤ u * M := by
        calc k₃ * d₃ * v * c ≤ k₃ * d₃ * (2 * u) * c := by gcongr
          _ = u * (2 * k₃ * d₃ * c) := by ring
          _ ≤ u * M := Nat.mul_le_mul_left u hMk
      omega
    have hx₃ : x₃ = r * (k₁ + 1) * (w + k₃ * d₃ * v * c) := by
      rw [hx₃def, hM'def, ← hw]
      ring
    have hαc : α * c = r * (k₁ + 1) * (d₃ * v * c) := by
      rw [hαdef, hβdef]
      ring
    have hNX : NX = x₀ • ((r * a) • D - D') + (x₀ * (r * ba)) • D + (x₃ * (d₃ * bb)) • D +
        (r * (k₁ + 1)) • (w • ((d₃ * b₃) • D - D₃) +
          (d₃ * v * c) • (k₃ • ((d₃ * b₃) • D - D₃) - A)) := by
      rw [hNXdef, hnat, hαc]
      conv_lhs => rw [hx₃]
      conv_rhs => rw [hx₃]
      module
    have hNXnef : CartierIsNef K NX := by
      rw [hNX]
      refine cartierIsNef_add (cartierIsNef_add (cartierIsNef_add
        (cartierIsNef_nsmul hnefa _) (cartierIsNef_nsmul hD _)) (cartierIsNef_nsmul hD _))
        (cartierIsNef_nsmul (cartierIsNef_add (cartierIsNef_nsmul
          (cartierIsAmpleProj_isNef hA₃) _) (cartierIsNef_nsmul hk₃nef _)) _)
    -- the ample part on T
    have hFamp : CartierIsAmpleProj K (α • Amp + β • F) := by
      have hsplit : α • Amp + β • F = β • ((k₁ • Amp - -F) + Amp) := by
        rw [hαdef, hβdef]
        module
      rw [hsplit]
      exact cartierIsAmpleProj_nsmul (proper_nef_add_ample_isAmpleProj K _ _ hk₁nef hAmp)
        (Nat.one_le_iff_ne_zero.mpr (by rw [hβdef]; positivity))
    rw [hT]
    exact cartierIsAmpleProj_add_principal (proper_nef_add_ample_isAmpleProj K _ _
      (cartierIsNef_cartierPullback_of_dominant p hNXnef) hFamp) _

end MixedFujita
