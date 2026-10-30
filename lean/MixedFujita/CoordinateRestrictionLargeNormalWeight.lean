/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateDivisorFormalMap

/-! 形式座標制限の高次数と大きい法線重み・原始化倍率。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable


/-- High order AFTER restriction to a coordinate divisor forces high weighted
AMBIENT order when the normal variable is assigned that order as weight.
Transverse ambient terms are allowed and may have low ordinary order. -/
theorem coordinate_restriction_order_le_large_normal_weightedOrder
    {S R : Type*} [Field R] (k : S) (F : MvPowerSeries S R) (N : ℕ)
    (h : (N : ℕ∞) ≤ (powerSeriesDivisorRestriction k F).order) :
    (N : ℕ∞) ≤ F.weightedOrder (fun i => if i = k then N else 1) := by
  classical
  let w : S → ℕ := fun i => if i = k then N else 1
  apply MvPowerSeries.nat_le_weightedOrder
  intro d hd
  have hdk : d k = 0 := by
    by_contra hn
    have hle := Finsupp.le_weight_of_ne_zero' w hn
    have he : w k = N := ite_eq_left rfl
    rw [he] at hle
    exact (not_le_of_gt hd) hle
  let e : {i : S // i ≠ k} ↪ S := Function.Embedding.subtype (· ≠ k)
  have hsupport : (d.support : Set S) ⊆ Set.range e := by
    intro i hi
    have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    exact ⟨⟨i, fun he => hdi (he ▸ hdk)⟩, rfl⟩
  let d' := d.comapDomain e e.injective.injOn
  have hemb : Finsupp.embDomain e d' = d := Finsupp.embDomain_comapDomain hsupport
  have hwdeg : Finsupp.weight w d = Finsupp.degree d := by
    rw [Finsupp.weight_apply, Finsupp.degree_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := fun he => (Finsupp.mem_support_iff.mp hi) (he ▸ hdk)
    simp only [w, ite_eq_right hik, smul_eq_mul, mul_one]
  have hdeg : Finsupp.degree d' = Finsupp.weight w d := by
    rw [hwdeg, ← hemb, Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  have hc : MvPowerSeries.coeff d' (powerSeriesDivisorRestriction k F) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    rw [hdeg]
    exact (show (Finsupp.weight w d : ℕ∞) < N by exact_mod_cast hd).trans_le h
  simp only [powerSeriesDivisorRestriction, MvPowerSeries.coeff_killCompl] at hc
  change MvPowerSeries.coeff (Finsupp.embDomain e d') F = 0 at hc
  rwa [hemb] at hc


/-- The large-normal-weight vector has the exact sum normalWeight + n-1. -/
theorem large_normal_weight_sum {n : ℕ} (k : Fin n) (N : ℕ) :
    (∑ i : Fin n, (if i = k then N + 1 else 1 : ℕ)) = n + N := by
  classical
  have he (i : Fin n) : (if i = k then N + 1 else 1 : ℕ) = 1 + if i = k then N else 0 := by
    by_cases h : i = k <;> simp [h, Nat.add_comm]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp


/-- If at least one tangent weight is 1, primitive normalization cannot scale
the actual toric extraction weights. -/
theorem large_normal_weight_primitive_normalization
    {n : ℕ} (k l : Fin n) (hl : l ≠ k) (N g : ℕ) (_hg : 1 ≤ g)
    (w' : Fin n → ℕ) (hw : ∀ i, (if i = k then N + 1 else 1 : ℕ) = g * w' i) :
    g = 1 ∧ w' = fun i => if i = k then N + 1 else 1 := by
  have hl' : 1 = g * w' l := by simpa only [ite_eq_right hl] using hw l
  have hg' : g = 1 := Nat.dvd_one.mp ⟨w' l, hl'⟩
  refine ⟨hg', ?_⟩
  funext i
  simpa only [hg', one_mul] using (hw i).symm

end MixedFujita
