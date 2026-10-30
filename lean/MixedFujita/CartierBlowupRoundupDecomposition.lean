/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.BlowupRoundupCoefficient
public import MixedFujita.NormalCartierCoefficientExt

/-! Exact Cartier roundup decomposition from total-transform identities and
distinct prime-component data. The supplied geometric identities are explicit;
the rounded divisor equality and the exceptional coefficient are outputs. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

theorem totalTransform_sum_decomposition {M : Type*} [AddCommGroup M]
    {m : ℕ} (s : Finset (Fin m)) (F G : Fin m → M) (E : M)
    (hFG : ∀ i, F i = G i + if i ∈ s then E else 0) (a : Fin m → ℤ) :
    ∑ i, a i • F i = (∑ i, a i • G i) + (∑ i ∈ s, a i) • E := by
  classical
  simp_rw [hFG, smul_add]
  rw [Finset.sum_add_distrib, Finset.sum_smul]
  congr 1
  simp [smul_ite, Finset.sum_ite_mem]

theorem roundup_totalTransform_decomposition {M : Type*} [AddCommGroup M]
    {m : ℕ} (s : Finset (Fin m)) (F G : Fin m → M) (E : M)
    (hFG : ∀ i, F i = G i + if i ∈ s then E else 0)
    (b : Fin m → ℤ) (d r : ℕ) :
    (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
        ⌈-((((∑ i ∈ s, b i) - (d : ℤ) * r : ℤ) : ℝ) / (d : ℝ))⌉ • E =
      (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • F i) + blowupRoundupCorrection s b d r • E := by
  rw [totalTransform_sum_decomposition s F G E hFG]
  dsimp only [blowupRoundupCorrection]
  rw [sub_smul]
  abel

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]

theorem cartier_roundup_disjoint_prime_combination
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    {m : ℕ} (ξ : Fin m → T) (hinj : Function.Injective ξ)
    (G : Fin m → CartierDivisor T)
    (hG : ∀ (i : Fin m) (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : T) (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = if (t : T) = η then 1 else 0)
    (hη : ∀ i, ξ i ≠ η) (b : Fin m → ℤ) (e : ℤ) (d : ℕ)
    (C : CartierDivisor T)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-((cartierCoefficient ((∑ i, b i • G i) + e • E) (t : T) : ℝ) / (d : ℝ))⌉) :
    C = (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) + ⌈-((e : ℝ) / (d : ℝ))⌉ • E := by
  classical
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm
  intro t
  rw [hC t]
  by_cases ht : (t : T) = η
  · have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hη i (hi.symm.trans ht)
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul, hG, hE]
    simp only [ite_eq_right (hg _), ite_eq_left ht, mul_zero, Finset.sum_const_zero, zero_add, mul_one]
  · by_cases hz : (t : T) ∈ Set.range ξ
    · obtain ⟨i, hi⟩ := hz
      have hg : ∀ a : Fin m → ℤ, cartierCoefficient (∑ j, a j • G j) (t : T) = a i := by
        intro a
        simp only [cartierCoefficient_sum, cartierCoefficient_zsmul, hG]
        simp [← hi, hinj.eq_iff]
      simp [cartierCoefficient_add, cartierCoefficient_zsmul, hg, hE, ht]
    · have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hz ⟨i, hi.symm⟩
      simp [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul, hG, hE, ht, hg]

theorem cartier_roundup_totalTransform_eq
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    {m : ℕ} (ξ : Fin m → T) (hinj : Function.Injective ξ)
    (G F : Fin m → CartierDivisor T)
    (hG : ∀ (i : Fin m) (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : T) (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = if (t : T) = η then 1 else 0)
    (hη : ∀ i, ξ i ≠ η) (s : Finset (Fin m))
    (hFG : ∀ i, F i = G i + if i ∈ s then E else 0)
    (b : Fin m → ℤ) (d r : ℕ) (C : CartierDivisor T)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-((cartierCoefficient ((∑ i, b i • F i) - ((d : ℤ) * r) • E) (t : T) : ℝ) / (d : ℝ))⌉) :
    C = (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • F i) + blowupRoundupCorrection s b d r • E := by
  have hb : (∑ i, b i • F i) - ((d : ℤ) * r) • E =
      (∑ i, b i • G i) + ((∑ i ∈ s, b i) - (d : ℤ) * r) • E := by
    rw [totalTransform_sum_decomposition s F G E hFG, sub_smul]
    abel
  have hc := cartier_roundup_disjoint_prime_combination hnorm ξ hinj G hG η E hE hη b
    ((∑ i ∈ s, b i) - (d : ℤ) * r) d C (by intro t; simpa only [hb] using hC t)
  exact hc.trans (roundup_totalTransform_decomposition s F G E hFG b d r)

end MixedFujita
