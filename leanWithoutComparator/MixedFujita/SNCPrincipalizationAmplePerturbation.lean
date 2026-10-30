/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCPrincipalizationSupportedDescent
public import MixedFujita.ProjectiveKawamataViehwegOfAmple
public import MixedFujita.SmoothSNCAmpleHigherVanishing

/-! Supported relative ample corrections for the actual BMO₁ sequence,
and a uniform small-perturbation lemma in every positive cohomological degree.
The final ample identity for a nef-and-big divisor is still a separate step. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData
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

/-- A nowhere-zero ideal on an integral scheme misses the generic point. -/
theorem nonzeroIdeal_genericPoint_notMem_support
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData) (hI : IsNonzeroEverywhere I) :
    genericPoint X ∉ I.support := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have htop : I.stalkIdeal (genericPoint X) = ⊤ :=
    (Ideal.eq_bot_or_top _).resolve_left (hI _)
  intro h
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal I _).mp h
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- For any chosen ample divisor downstairs, the concrete principalization
has an effective correction supported on its total boundary making the
pullback of a positive multiple ample. This supplies the relative ample term
used in the nef-and-big perturbation argument. -/
theorem snc_principalization_exists_supported_ample_correction
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (T : AlgebraicGeometry.Triple k)
    [IsIntegral T.X.left] [IsProper (T.X.left ↘ Spec (.of k))]
    [IsIntegral (sncMarkedPrincipalizationSequence T).last]
    [(sncMarkedPrincipalizationSequence T).last.Over (Spec (.of k))]
    [(sncMarkedPrincipalizationSequence T).composite.IsOver (Spec (.of k))]
    [IsDominant (sncMarkedPrincipalizationSequence T).composite]
    [IsNoetherian (sncMarkedPrincipalizationSequence T).last]
    (H : CartierDivisor T.X.left) (hH : CartierIsAmpleProj k H) :
    let S := sncMarkedPrincipalizationSequence T
    ∃ (c : ℕ) (G : CartierDivisor S.last), 1 ≤ c ∧ G.IsEffective ∧
      (∀ t : S.last, t ∉ (S.totalTransformSeq T.E (Fin.last _)).support →
        cartierCoefficient G t = 0) ∧
      CartierIsAmpleProj k (cartierPullback S.composite (c • H) - G) := by
  let S := sncMarkedPrincipalizationSequence T
  let : IsIntegral S.last := inferInstanceAs (IsIntegral (sncMarkedPrincipalizationSequence T).last)
  let : S.last.Over (Spec (.of k)) := inferInstanceAs
    ((sncMarkedPrincipalizationSequence T).last.Over (Spec (.of k)))
  let : IsDominant S.composite := inferInstanceAs
    (IsDominant (sncMarkedPrincipalizationSequence T).composite)
  let : S.composite.IsOver (Spec (.of k)) := inferInstanceAs
    ((sncMarkedPrincipalizationSequence T).composite.IsOver (Spec (.of k)))
  let : IsNoetherian S.last := inferInstanceAs
    (IsNoetherian (sncMarkedPrincipalizationSequence T).last)
  let : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  let : IsProper S.composite := S.isProper_composite
  let : IsProper (S.last ↘ Spec (.of k)) := by
    rw [← HomIsOver.comp_over (f := S.composite)]
    infer_instance
  obtain ⟨_, _, N, e, he, hbase, _⟩ := id hH
  let := he
  have hc := (sncMarkedPrincipalizationSequence_geometric_control T).2.1
  obtain ⟨H₀, c, G, hH₀, hcpos, hG, hG0, hamp⟩ :=
    blowUpSequence_exists_relative_ample e hbase S T.I.support
      (nonzeroIdeal_genericPoint_notMem_support T.I T.isNonzeroEverywhere) hc
  obtain ⟨a, ha, hnef⟩ := exists_nsmul_sub_isNef hH H₀
  refine ⟨c * a, G,
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hG, ?_, ?_⟩
  · intro t ht
    apply hG0
    intro hi
    exact ht (sncMarkedPrincipalizationSequence_support_le_total_boundary T
      ((mem_support_comap_iff_apply T.I S.composite t).mpr hi))
  · have hid : cartierPullback S.composite ((c * a) • H) - G =
        c • cartierPullback S.composite (a • H - H₀) +
          (cartierPullback S.composite (c • H₀) - G) := by
      rw [cartierPullback_sub, cartierPullback_nsmul, cartierPullback_nsmul,
        cartierPullback_nsmul, mul_smul]
      module
    rw [hid]
    exact proper_nef_add_ample_isAmpleProj k _ _
      (cartierIsNef_nsmul (cartierIsNef_cartierPullback_of_dominant S.composite hnef) c) hamp

/-- A single finite coefficient bound makes every sufficiently small effective
SNC perturbation preserve the same roundup. Whenever the perturbed adjoint is
ample, characteristic-zero vanishing then holds in every positive degree. -/
theorem snc_effective_perturbation_roundup_higher_vanishing
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.Over (Spec (.of k))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (cX : EtaleChart k X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily k n ξ)
    (B E Q J : CartierDivisor X) (d : ℕ) (hd : 1 ≤ d) (hJ : J.IsEffective)
    (hBsup : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient B t = 0)
    (hJsup : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ → cartierCoefficient J t = 0)
    (hE : ∀ t : CodimensionOnePoint X, cartierCoefficient E t =
      ⌈-((cartierCoefficient B t : ℝ) / (d : ℝ))⌉) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
      (∀ t : CodimensionOnePoint X, cartierCoefficient E t =
        ⌈-((cartierCoefficient (s • B + J) t : ℝ) / ((d * s : ℕ) : ℝ))⌉) ∧
      (CartierIsAmpleProj k ((d * s) • (Q - smoothCanonicalDivisor cX) - (s • B + J)) →
        ∀ j : ℕ, 1 ≤ j → Subsingleton (Scheme.Modules.Cohomology (Q + E).sheaf j)) := by
  let M : ℕ := ∑ i, (cartierCoefficient J (ξ i)).toNat
  refine ⟨M + 1, by omega, fun s hs => ?_⟩
  have hspos : 1 ≤ s := by omega
  have hlt : ∀ t : CodimensionOnePoint X, cartierCoefficient J t < (s : ℤ) := by
    intro t
    by_cases ht : (t : X) ∈ Set.range ξ
    · obtain ⟨i, hi⟩ := ht
      have hsum : (cartierCoefficient J (ξ i)).toNat ≤ M :=
        Finset.single_le_sum (f := fun i => (cartierCoefficient J (ξ i)).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hval := Int.self_le_toNat (cartierCoefficient J (ξ i))
      rw [← hi]
      omega
    · rw [hJsup t ht]
      exact_mod_cast (show 0 < s by omega)
  have hround : ∀ t : CodimensionOnePoint X, cartierCoefficient E t =
      ⌈-((cartierCoefficient (s • B + J) t : ℝ) / ((d * s : ℕ) : ℝ))⌉ := by
    intro t
    rw [cartierCoefficient_add, cartierCoefficient_nsmul,
      ceil_neg_div_perturb _ _ d s hd hspos (cartierCoefficient_nonneg_of_isEffective J hJ t)
        (hlt t)]
    exact hE t
  refine ⟨hround, fun hamp j hj => ?_⟩
  apply signed_snc_roundup_higher_vanishing_of_charZero k cX ξ hinj hξ hsnc
    (s • B + J) E Q (d * s)
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ?_ hround hamp j hj
  intro t ht
  rw [cartierCoefficient_add, cartierCoefficient_nsmul, hBsup t ht, hJsup t ht]
  simp

end MixedFujita
