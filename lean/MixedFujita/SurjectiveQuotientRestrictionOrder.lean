/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateDivisorFormalMap
public import MixedFujita.CompletionJetApproximation
public import MixedFujita.TangentRestrictionMap

/-! 商環完備化同型を省く実局所全射の高次数持ち上げ。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable


/-- High order in an ACTUAL surjective local quotient lifts to the ambient
maximal-ideal power modulo the normal coordinate. Killing that coordinate in
completion then preserves the order. No target completion coordinates or
quotient-completion isomorphism are supplied. -/
theorem surjective_local_quotient_high_order_coordinate_restriction
    {R S K I : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [Field K] [CharZero K] [Finite I]
    (q : R →+* S) (hq : Function.Surjective q)
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* MvPowerSeries I K)
    (k : I) (normal : R)
    (he : e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) normal) = MvPowerSeries.X k)
    (hker : RingHom.ker q ≤ Ideal.span {normal})
    (a : R) (N : ℕ) (horder : (N : ℕ∞) ≤ localAdicOrder S (q a)) :
    (N : ℕ∞) ≤ (powerSeriesDivisorRestriction k
      (e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) a))).order := by
  classical
  let := Fintype.ofFinite I
  let φ : R →+* MvPowerSeries I K := e.toRingHom.comp (algebraMap R _)
  let δ := powerSeriesDivisorRestriction (K := K) k
  have hqmap : Ideal.map q (IsLocalRing.maximalIdeal R ^ N) = IsLocalRing.maximalIdeal S ^ N := by
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective q hq]
  have hqa : q a ∈ Ideal.map q (IsLocalRing.maximalIdeal R ^ N) := by
    rw [hqmap]
    exact (localAdicOrder_nat_le_iff _ _).mp horder
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective q hq).mp hqa
  have hsub : a - b ∈ RingHom.ker q := by
    change q (a - b) = 0
    rw [map_sub, hba, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hker hsub)
  have heq : δ (φ a) = δ (φ b) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← map_sub, ← hc, map_mul, map_mul]
    change δ (φ c) * δ (e (algebraMap R _ normal)) = 0
    rw [he, powerSeriesDivisorRestriction_X_self, mul_zero]
  have hbφ : (N : ℕ∞) ≤ (φ b).order := completionCoordinates_order_ge_of_mem_pow e hb
  change (N : ℕ∞) ≤ (δ (φ a)).order
  rw [heq]
  apply le_order_algHom_of_le_order δ ?_ N (φ b) hbφ
  intro i
  by_cases hi : i = k
  · subst i
    simp only [δ, powerSeriesDivisorRestriction_X_self, map_zero]
  · rw [show δ (MvPowerSeries.X i) = MvPowerSeries.X (⟨i, hi⟩ : {i : I // i ≠ k}) from
      powerSeriesDivisorRestriction_X k ⟨i, hi⟩]
    exact MvPowerSeries.constantCoeff_X _

end MixedFujita
