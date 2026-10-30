/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteLCThresholdArithmetic

/-! klt基準係数との混合で旧臨界成分だけを残す固定有理閾値。 See reports/check-267-klt-anchor-center-isolation.json for the verified scope. A fixed rational perturbation ratio and all-large mixing with an actual klt anchor retain only OLD positive-perturbation critical components and preserve ORIGINAL L ample adjoints. On a SUPPLIED actual shared proper SNC model with a SUPPLIED actual effective source perturbation and critical-placement/positivity inputs, the entire ORIGINAL nonKlt locus equals the chosen minimal lc center. The exact reduced center ideal is internally identified, and EXPLICIT usual H1 KV yields original Cartier and all-large ORIGINAL mL restriction lifting. Constructing the isolation perturbation/model/placement/positivity and numerical-zero center nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable


/-- A klt anchor mixed with a large multiple of an lc coefficient family has
an exact positive rational perturbation whose NEW critical indices are ONLY
old critical indices with positive perturbation. The ratio is fixed before
the large mixing coefficient, permitting independent ampleness control. -/
theorem finite_lc_klt_anchor_isolating_coefficients
    {r : ℕ} (b c g : Fin r → ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : ∀ i, b i ≤ (d : ℤ)) (hc : ∀ i, c i < (d : ℤ))
    (hg : ∀ i, 0 ≤ g i) (hpos : ∃ i, b i = (d : ℤ) ∧ 0 < g i) :
    ∃ p q N₀ : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ ∃ i₀ : Fin r,
      b i₀ = (d : ℤ) ∧ 0 < g i₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        (∀ i, (q : ℤ) * ((N : ℤ) * b i + c i) + (p : ℤ) * g i ≤ ((q * (N + 1) * d : ℕ) : ℤ)) ∧
        (q : ℤ) * ((N : ℤ) * b i₀ + c i₀) + (p : ℤ) * g i₀ = ((q * (N + 1) * d : ℕ) : ℤ) ∧
        ∀ i, (q : ℤ) * ((N : ℤ) * b i + c i) + (p : ℤ) * g i = ((q * (N + 1) * d : ℕ) : ℤ) →
          b i = (d : ℤ) ∧ 0 < g i := by
  classical
  let I := {i : Fin r // b i = (d : ℤ)}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hposI : ∃ j, 0 < g (e j).val := by
    obtain ⟨i, hi, hgi⟩ := hpos
    exact ⟨e.symm ⟨i, hi⟩, by simpa only [e.apply_symm_apply] using hgi⟩
  obtain ⟨a, q, j₀, ha, hq, hgj₀, _, _, heq, htest⟩ :=
    finite_integer_lc_coefficients_exact_threshold (fun j => c (e j).val) (fun j => g (e j).val)
      d hd (fun j => (hc _).le) (fun j => hg _) (by intro j hj; have := hc (e j).val; omega) hposI
  let p := d * a
  have hp : 1 ≤ p := Nat.mul_pos (by omega) (by omega)
  have hcrit (i : Fin r) (hi : b i = (d : ℤ)) :
      (q : ℤ) * c i + (p : ℤ) * g i ≤ (q : ℤ) * d := by
    have hh := (htest a q hq).mpr le_rfl (e.symm ⟨i, hi⟩)
    simpa only [e.apply_symm_apply, Nat.cast_mul, p] using hh
  let N₀ := Finset.univ.sup fun i : Fin r => ((p : ℤ) * g i).toNat
  refine ⟨p, q, N₀, hp, hq, (e j₀).val, (e j₀).property, hgj₀, fun N hN => ?_⟩
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
  have hNnonneg : (0 : ℤ) ≤ N := by omega
  have hstrict (i : Fin r) (hi : b i < (d : ℤ)) :
      (q : ℤ) * ((N : ℤ) * b i + c i) + (p : ℤ) * g i < ((q * (N + 1) * d : ℕ) : ℤ) := by
    have hni : ((p : ℤ) * g i).toNat ≤ N := (Finset.le_sup (f := fun i => ((p : ℤ) * g i).toNat)
      (Finset.mem_univ i)).trans hN
    have hpgN : (p : ℤ) * g i ≤ N := by omega
    have hgap : (1 : ℤ) ≤ (d : ℤ) - b i := by omega
    have hqN : (N : ℤ) ≤ (q : ℤ) * N := by nlinarith
    have hmul : (q : ℤ) * N ≤ (q : ℤ) * N * ((d : ℤ) - b i) :=
      le_mul_of_one_le_right (mul_nonneg hqpos.le hNnonneg) hgap
    have hanchor := mul_lt_mul_of_pos_left (hc i) hqpos
    push_cast
    nlinarith [hpgN.trans (hqN.trans hmul)]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : b i = (d : ℤ)
    · have hh := hcrit i hi
      push_cast
      rw [hi]
      nlinarith
    · exact (hstrict i (lt_of_le_of_ne (hb i) hi)).le
  · have hj := (e j₀).property
    dsimp only [p]
    push_cast
    rw [hj]
    push_cast at heq
    nlinarith
  · intro i hi
    have hbcrit : b i = (d : ℤ) := by
      by_contra hne
      exact (ne_of_lt (hstrict i (lt_of_le_of_ne (hb i) hne))) hi
    refine ⟨hbcrit, ?_⟩
    by_contra hnpos
    have hgzero : g i = 0 := by have := hg i; omega
    have hanchor := mul_lt_mul_of_pos_left (hc i) hqpos
    rw [hbcrit, hgzero, mul_zero, add_zero] at hi
    push_cast at hi
    nlinarith

end MixedFujita
