/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompactifiedModelVanishing
public import MixedFujita.OpenImmersionModelRestriction

/-!
The roundup H¹ vanishing of the connectedness argument for a klt pair on the open model of a
compactification (step 15).

Let `T̄` be a smooth projective variety with an SNC family supporting a divisor `B̄` and an effective
`Ḡ`, such that `d K_{T̄} + B̄` is principal (`B̄` is the crepant boundary of a pair whose divisor is
principal: then `B̄ = ρ^* div u − d div(ρ^*ω)`), and `D̄` an effective nef and big divisor with
`c D̄ − Ḡ` nef. For `M m ≥ c + 1` the adjoint `dM (m D̄ − K) − (M B̄ + d Ḡ)` is `d (M m D̄ − Ḡ)` up to a
principal divisor, which is big and nef, so the signed roundup form of Kawamata–Viehweg vanishing
gives `H¹(T̄, 𝒪(m D̄ + Ē)) = 0` for `Ē = ⌈−(M B̄ + d Ḡ)/(dM)⌉` (`klt_compactified_twist_H1_vanishing`);
the canonical divisor has been absorbed by the crepant boundary. On the open model `T = T̄ ∖ D̄`,
for a principal `H` and the restrictions `B`, `G` of `B̄`, `Ḡ`, the roundup of the boundary
`dM H + M B + d G` of the connectedness argument has vanishing H¹
(`klt_open_model_roundup_H1_vanishing`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

section Compactified

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

/-- **Kawamata–Viehweg vanishing for the twists of the klt roundup.** On a smooth projective
variety, for divisors `B̄` and `Ḡ` supported on an SNC family with `d K + B̄` principal, the Cartier
divisor `Ē` with coefficients `⌈−(M b̄ + d ḡ)/(dM)⌉`, and an effective nef and big `D̄` with `c D̄ − Ḡ`
nef, the first cohomology of `𝒪(m D̄ + Ē)` vanishes as soon as `M m ≥ c + 1`. -/
theorem klt_compactified_twist_H1_vanishing (hKV : KawamataViehwegVanishingSNCProjective K n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ H : CartierDivisor T, CartierIsAmpleProj K H) (hn : 1 ≤ n)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B G E D : CartierDivisor T) (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hBsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient B (t : T) = 0)
    (hGsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient G (t : T) = 0)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((((M : ℤ) * cartierCoefficient B (t : T) + (d : ℤ) * cartierCoefficient G (t : T) : ℤ) :
        ℝ) / ((d * M : ℕ) : ℝ))⌉)
    (F : T.functionFieldˣ) (hF : d • smoothCanonicalDivisor cT + B = principalCartierDivisor T F)
    (hDnef : CartierIsNef K D) (hDbig : CartierIsBig K D) (c : ℕ)
    (hGnef : CartierIsNef K (c • D - G)) (m : ℕ) (hm : c + 1 ≤ M * m) :
    Subsingleton (Scheme.Modules.Cohomology (m • D + E).sheaf 1) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  obtain ⟨k, hk⟩ : ∃ k, M * m = 1 + k + c := ⟨M * m - 1 - c, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hdM : 1 ≤ (d' + 1) * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hBeq : B = principalCartierDivisor T F - (d' + 1) • smoothCanonicalDivisor cT :=
    eq_sub_of_add_eq' hF
  let N : CartierDivisor T := (d' • D + (d' + 1) • (k • D + (c • D - G))) +
    principalCartierDivisor T (F ^ M)⁻¹
  have hNeq : N = (d' • D + (d' + 1) • (k • D + (c • D - G))) - M • principalCartierDivisor T F := by
    simp only [N]
    rw [principalCartierDivisor_inv, principalCartierDivisor_power]
    abel
  have hadj : ((d' + 1) * M) • (m • D - smoothCanonicalDivisor cT) -
      (M • B + (d' + 1) • G) = D + N := by
    have hmul : ((d' + 1) * M) • (m • D) = (d' + 1) • ((1 + k + c) • D) := by
      rw [smul_smul, smul_smul, mul_assoc, hk]
    rw [hNeq, hBeq, smul_sub, hmul]
    module
  have hN : CartierIsNef K N := by
    refine (cartierIsNef_add_principal_iff _).mpr (cartierIsNef_add (cartierIsNef_nsmul hDnef _)
      (cartierIsNef_nsmul (cartierIsNef_add (cartierIsNef_nsmul hDnef _) hGnef) _))
  have hnef : CartierIsNef K (((d' + 1) * M) • (m • D - smoothCanonicalDivisor cT) -
      (M • B + (d' + 1) • G)) := by
    rw [hadj]
    exact cartierIsNef_add hDnef hN
  have hbig : CartierIsBig K (((d' + 1) * M) • (m • D - smoothCanonicalDivisor cT) -
      (M • B + (d' + 1) • G)) := by
    rw [hadj]
    exact proper_normal_cartierIsBig_add_of_isNef K n hdim hn hnormT D _ hDbig hN
  have hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (M • B + (d' + 1) • G) (t : T) = 0 := by
    intro t ht
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul, hBsupp t ht,
      hGsupp t ht]
    simp
  have hE' : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (M • B + (d' + 1) • G) (t : T) : ℝ) /
        (((d' + 1) * M : ℕ) : ℝ))⌉ := by
    intro t
    rw [hE t, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul]
  exact signed_snc_roundup_H1_vanishing_of_projective_KV K hKV hProj cT ξ hinj hξ hsnc
    (M • B + (d' + 1) • G) E (m • D) ((d' + 1) * M) hdM hsupp hE' hnef hbig

end Compactified

section OpenModel

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

theorem int_ceil_neg_mul_add_div_nat (N : ℕ) (hN : 1 ≤ N) (h g : ℤ) :
    ⌈-((((N : ℤ) * h + g : ℤ) : ℝ) / ((N : ℕ) : ℝ))⌉ = -h + ⌈-((g : ℝ) / ((N : ℕ) : ℝ))⌉ :=
  int_ceil_neg_mul_add_div N hN h g

/-- **The klt roundup H¹ vanishing on the open model of a compactification.** Let `T̄` be a smooth
projective variety with an SNC family supporting `B̄` and `Ḡ`, `d K_{T̄} + B̄` principal, `D̄` effective
nef and big with `c D̄ − Ḡ` nef, and `ι : T → T̄` an open immersion onto the locus where `1` is a
local equation of `D̄`. For a principal divisor `H` on `T` and `B = ι^* B̄`, `G = ι^* Ḡ`, every
Cartier divisor `C` on `T` with coefficients `⌈−(dM h + M b + d g)/(dM)⌉` has `H¹(T, 𝒪(C)) = 0`. -/
theorem klt_open_model_roundup_H1_vanishing (hKV : KawamataViehwegVanishingSNCProjective K n)
    (hn : 1 ≤ n) {Tb : Scheme.{u}} [IsIntegral Tb] [IsNoetherian Tb]
    [Tb.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K))]
    [IsProper (Tb ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Tb))]
    (hProj : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H)
    (cTb : EtaleChart K Tb n) {r : ℕ} (ξ : Fin r → Tb)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (Bb Gb Db : CartierDivisor Tb) (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hBsupp : ∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ →
      cartierCoefficient Bb (t : Tb) = 0)
    (hGsupp : ∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ →
      cartierCoefficient Gb (t : Tb) = 0)
    (F : Tb.functionFieldˣ) (hF : d • smoothCanonicalDivisor cTb + Bb = principalCartierDivisor Tb F)
    (hDeff : Db.IsEffective) (hDnef : CartierIsNef K Db) (hDbig : CartierIsBig K Db) (c : ℕ)
    (hGnef : CartierIsNef K (c • Db - Gb))
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ι : T ⟶ Tb) [IsOpenImmersion ι] [IsDominant ι]
    (hV : ∀ x : Tb, x ∈ ι.opensRange ↔ Db.IsLocalEquationAt x 1)
    (v : T.functionFieldˣ) (C : CartierDivisor T)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-(((((d * M : ℕ) : ℤ) * T.ord (v : T.functionField) (t : T) +
        ((M : ℤ) * cartierCoefficient (cartierPullback ι Bb) (t : T) +
          (d : ℤ) * cartierCoefficient (cartierPullback ι Gb) (t : T)) : ℤ) : ℝ) /
        ((d * M : ℕ) : ℝ))⌉) :
    Subsingleton (Scheme.Modules.Cohomology C.sheaf 1) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (Tb ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdM : 1 ≤ d * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the roundup on the compactification
  obtain ⟨F', -, -, hFc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  let a : Fin r → ℤ := fun i => ⌈-((((M : ℤ) * cartierCoefficient Bb (ξ i) +
    (d : ℤ) * cartierCoefficient Gb (ξ i) : ℤ) : ℝ) / ((d * M : ℕ) : ℝ))⌉
  let Eb : CartierDivisor Tb := ∑ i, a i • F' i
  have hEb : ∀ t : CodimensionOnePoint Tb, cartierCoefficient Eb (t : Tb) =
      ⌈-((((M : ℤ) * cartierCoefficient Bb (t : Tb) + (d : ℤ) * cartierCoefficient Gb (t : Tb) :
        ℤ) : ℝ) / ((d * M : ℕ) : ℝ))⌉ := by
    intro t
    rcases cartierCoefficient_member_combination ξ hinj F' hFc a t with ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci, hBsupp t hti, hGsupp t hti]
      norm_num
  have htw : ∀ m, c + 1 ≤ m → Subsingleton (Scheme.Modules.Cohomology (Eb + m • Db).sheaf 1) := by
    intro m hm
    have hmM : c + 1 ≤ M * m := le_trans hm (Nat.le_mul_of_pos_left m hM)
    have h := klt_compactified_twist_H1_vanishing K hKV hProj hn cTb ξ hinj hξ hsnc Bb Gb Eb Db
      d M hd hM hBsupp hGsupp hEb F hF hDnef hDbig c hGnef m hmM
    rwa [add_comm] at h
  have hvan := cartierPullback_H1_subsingleton_of_twists ι Eb Db hDeff hV (c + 1) htw
  -- the roundup on the open model is the restriction up to a principal divisor
  have hCeq : C = cartierPullback ι Eb + principalCartierDivisor T v⁻¹ := by
    apply cartierDivisor_eq_of_forall_coefficient_eq hnormT
    intro t
    have hcoh : Order.coheight (ι (t : T)) = 1 :=
      (coheight_eq_of_isOpenImmersion ι (t : T)).trans t.2
    rw [hC t, cartierCoefficient_add, principalCartierDivisor_inv, cartierCoefficient_neg,
      cartierCoefficient_principal,
      cartierCoefficient_cartierPullback_of_isOpenImmersion (K := K) (n := n) ι Eb t,
      hEb ⟨ι (t : T), hcoh⟩, cartierCoefficient_cartierPullback_of_isOpenImmersion (K := K) (n := n) ι Bb t,
      cartierCoefficient_cartierPullback_of_isOpenImmersion (K := K) (n := n) ι Gb t,
      int_ceil_neg_mul_add_div_nat (d * M) hdM]
    ring
  rw [hCeq]
  let e := cartierSheafPrincipalShiftIso (cartierPullback ι Eb) v⁻¹
  let : Subsingleton ((Sheaf.functorH.{u} _ 1).obj ((SheafOfModules.toSheaf T.ringCatSheaf).obj
      (cartierPullback ι Eb).sheaf)) := hvan
  exact ((Sheaf.functorH.{u} _ 1).mapIso
    ((SheafOfModules.toSheaf T.ringCatSheaf).mapIso e)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end OpenModel

end MixedFujita
