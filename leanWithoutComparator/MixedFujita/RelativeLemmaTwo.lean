/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltWeightDiscrepancyInterval
public import MixedFujita.KltGlobalMinimizer
public import MixedFujita.RelativeAttainment
public import MixedFujita.SteinCartierSections
public import MixedFujita.CartierSectionPullbackAvoidance

/-!
Lemma 2 and the bounds of section 3.1 over a fibre (step 17R-2).

Let (X, B) be a projective klt pair, f : X → Y a contraction and J an ample divisor of the base.
The sections of j f*J are the pullbacks of the sections of j J (Stein), so the profile data over
the fibre of y of the sections of j f*J satisfy the bounds of section 3.1:

* Lemma 2 needs only a section of a f*J nonvanishing at the point of the datum: the pullback of a
  section of the globally generated a J nonvanishing at y. Lemma 1 and the product estimate are
  those of the pair on X for the divisor f*J and an ample divisor H of X
  (`klt_prime_coefficient_le_of_product_of_ample`, `klt_weightExponentialObjective_ge_of_ample`),
  and the fraction of sections of q J among those of j J is the one on the base
  (`rel_klt_sncWeightProfiles_exponential_bound`);
* both ends of the discrepancy window (`rel_klt_sncWeightProfiles_bounds`) and the positive lower
  bound of the normalized infimum over the fibre (`rel_klt_normalizedInfimum_ge`);
* with the attainment over the fibre (`rel_exists_basis_sncWeightProfile_minimizer`), a global
  minimizer over the fibre with the same gap as the infimum
  (`rel_klt_global_minimizer_of_infimum_gap`).
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

section Product

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- Lemma 2 at actual test primes for an arbitrary divisor A of a projective klt pair: the
constant is multiplied by q, the degree of the second factor. -/
theorem klt_prime_coefficient_le_of_product_of_ample (hn : 1 ≤ n)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : X) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
        [U.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
        (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
        (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
        (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
        x ∈ closure ({σ (e : U)} : Set X) →
        ∀ s ∈ LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀), ∀ hs : s ≠ 0,
          (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor ((a + q) • A) s hs))
            (e : U) : ℝ) ≤ ((C * q : ℕ) : ℝ) *
              (((d : ℝ) + cartierCoefficient
                (logDiscrepancyDivisor n σ hσ cX fX d D₀ cU etaleCharts_cover) (e : U)) / d) := by
  obtain ⟨C, hC, hc⟩ := klt_model_coefficient_le hn cX fX d hd D₀ A hklt hH
  refine ⟨C, hC, fun x a q hq σ₀ hx U _ _ _ _ σ _ _ hσ cU e hcl s hsU hs => ?_⟩
  obtain ⟨t, rfl⟩ := hsU
  have ht : t ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) e
  have hσ₀ : σ (e : U) ∈ cartierSectionNonvanishingOpen (a • A) σ₀ :=
    (specializes_iff_mem_closure.mpr hcl).mem_open
      (cartierSectionNonvanishingOpen (a • A) σ₀).isOpen hx
  have heq := cartierPullback_nsmulProduct_coefficient_eq σ A a q σ₀ t ht hs e hσ₀
  apply (congrArg (fun z : ℤ => (z : ℝ)) heq).le.trans
  simpa only [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg,
    Int.cast_neg, sub_neg_eq_add, Nat.cast_mul] using (hc U σ hσ cU e q hq t ht).2

/-- The klt form of (8) before choosing q, for an arbitrary divisor A of a projective klt pair:
the objective is at least h⁰(q A) exp(A(w) (1/t − C q/j)). -/
theorem klt_weightExponentialObjective_ge_of_ample (hn : 1 ≤ n)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : X) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
        [T.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
        (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
        (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
        (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T),
        Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K n ξ →
        (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
          cartierCoefficient (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover)
            (z : T) = 0) →
        ∀ {N : ℕ} (B : Module.Basis (Fin N) K Γ(((a + q) • A).sheaf, ⊤)),
        (∀ i, ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (z : T) = 0) →
        ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
        (∃ p ∈ π ⁻¹' ({x} : Set X), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set T)) →
        ∀ {t j : ℝ}, 0 < j →
          (Module.finrank K Γ((q • A).sheaf, ⊤) : ℝ) *
            Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)) *
              (1 / t - ((C * q : ℕ) : ℝ) / j)) ≤
            weightExponentialObjective
              (fun k => ((d : ℝ) - cartierCoefficient
                (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)
              (fun i k => (cartierCoefficient (cartierPullback π
                (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (ξ k) : ℝ))
              t j w := by
  obtain ⟨C, hC, hc⟩ := klt_prime_coefficient_le_of_product_of_ample hn cX fX d hd D₀ A hklt hH
  refine ⟨C, hC, fun x a q hq σ₀ hx T _ _ _ _ π _ _ hπ cT r ξ hinj hξ hsnc hBsupp N B hGsupp
    w hw0 hwΦ t j hj => ?_⟩
  have hσ₀0 : σ₀ ≠ 0 := by
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen (a • A) 0 x).mp hx
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  have hrank : Module.finrank K (LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀)) =
      Module.finrank K Γ((q • A).sheaf, ⊤) :=
    LinearMap.finrank_range_of_inj (cartierNsmulProduct_injective A a q σ₀ hσ₀0)
  rw [← hrank]
  exact weightExponentialObjective_ge_of_low_subspace π hπ cX fX d hd D₀ cT ξ hinj hξ hsnc
    hBsupp ((a + q) • A) B hGsupp x
    (LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀))
    (fun U _ _ _ _ σ _ _ hσ cU e hcl s hsU hs => hc x a q hq σ₀ hx U σ hσ cU e hcl s hsU hs)
    w hw0 hwΦ hj

end Product

section Fibre

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The klt form of (8) over a fibre, for the profile data of the sections of j f*J. -/
theorem rel_klt_sncWeightProfiles_exponential_bound (hn : 1 ≤ n) (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ}
    (hdimY : topologicalKrullDim Y = k) (hk : 1 ≤ k) {J : CartierDivisor Y}
    (hJ : CartierIsAmpleProj K J) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (y : Y) {N : ℕ}
      (B : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤)) p,
      p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B →
      ∀ {t : ℝ}, 0 < t → t ≤ b →
        κ * (N : ℝ) * Real.exp (p.1 / (2 * t)) ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
  obtain ⟨C, hC, hc⟩ := klt_weightExponentialObjective_ge_of_ample hn cX fX d hd D₀
    (cartierPullback f J) hklt hH
  obtain ⟨κ, hκ, hκ1, hfrac⟩ := cartierIsAmpleProj_exists_section_fraction hdimY hk hJ hC hb
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hfrac] with j hj
  obtain ⟨a, q, rfl, hq, hcq, hGG, hdimq⟩ := hj
  intro y N B p hp t ht htb
  obtain ⟨x, hxy, hp⟩ := hp
  obtain ⟨hs, T, hTi, hTN, hTo, hTs, π, hπd, hπo, hπp, hπ, cT, r, ξ, w, hinj, hξ, hsnc,
    hBsupp, hGsupp, hw0, hwΦ, hAw, hv⟩ := hp
  -- a section of a J nonvanishing at y, pulled back to a section of a f*J nonvanishing at x
  obtain ⟨τ₀, hτ₀unit⟩ := hGG y
  have hτ₀ : y ∈ cartierSectionNonvanishingOpen (a • J) τ₀ :=
    (mem_cartierSectionNonvanishingOpen _ _ y).mpr ⟨_, _, hτ₀unit⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Γ((a • cartierPullback f J).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • cartierPullback f J) σ₀ := by
    rw [← cartierPullback_nsmul]
    refine ⟨cartierDominantPullbackSection f (a • J) τ₀,
      (cartierDominantPullbackSection_nonvanishing_iff f (a • J) τ₀ x).mpr ?_⟩
    rw [hxy]
    exact hτ₀
  have hjpos : (0 : ℝ) < ((a + q : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < a + q by omega)
  have hmain := hc x a q hq σ₀ hσ₀ T π hπ cT ξ hinj hξ hsnc hBsupp B hGsupp
    w hw0 hwΦ (t := t) hjpos
  let Aw : ℝ := ∑ k, w k * (((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)
  have hAw0 : 0 ≤ Aw := by
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (div_nonneg ?_ (Nat.cast_nonneg d))
    have h := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cX fX d D₀ hklt cT ⟨ξ k, hξ k⟩
    have h' : (cartierCoefficient (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover)
      (ξ k) : ℝ) < d := by exact_mod_cast h
    linarith
  -- the dimensions of the sections are those on the base
  have hNeq : Module.finrank K Γ(((a + q) • cartierPullback f J).sheaf, ⊤) = N := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have hqX : Module.finrank K Γ((q • cartierPullback f J).sheaf, ⊤) =
      Module.finrank K Γ((q • J).sheaf, ⊤) :=
    stein_finrank_sections_nsmul_cartierPullback f happ K J q
  have hjX : Module.finrank K Γ(((a + q) • cartierPullback f J).sheaf, ⊤) =
      Module.finrank K Γ(((a + q) • J).sheaf, ⊤) :=
    stein_finrank_sections_nsmul_cartierPullback f happ K J (a + q)
  rw [← hjX, hNeq, ← hqX] at hdimq
  have hcqt : ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) ≤ 1 / (2 * t) :=
    hcq.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hexp : Real.exp (Aw / (2 * t)) ≤
      Real.exp (Aw * (1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hhalf : 1 / t - 1 / (2 * t) = 1 / (2 * t) := by field_simp; ring
    have hle : 1 / (2 * t) ≤ 1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) := by linarith
    calc Aw / (2 * t) = Aw * (1 / (2 * t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hAw0
  have hobj : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX d D₀ cT etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor ((a + q) • cartierPullback f J) (B i) (B.ne_zero i))) (ξ k) :
          ℝ)) t ((a + q : ℕ) : ℝ) w =
      ∑ i, Real.exp (p.1 / t - p.2 i / ((a + q : ℕ) : ℝ)) := by
    unfold weightExponentialObjective
    rw [hAw]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  have hpA : p.1 = Aw := hAw
  calc κ * (N : ℝ) * Real.exp (p.1 / (2 * t)) = κ * (N : ℝ) * Real.exp (Aw / (2 * t)) := by
        rw [hpA]
    _ ≤ (Module.finrank K Γ((q • cartierPullback f J).sheaf, ⊤) : ℝ) *
        Real.exp (Aw * (1 / t - ((C * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) :=
      mul_le_mul hdimq hexp (Real.exp_pos _).le (Nat.cast_nonneg _)
    _ ≤ _ := hmain
    _ = _ := hobj

/-- Both ends of the klt discrepancy window and all value bounds over a fibre. -/
theorem rel_klt_sncWeightProfiles_bounds (hn : 1 ≤ n) (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ}
    (hdimY : topologicalKrullDim Y = k) (hk : 1 ≤ k) {J : CartierDivisor Y}
    (hJ : CartierIsAmpleProj K J) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ C : ℕ, 1 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
      ∀ (y : Y) {N : ℕ}, 0 < N →
      ∀ (B : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤)) p,
        p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B →
        ∀ {t δ : ℝ}, 0 < t → t ≤ b → 0 ≤ δ →
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) →
          -Real.log (1 - δ) / C ≤ p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) ∧
            ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (C : ℝ) * j * p.1 := by
  obtain ⟨κ, hκ, hκ1, hev⟩ := rel_klt_sncWeightProfiles_exponential_bound hn cX fX d hd D₀ hklt
    hH f happ hdimY hk hJ hb
  obtain ⟨C, hC, hc⟩ := klt_sncWeightProfiles_lower_bounds hn cX fX d hd D₀ (cartierPullback f J)
    hklt hH
  refine ⟨κ, hκ, hκ1, C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro y N hN B p hp t δ ht htb hδ hF
  obtain ⟨x, hxy, hpx⟩ := hp
  have hlow := hc j hj1 x hN B p hpx ht hF
  refine ⟨hlow.1, ?_, hlow.2⟩
  exact weight_logDiscrepancy_le_of_exp_bound hκ hκ1 (by exact_mod_cast hN) ht htb hδ
    (hj y B p ⟨x, hxy, hpx⟩ ht htb) hF

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] [IsAlgClosed K] in
/-- Over a point of the image, the objective N of the zero datum is an objective value over the
fibre. -/
theorem relWeightObjectiveValues_natCast_mem [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor X)
    (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y) {N : ℕ}
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (t j : ℝ) :
    (N : ℝ) ∈ relWeightObjectiveValues cX fX d D₀ D f y N t j := by
  obtain ⟨B', p, hp, hval⟩ := sncWeightObjectiveValues_natCast_mem cX fX d D₀ D x B t j
  exact ⟨B', p, ⟨x, hxy, hp⟩, hval⟩

/-- The normalized infimum over a fibre is uniformly bounded below by a positive constant for large
degrees. -/
theorem rel_klt_normalizedInfimum_ge (hn : 1 ≤ n) (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ}
    (hdimY : topologicalKrullDim Y = k) (hk : 1 ≤ k) {J : CartierDivisor Y}
    (hJ : CartierIsAmpleProj K J) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (x : X) {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤), ∀ {t : ℝ}, 0 < t →
        t ≤ b → κ ≤ relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f (f x) N t j / N := by
  obtain ⟨κ, hκ, hκ1, hev⟩ := rel_klt_sncWeightProfiles_exponential_bound hn cX fX d hd D₀ hklt
    hH f happ hdimY hk hJ hb
  have := cartierIsAmpleProj_isProper_base H hH
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hev] with j hj
  intro x N hN B₀ t ht htb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr]
  apply le_relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f (f x) N t j
    ⟨N, relWeightObjectiveValues_natCast_mem cX fX d D₀ _ f rfl B₀ t j⟩
  intro B p hp
  have hstrong := hj (f x) B p hp ht htb
  have hApos := (relWeightProfiles_fst_nonneg cX fX hd D₀ _ hklt f (f x) B hp).1
  have h1 : (1 : ℝ) ≤ Real.exp (p.1 / (2 * t)) := Real.one_le_exp (div_nonneg hApos (by positivity))
  calc κ * (N : ℝ) = κ * (N : ℝ) * 1 := by ring
    _ ≤ κ * (N : ℝ) * Real.exp (p.1 / (2 * t)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hκ.le hNr.le)
    _ ≤ _ := hstrong

/-- An infimum gap over the fibre of a closed point gives an actual global minimizer over the
fibre with the same gap, uniformly in t and in the closed points of the base. -/
theorem rel_klt_global_minimizer_of_infimum_gap (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (D₀ : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D₀)
    (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ}
    (hdimY : topologicalKrullDim Y = k) (hk : 1 ≤ k) {J : CartierDivisor Y}
    (hJ : CartierIsAmpleProj K J) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ j : ℕ in atTop, ∀ (y : Y), IsClosed ({y} : Set Y) → ∀ {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤), ∀ {t δ : ℝ},
        0 < t → t ≤ b → 0 < δ →
        (relWeightObjectiveValues cX fX d D₀ (j • cartierPullback f J) f y N t j).Nonempty →
        relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y N t j ≤ (N : ℝ) * (1 - δ) →
        ∃ B : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤),
          ∃ p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
            (∀ B' : Module.Basis (Fin N) K Γ((j • cartierPullback f J).sheaf, ⊤),
              ∀ p' ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B',
                (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
                  ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) := by
  obtain ⟨κ, hκ, hκ1, C, hC, hev⟩ := rel_klt_sncWeightProfiles_bounds hn cX fX d hd D₀ hklt hH
    f happ hdimY hk hJ hb
  have := cartierIsAmpleProj_isProper_base H hH
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro y hyc N hN B₀ t δ ht htb hδ hne hgap
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  -- a datum strictly below N
  have hinf : relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y N t j < N :=
    hgap.trans_lt (by nlinarith)
  obtain ⟨val, ⟨B₁, p₁, hp₁, rfl⟩, hval⟩ := exists_lt_of_csInf_lt hne hinf
  set S : ℝ := ∑ i, Real.exp (p₁.1 / t - p₁.2 i / j) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  set δ₁ : ℝ := (1 - S / N) / 2 with hδ₁def
  have hδ₁ : 0 < δ₁ := half_pos (sub_pos.mpr ((div_lt_one hNpos).mpr hval))
  have hδ₁1 : δ₁ < 1 := by
    have h : 0 ≤ S / (N : ℝ) := div_nonneg hS hNpos.le
    rw [hδ₁def]
    linarith
  have hstart : S ≤ (N : ℝ) * (1 - δ₁) := by
    rw [hδ₁def]
    field_simp
    nlinarith [hval]
  have hlog : 0 < -Real.log (1 - δ₁ / 2) / C := by
    have h : Real.log (1 - δ₁ / 2) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hCpos
  have hlevel : (N : ℝ) * (1 - δ₁) < (N : ℝ) * (1 - δ₁ / 2) := by nlinarith
  -- the minimizer over the fibre
  obtain ⟨B, p, hp, hmin⟩ := rel_exists_basis_sncWeightProfile_minimizer hL3 hn hnorm hcov cX fX
    hd D₀ heff hklt (j • cartierPullback f J) f y hyc hN B₀ ht hjpos hlog
    (L := (N : ℝ) * (1 - δ₁ / 2)) (aHigh := 2 * b * Real.log (1 / κ)) (Cq := (C : ℝ) * j)
    (fun B p hp hL => hj y hN B p hp ht htb (by linarith) hL)
    ⟨B₁, p₁, hp₁, hstart.trans_lt hlevel, hstart.trans_lt (by nlinarith)⟩
  -- its objective is the infimum
  have heq : (∑ i, Real.exp (p.1 / t - p.2 i / j)) =
      relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y N t j :=
    le_antisymm (le_relWeightInfimum cX fX d D₀ _ f y N t j hne hmin)
      (relWeightInfimum_le cX fX d D₀ _ f y t j B hp)
  exact ⟨B, p, hp, hmin, heq.le.trans hgap⟩

end Fibre

end MixedFujita
