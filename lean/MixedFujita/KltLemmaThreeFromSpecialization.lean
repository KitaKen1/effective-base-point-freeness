/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltAffineLemmaThreeRealization
public import MixedFujita.LemmaThreeFromRestriction

/-!
The klt Lemma 3 on affine opens from the specialization of bad points in smooth families
(step 15).

`KltFamilySpecializationStatement` is the lower semicontinuity of thresholds along a smooth
parameter family with a section, for a klt pair (c_Y, f_Y, d, D₀) with effective boundary on a
normal variety: for an affine open V, a finitely generated domain B over K with formally étale coordinates, a family g on
V × Spec B and a K-algebra map σ : Γ(V) → B (a section Spec B → V), if for a Zariski dense set of
K-points w of B the restriction (id ⊗ w)(g) has threshold at most 1/M at the point σ(w) of V, then
so does it at every K-point of B. For the zero boundary on a smooth variety this is what check 309
derives from restriction to fibres and generic restriction on the product V × Spec B.

The assembly of check 309 then gives the klt Lemma 3
(`kltAffineLemmaThreeStatement_of_familySpecialization`): a K-point χ₀ of Γ(V)[c] killing the
vanishing ideal of the bad points lies on V(𝔭) for a minimal prime 𝔭 in which the bad points are
dense; the domain B of an étale chart of a resolution of V(𝔭) through χ₀
(`exists_resolution_chart_of_prime_coordinates`) carries the family G(Φ(c)) on
V × Spec B and the section given by Φ, the lifts of the bad points are dense in B, and the
specialization at the K-point over χ₀ makes χ₀ bad. With
`kawamataNumericalFreeness_of_kltAffineLemmaThree`, K-NF and F2 follow from the specialization
statement (`kawamataNumericalFreeness_of_kltFamilySpecialization`,
`linearEffectiveFreeness_of_kltFamilySpecialization_of_basePointFree_of_ambro`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

section Statement

/-- **Specialization of bad points in smooth families for a klt pair with effective boundary**:
for an affine open V of a normal variety whose codimension-one points lie in étale charts, a klt
pair with effective boundary, a domain B of finite type with formally étale coordinates, a family g
on V × Spec B and a
K-algebra map σ : Γ(V) → B, if for a Zariski dense set of K-points w of B the restriction
(id ⊗ w)(g) has threshold at most 1/M at the closed point of V given by w ∘ σ, then so does it at
the point w₀ ∘ σ for every K-point w₀ of B. Here B is a domain of finite type with formally étale
coordinates K[u_1, …, u_e] → B (the domain of an étale chart of a smooth variety). -/
def KltFamilySpecializationStatement (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] :
    Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ), 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ D₀ : CartierDivisor Y, LogPairBoundaryEffective cY fY d D₀ → LogPairIsKlt cY fY d D₀ →
    ∀ (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (B : Type u) [CommRing B] [IsDomain B]
      [Algebra K B] [Algebra.FiniteType K B] (e : ℕ) (φ : MvPolynomial (Fin e) K →ₐ[K] B),
      φ.toRingHom.FormallyEtale →
      ∀ {J : Type} [Finite J] (g : J → Γ(Y, V) ⊗[K] B) (M : ℕ), 1 ≤ M →
      ∀ (σS : Γ(Y, V) →ₐ[K] B) (Dset : Set (B →ₐ[K] K)),
        (∀ w ∈ Dset, ∃ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) ∧
          (∀ a, w (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
          ModelThresholdBadAt cY fY d D₀ y
            (fun j => Y.germToFunctionField V (fibreAt w (g j))) M) →
        (∀ b : B, (∀ w ∈ Dset, w b = 0) → b = 0) →
        ∀ (w₀ : B →ₐ[K] K) (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
          (∀ a, w₀ (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) →
          ModelThresholdBadAt cY fY d D₀ y
            (fun j => Y.germToFunctionField V (fibreAt w₀ (g j))) M

end Statement

section Coordinates

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- An étale chart of a resolution of V(𝔭) through a K-point χ₀ on it: a finitely generated domain B
with formally étale coordinates, a K-algebra map Φ : R → B of kernel 𝔭, a common denominator
t ∉ 𝔭 of the elements of B, and a K-point of B over χ₀ (the variant of
`exists_resolution_chart_of_prime` on the domain of an étale chart). -/
theorem exists_resolution_chart_of_prime_coordinates {R : Type u} [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (𝔭 : Ideal R) [𝔭.IsPrime] (χ₀ : R →ₐ[K] K)
    (h₀ : ∀ r ∈ 𝔭, χ₀ r = 0) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B)
      (_ : Algebra.FiniteType K B) (d : ℕ) (φ : MvPolynomial (Fin d) K →ₐ[K] B)
      (_ : φ.toRingHom.FormallyEtale) (Φ : R →ₐ[K] B) (t : R), (∀ r ∈ 𝔭, Φ r = 0) ∧ (∀ r, Φ r = 0 → r ∈ 𝔭) ∧ t ∉ 𝔭 ∧
      (∀ b : B, ∃ (N : ℕ) (r : R), Φ t ^ N * b = Φ r) ∧
      ∃ w₀ : B →ₐ[K] K, w₀.comp Φ = χ₀ := by
  classical
  -- the integral affine scheme of R/𝔭
  let Q := R ⧸ 𝔭
  let S := Spec (CommRingCat.of Q)
  have : LocallyOfFiniteType (S ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K Q)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : QuasiCompact (S ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated (S ↘ Spec (CommRingCat.of K)) := inferInstance
  let χq : Q →ₐ[K] K := Ideal.Quotient.liftₐ 𝔭 χ₀ h₀
  let s₀ : S := specAlgHomPoint χq
  -- a smooth chart of S and a proper smooth birational model
  obtain ⟨-, -, -, d, c, -⟩ := exists_closedPoint_etaleChart (K := K) (W := S) Set.univ
    isOpen_univ ⟨s₀, trivial⟩
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, -, -, -, -⟩ :=
    exists_proper_snc_model c (1 : S.functionFieldˣ) 1 0
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth d _
  -- ρ is surjective; a closed point of T over s₀ and an affine open around it
  have hsurj : Function.Surjective ρ := by
    have hclosed : IsClosed (Set.range ρ) := (Scheme.Hom.isClosedMap ρ).isClosed_range
    have hdense : Dense (Set.range ρ) := hdom.denseRange
    intro s
    have : s ∈ Set.range ρ := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
      trivial
    exact this
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace (T ↘ Spec (CommRingCat.of K))
  obtain ⟨t₁, ht₁⟩ := hsurj s₀
  obtain ⟨t₀, ht₀F, ht₀c⟩ := nonempty_inter_closedPoints (Z := ρ ⁻¹' {s₀}) ⟨t₁, ht₁⟩
    ((specAlgHomPoint_isClosed χq).preimage ρ.continuous).isLocallyClosed
  obtain ⟨cW, ht₀W⟩ : ∃ c : EtaleChart K T d, t₀ ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := d)).symm ▸ Opens.mem_top t₀)
  set W : T.Opens := cW.U with hWdef
  have hW : IsAffineOpen W := cW.isAffine
  have : Nonempty W := ⟨⟨t₀, ht₀W⟩⟩
  have ht₀ : ρ t₀ = s₀ := ht₀F
  have ht₀closed : IsClosed ({t₀} : Set T) := ht₀c
  -- the sections over W
  have hFT : Algebra.FiniteType K Γ(T, W) := smooth_affineOpen_finiteType (n := d) hW
  -- the map Φ : R → Γ(T, W)
  have e : W ≤ ρ ⁻¹ᵁ (⊤ : S.Opens) := fun x _ => trivial
  let ψS : Q →ₐ[K] Γ(S, ⊤) :=
    { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
      commutes' := fun k => (specAlgebraOver_algebraMap Q k).symm }
  let Φ : R →ₐ[K] Γ(T, W) := (appLEAlgHom ρ ⊤ W e).comp (ψS.comp (Ideal.Quotient.mkₐ K 𝔭))
  have hΦ : ∀ r, Φ r = ρ.appLE ⊤ W e
      ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv (Ideal.Quotient.mk 𝔭 r)) := fun r => rfl
  have hinj : Function.Injective (ρ.appLE ⊤ W e) := by
    intro a b hab
    apply S.germToFunctionField_injective ⊤
    apply (dominantFunctionFieldMap ρ).hom.injective
    rw [dominantFunctionFieldMap_germ ρ ⊤ W e a, dominantFunctionFieldMap_germ ρ ⊤ W e b, hab]
  have hker : ∀ r, Φ r = 0 → r ∈ 𝔭 := by
    intro r hr
    rw [hΦ] at hr
    have h1 := hinj (hr.trans (map_zero _).symm)
    have h2 : Ideal.Quotient.mk 𝔭 r = 0 := by
      have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).hom h1
      simpa using h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hΦ𝔭 : ∀ r ∈ 𝔭, Φ r = 0 := by
    intro r hr
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]
  -- every section over W has a denominator from R
  have hfrac : ∀ b : Γ(T, W), ∃ (a s : R), s ∉ 𝔭 ∧ Φ s * b = Φ a := by
    intro b
    have : IsFractionRing Γ(S, ⊤) S.functionField :=
      functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
    obtain ⟨q, hq⟩ := hρ.2 (T.germToFunctionField W b)
    obtain ⟨a', s', hs', hq'⟩ := IsFractionRing.div_surjective (A := Γ(S, ⊤)) q
    have hs'0 : s' ≠ 0 := nonZeroDivisors.ne_zero hs'
    have hgs' : S.germToFunctionField ⊤ s' ≠ 0 := fun h0 =>
      hs'0 (S.germToFunctionField_injective ⊤ (h0.trans (map_zero _).symm))
    have hq2 : q * S.germToFunctionField ⊤ s' = S.germToFunctionField ⊤ a' := by
      rw [← hq']
      change algebraMap Γ(S, ⊤) S.functionField a' / algebraMap Γ(S, ⊤) S.functionField s' *
        algebraMap Γ(S, ⊤) S.functionField s' = algebraMap Γ(S, ⊤) S.functionField a'
      exact div_mul_cancel₀ _ hgs'
    have hq3 := congrArg (dominantFunctionFieldMap ρ).hom hq2
    rw [map_mul, dominantFunctionFieldMap_germ ρ ⊤ W e s',
      dominantFunctionFieldMap_germ ρ ⊤ W e a'] at hq3
    have hq4 : (dominantFunctionFieldMap ρ).hom q = T.germToFunctionField W b := hq
    rw [hq4, ← map_mul] at hq3
    have hb : ρ.appLE ⊤ W e s' * b = ρ.appLE ⊤ W e a' := by
      have := T.germToFunctionField_injective W hq3
      rw [mul_comm] at this
      exact this
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom a')
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom s')
    have hinv : ∀ x : Γ(S, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Q)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom x) = x :=
      fun x => Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of Q)) x
    refine ⟨a, s, fun hs𝔭 => hs'0 ?_, ?_⟩
    · have h0 : (Scheme.ΓSpecIso (CommRingCat.of Q)).hom s' = 0 := by
        rw [← hs]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hs𝔭
      rw [← hinv s', h0, map_zero]
    · rw [hΦ, hΦ, hs, ha, hinv, hinv]
      exact hb
  choose a s hs𝔭 hab using hfrac
  obtain ⟨G, hG⟩ := hFT.out
  let t : R := ∏ b ∈ G, s b
  have ht𝔭 : t ∉ 𝔭 := by
    intro h
    obtain ⟨b, -, hsb⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hs𝔭 b hsb
  have hgen : ∀ b ∈ G, ∃ r, Φ t * b = Φ r := by
    intro b hb
    refine ⟨(∏ b' ∈ G.erase b, s b') * a b, ?_⟩
    have htb : t = (∏ b' ∈ G.erase b, s b') * s b := (Finset.prod_erase_mul _ _ hb).symm
    rw [htb, map_mul, map_mul, mul_assoc, hab b]
  have hden : ∀ x : Γ(T, W), ∃ (N : ℕ) (r : R), Φ t ^ N * x = Φ r := by
    intro x
    have hx : x ∈ Algebra.adjoin K (G : Set Γ(T, W)) := by
      rw [hG]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨r, hr⟩ := hgen x hx
      exact ⟨1, r, by rw [pow_one]; exact hr⟩
    | algebraMap k =>
      exact ⟨0, algebraMap K R k, by rw [pow_zero, one_mul, AlgHom.commutes]⟩
    | add x y _ _ hx hy =>
      obtain ⟨N, r, hr⟩ := hx
      obtain ⟨N', r', hr'⟩ := hy
      refine ⟨N + N', r * t ^ N' + r' * t ^ N, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hr, ← hr', pow_add]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨N, r, hr⟩ := hx
      obtain ⟨N', r', hr'⟩ := hy
      refine ⟨N + N', r * r', ?_⟩
      rw [map_mul, ← hr, ← hr', pow_add]
      ring
  -- the K-point of the closed point over χ₀
  have hmax : (hW.primeIdealOf ⟨t₀, ht₀W⟩).asIdeal.IsMaximal :=
    hW.primeIdealOf_isMaximal_of_isClosed ⟨t₀, ht₀W⟩ ht₀closed
  let w₀ : Γ(T, W) →ₐ[K] K :=
    closedPointEvaluation (K := K) (hW.primeIdealOf ⟨t₀, ht₀W⟩).asIdeal
  have hw₀ : w₀.comp Φ = χ₀ := by
    apply algHom_eq_of_forall_eq_zero_iff
    intro r
    change w₀ (Φ r) = 0 ↔ χ₀ r = 0
    rw [closedPointEvaluation_eq_zero_iff (K := K), ← not_iff_not,
      ← mem_basicOpen_iff_notMem_primeIdealOf hW t₀ ht₀W, hΦ, Scheme.basicOpen_appLE]
    change t₀ ∈ W ∧ ρ t₀ ∈ S.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv
      (Ideal.Quotient.mk 𝔭 r)) ↔ ¬ χ₀ r = 0
    rw [basicOpen_eq_of_affine, ht₀]
    change t₀ ∈ W ∧ Ideal.Quotient.mk 𝔭 r ∉ RingHom.ker χq.toRingHom ↔ ¬ χ₀ r = 0
    rw [RingHom.mem_ker]
    exact ⟨fun h => h.2, fun h => ⟨ht₀W, h⟩⟩
  exact ⟨Γ(T, W), inferInstance, inferInstance, inferInstance, hFT, d, cW.coords, cW.formallyEtale,
    Φ, t, hΦ𝔭, hker, ht𝔭, hden, w₀, hw₀⟩

end Coordinates

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- **The klt Lemma 3 on affine opens from the specialization of bad points in smooth families.** -/
theorem kltAffineLemmaThreeStatement_of_familySpecialization
    (hS : KltFamilySpecializationStatement K) : KltAffineLemmaThreeStatement K := by
  classical
  intro Y _ _ _ _ _ _ n hn hnorm hcov cY fY d hd D₀ heff hklt V hV _ ι J _ _ G M hM
  have hFTA : Algebra.FiniteType K Γ(Y, V) := sectionsBaseOpen_finiteType hV
  have hFTR : Algebra.FiniteType K (MvPolynomial ι Γ(Y, V)) :=
    Algebra.FiniteType.trans hFTA inferInstance
  have : IsNoetherianRing (MvPolynomial ι Γ(Y, V)) := Algebra.FiniteType.isNoetherianRing K _
  -- the bad K-points of Γ(V)[c]
  let ψof : (MvPolynomial ι Γ(Y, V) →ₐ[K] K) → (Γ(Y, V) →ₐ[K] K) := fun χ =>
    χ.comp (IsScalarTower.toAlgHom K Γ(Y, V) (MvPolynomial ι Γ(Y, V)))
  let Bad : Y → (ι → K) → Prop := fun y c =>
    ModelThresholdBadAt cY fY d D₀ y
      (fun j => Y.germToFunctionField V
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j))) M
  let Dset : Set (MvPolynomial ι Γ(Y, V) →ₐ[K] K) := {χ | ∃ (y : Y) (hy : y ∈ V),
    IsClosed ({y} : Set Y) ∧ (∀ a, ψof χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
      Bad y (fun i => χ (MvPolynomial.X i))}
  let I : Ideal (MvPolynomial ι Γ(Y, V)) := ⨅ χ ∈ Dset, RingHom.ker χ.toRingHom
  have hmemI : ∀ g, g ∈ I ↔ ∀ χ ∈ Dset, χ g = 0 := by
    intro g
    simp only [I, Submodule.mem_iInf, RingHom.mem_ker]
    rfl
  refine ⟨I, fun y hy hyc c => ?_⟩
  -- the K-point of (y, c)
  have hmax : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  let evy : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  let χ₀ : MvPolynomial ι Γ(Y, V) →ₐ[K] K :=
    evy.comp ((MvPolynomial.aeval (fun i => algebraMap K Γ(Y, V) (c i))).restrictScalars K)
  have hχ₀ : ∀ g, χ₀ g = evy (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g) := by
    intro g
    change evy (MvPolynomial.aeval _ g) = _
    rw [MvPolynomial.aeval_eq_eval]
  have hψ₀ : ψof χ₀ = evy := by
    ext a
    change χ₀ (MvPolynomial.C a) = evy a
    rw [hχ₀, MvPolynomial.eval_C]
  have hc₀ : (fun i => χ₀ (MvPolynomial.X i)) = c := by
    funext i
    rw [hχ₀, MvPolynomial.eval_X, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hRHS : (∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal) ↔ ∀ g ∈ I, χ₀ g = 0 := by
    refine forall₂_congr fun g _ => ?_
    rw [hχ₀, closedPointEvaluation_eq_zero_iff (K := K)]
  rw [hRHS]
  constructor
  · -- a bad point is in the bad set
    intro hbad g hg
    refine (hmemI g).mp hg χ₀ ⟨y, hy, hyc, ?_, ?_⟩
    · intro a
      rw [hψ₀]
      exact closedPointEvaluation_eq_zero_iff (K := K) _ a
    · rw [hc₀]
      exact hbad
  · -- closedness of the bad set
    intro hI
    have hIle : I ≤ RingHom.ker χ₀.toRingHom := fun g hg => (RingHom.mem_ker).mpr (hI g hg)
    have : (RingHom.ker χ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
    obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hIle
    have h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
    have hI𝔭 : I ≤ 𝔭 := h𝔭min.1.2
    -- an element of the other minimal primes outside 𝔭
    have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
    obtain ⟨s, hsP, hs𝔭⟩ : ∃ s, (∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≠ 𝔭 → s ∈ 𝔮) ∧ s ∉ 𝔭 := by
      by_contra hno
      push Not at hno
      have hle : (hfin.toFinset.erase 𝔭).inf id ≤ 𝔭 := fun s hs => hno s fun 𝔮 h𝔮 hne =>
        (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr h𝔮⟩)) hs
      obtain ⟨𝔮, h𝔮F, h𝔮le⟩ := h𝔭prime.inf_le'.mp hle
      obtain ⟨hne, h𝔮mem⟩ := Finset.mem_erase.mp h𝔮F
      have h𝔮min : 𝔮 ∈ I.minimalPrimes := hfin.mem_toFinset.mp h𝔮mem
      exact hne (le_antisymm h𝔮le (h𝔭min.2 h𝔮min.1 h𝔮le))
    -- the bad points on V(𝔭) are dense in V(𝔭)
    let D𝔭 : Set (MvPolynomial ι Γ(Y, V) →ₐ[K] K) := {χ | χ ∈ Dset ∧ ∀ r ∈ 𝔭, χ r = 0}
    have hD𝔭 : ∀ r, (∀ χ ∈ D𝔭, χ r = 0) → r ∈ 𝔭 := by
      intro r hr
      have hrs : r * s ∈ I := by
        refine (hmemI _).mpr fun χ hχ => ?_
        have hIχ : I ≤ RingHom.ker χ.toRingHom := fun g hg =>
          (RingHom.mem_ker).mpr ((hmemI g).mp hg χ hχ)
        have : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
        obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hIχ
        rw [map_mul]
        by_cases h𝔮 : 𝔮 = 𝔭
        · subst h𝔮
          rw [hr χ ⟨hχ, fun r' hr' => (RingHom.mem_ker).mp (h𝔮le hr')⟩, zero_mul]
        · have hs0 : χ s = 0 := (RingHom.mem_ker).mp (h𝔮le (hsP 𝔮 h𝔮min h𝔮))
          rw [hs0, mul_zero]
      exact (h𝔭prime.mem_or_mem (hI𝔭 hrs)).resolve_right hs𝔭
    -- a smooth affine chart of a resolution of V(𝔭) through χ₀
    obtain ⟨B, _, _, _, hFTB, e, φB, hφB, Φ, t, hΦ𝔭, hker, ht𝔭, hden, w₀, hw₀⟩ :=
      exists_resolution_chart_of_prime_coordinates 𝔭 χ₀
        (fun r hr => (RingHom.mem_ker).mp (h𝔭le hr))
    -- the family on V × Spec B and its fibres
    let ΦX : MvPolynomial ι Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B :=
      (MvPolynomial.aeval (R := Γ(Y, V)) (fun i =>
        (Algebra.TensorProduct.includeRight : B →ₐ[K] Γ(Y, V) ⊗[K] B)
          (Φ (MvPolynomial.X i)))).restrictScalars K
    let g : J → Γ(Y, V) ⊗[K] B := fun j => ΦX (G j)
    have hfib : ∀ (w : B →ₐ[K] K) (j : J), fibreAt w (g j) =
        MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (w (Φ (MvPolynomial.X i)))) (G j) := by
      intro w j
      have h1 : (fibreAt w).toRingHom.comp ΦX.toRingHom = MvPolynomial.eval₂Hom (RingHom.id _)
          (fun i => algebraMap K Γ(Y, V) (w (Φ (MvPolynomial.X i)))) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          change fibreAt w (MvPolynomial.aeval _ (MvPolynomial.C a)) = _
          rw [MvPolynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, fibreAt_tmul]
          simp
        · intro i
          change fibreAt w (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
          rw [MvPolynomial.aeval_X]
          change fibreAt w (1 ⊗ₜ[K] Φ (MvPolynomial.X i)) = _
          rw [fibreAt_tmul]
          simp
      exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* Γ(Y, V) => φ (G j)) h1
    -- the section Spec B → V
    let σS : Γ(Y, V) →ₐ[K] B := Φ.comp (IsScalarTower.toAlgHom K Γ(Y, V) (MvPolynomial ι Γ(Y, V)))
    have hσS : ∀ (w : B →ₐ[K] K) (a : Γ(Y, V)), w (σS a) = ψof (w.comp Φ) a := fun _ _ => rfl
    -- the lifts of the bad points of V(𝔭) are bad and dense
    let DB : Set (B →ₐ[K] K) := {w | w.comp Φ ∈ D𝔭}
    have hbadB : ∀ w ∈ DB, ∃ (y' : Y) (hy' : y' ∈ V), IsClosed ({y'} : Set Y) ∧
        (∀ a, w (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y', hy'⟩).asIdeal) ∧
        ModelThresholdBadAt cY fY d D₀ y'
          (fun j => Y.germToFunctionField V (fibreAt w (g j))) M := by
      intro w hw
      obtain ⟨⟨y', hy', hyc', hψ', hbad'⟩, -⟩ := hw
      refine ⟨y', hy', hyc', fun a => ?_, ?_⟩
      · rw [hσS]
        exact hψ' a
      · simp only [hfib]
        exact hbad'
    have hdenseB : ∀ b : B, (∀ w ∈ DB, w b = 0) → b = 0 := fun b hb =>
      eq_zero_of_forall_lift_mem Φ 𝔭 hΦ𝔭 hker t ht𝔭 hden D𝔭 (fun χ hχ => hχ.2) hD𝔭
        (one_ne_zero : (1 : B) ≠ 0) fun w _ hw => hb w hw
    -- the point over χ₀ is bad
    have hψ₀' : ψof (w₀.comp Φ) = evy := by
      rw [hw₀]
      exact hψ₀
    have hmatch : ∀ a, w₀ (σS a) = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
      intro a
      rw [hσS, hψ₀']
      exact closedPointEvaluation_eq_zero_iff (K := K) _ a
    have hfin' := hS Y n hn hnorm hcov cY fY d hd D₀ heff hklt V hV B e φB hφB g M hM σS DB
      hbadB hdenseB w₀ y hy hyc hmatch
    simp only [hfib] at hfin'
    have hc' : (fun i => w₀ (Φ (MvPolynomial.X i))) = c := by
      funext i
      have h3 := congrArg (fun φ : MvPolynomial ι Γ(Y, V) →ₐ[K] K => φ (MvPolynomial.X i)) hw₀
      simp only [AlgHom.comp_apply] at h3
      rw [h3]
      exact congrFun hc₀ i
    have hc'' : ∀ i, w₀ (Φ (MvPolynomial.X i)) = c i := fun i => congrFun hc' i
    simp only [hc''] at hfin'
    exact hfin'

end Assembly

/-- **K-NF from the specialization of bad points in smooth families of klt pairs** (Kawamata–Viehweg
vanishing is proved). -/
theorem kawamataNumericalFreeness_of_kltFamilySpecialization
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltFamilySpecializationStatement K) :
    KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_kltAffineLemmaThree fun K _ _ _ =>
    kltAffineLemmaThreeStatement_of_familySpecialization (h K)

/-- **F2 from the specialization of bad points in smooth families of klt pairs, the base point
free theorem for klt pairs and Ambro's canonical bundle formula for contractions to
lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_kltFamilySpecialization_of_basePointFree_of_ambro
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      KltFamilySpecializationStatement K)
    (hbpf : KltBasePointFreeStatement.{u}) (hamb : AmbroStrictDimensionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kltAffineLemmaThree_of_basePointFree_of_ambro
    (fun K _ _ _ => kltAffineLemmaThreeStatement_of_familySpecialization (h K)) hbpf hamb

end MixedFujita
