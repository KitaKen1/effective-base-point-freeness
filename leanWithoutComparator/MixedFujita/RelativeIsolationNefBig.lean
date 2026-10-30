/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeIsolationLifting

/-!
Section 6 of the manuscript when the sections do not span a big divisor (step 17R-1).

In section 6 the sections s_i are sections of multiples of L_X and the bigness of the divisor
D₁ in (27) comes from L_X. In relative K-NF, L_X is the pullback of an ample divisor of the base
of a contraction and is not big; the bigness comes from the remainder N_X instead. Here
d π*P − (d(K_X + div f₀) + B) = L_X + N_X with ρ*L_X and ρ*N_X nef and every combination
a ρ*L_X + b ρ*N_X with b ≥ 1 big; then the whole divisor e₁ ρ*L_X + w(u ρ*L_X − G) + m' ρ*N_X of
(27) is nef and big, and the ordinary Kawamata–Viehweg statement gives the vanishing.

* `isolation_model_floor_divisor_nef_big_of_remainder`: the numerical statement (27);
* `isolation_model_exists_section_generating_of_kv_of_open`: sections 6.1 to 6.3 on a given
  isolation model, with the centre in a closed set;
* `exists_section_generating_of_minimizer_data_of_kv_of_open`: from the data of the minimizer over
  a closed set and the Kawamata–Viehweg statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Model

variable {K : Type u} [Field K] {n : ℕ} {X T V : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral V] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

omit [IsLocallyNoetherian X] in
/-- The numerical statement (27) and (30) with denominators cleared, with the bigness taken from
the remainder: if ρ*L_X and ρ*N_X are nef and every a ρ*L_X + b ρ*N_X with b ≥ 1 is big, there
are natural numbers a_k < m' d and a nef and big divisor D₁ such that
m' d (ρ*π*P − ⌊Γ⌋ − K_T) − Σ a_k E_k = D₁. -/
theorem isolation_model_floor_divisor_nef_big_of_remainder
    (π : X ⟶ V) [IsDominant π] (P : CartierDivisor V)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T)
    (hinjT : Function.Injective ξT) (E : Fin r' → CartierDivisor T)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (Mn : ℕ) (η : ℝ) (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m')
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hNnef : CartierIsNef K (cartierPullback ρ NX))
    (hABbig : ∀ a b : ℕ, 1 ≤ b →
      CartierIsBig K (a • cartierPullback ρ LX + b • cartierPullback ρ NX))
    (hABfin : ∀ a b : ℕ,
      FiniteDimensional K Γ((a • cartierPullback ρ LX + b • cartierPullback ρ NX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc)) :
    ∃ a : Fin r' → ℕ, (∀ k, a k < m' * d) ∧ ∃ D₁ : CartierDivisor T,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ ∧
      CartierIsNef K D₁ ∧ CartierIsBig K D₁ := by
  obtain ⟨a, halt, f, hEq⟩ := isolation_model_floor_divisor_linear_equivalence ρ hρ π P c₀ f₀ d
    hd B Dv cT ξT hinjT E hEc hTB hTD Gc hTG c₁ Mn η LX NX hLN j hDlin m' hm' p w u e₁ hp hw he₁
  refine ⟨a, halt, _, hEq, ?_, ?_⟩
  · exact (cartierIsNef_add_principal_iff f).mpr (cartierIsNef_add (cartierIsNef_add
      (cartierIsNef_nsmul hLnef e₁) (cartierIsNef_nsmul (cartierIsGloballyGenerated_isNef hGG) w))
      (cartierIsNef_nsmul hNnef m'))
  · have hsplit : e₁ • cartierPullback ρ LX + w • (cartierPullback ρ (u • LX) - Gc) +
        m' • cartierPullback ρ NX + principalCartierDivisor T f =
        ((e₁ • cartierPullback ρ LX + m' • cartierPullback ρ NX) +
          w • (cartierPullback ρ (u • LX) - Gc)) + principalCartierDivisor T f := by
      abel
    rw [hsplit]
    apply cartierIsBig_add_principal
    obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isGloballyGenerated _ hGG
    refine cartierIsBig_add_of_section (hABbig e₁ m' hm') (cartierSectionPower _ t w)
      (cartierSectionPower_ne_zero _ t ht w) fun k => ?_
    obtain ⟨tG, htG⟩ := exists_section_ne_zero_of_isEffective ((k * w) • Gc)
      (cartier_nsmul_isEffective Gc hGc (k * w))
    refine finiteDimensional_of_eq_add_of_section (K := K) _ ((k * w) • Gc)
      ((k * (e₁ + w * u)) • cartierPullback ρ LX + (k * m') • cartierPullback ρ NX) ?_ tG htG
      (hABfin _ _)
    rw [cartierPullback_nsmul ρ LX u]
    module

variable [IsLocallyNoetherian V] [IsProper ρ]

/-- Sections 6.1 to 6.3 on a given isolation model with the centre in a closed set and the
bigness taken from the remainder, with the vanishing as a hypothesis in the form of the ordinary
Kawamata–Viehweg statement. -/
theorem isolation_model_exists_section_generating_of_kv_of_open
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (Φ : Set V) (hΦ : IsClosed Φ) (fP : V.functionFieldˣ) (V₀ : V.Opens)
    (hΦV₀ : Φ ⊆ (V₀ : Set V)) (hV₀ : ∀ v ∈ V₀, P.IsLocalEquationAt v fP)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1)
    (E : Fin r' → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (S : Set (Fin r')) (hS : S.Nonempty) (hSΦ : ∀ k ∈ S, π (ρ (ξT k)) ∈ Φ)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m')
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hNnef : CartierIsNef K (cartierPullback ρ NX))
    (hABbig : ∀ a b : ℕ, 1 ≤ b →
      CartierIsBig K (a • cartierPullback ρ LX + b • cartierPullback ρ NX))
    (hABfin : ∀ a b : ℕ,
      FiniteDimensional K Γ((a • cartierPullback ρ LX + b • cartierPullback ρ NX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc))
    (hvan : ∀ a : Fin r' → ℕ, (∀ k, a k < m' * d) → ∀ D₁ : CartierDivisor T,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ →
      CartierIsNef K D₁ → CartierIsBig K D₁ →
      Subsingleton (Scheme.Modules.Cohomology
        (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k).sheaf 1)) :
    ∃ v ∈ Φ, ∃ (g : V.functionField) (u' : (V.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (V.presheaf.stalk v) V.functionField u' = fP * g := by
  obtain ⟨a, halt, D₁, hdec, hnef, hbig⟩ := isolation_model_floor_divisor_nef_big_of_remainder ρ hρ
    π P c₀ f₀ d hd B Dv cT ξT hinjT E hEc hTB hTD Gc hGc hTG c₁ Mn η LX NX hLN j hDlin m' hm' p w
    u e₁ hp hw he₁ hLnef hNnef hABbig hABfin hGG
  exact isolation_model_exists_section_generating_of_open ρ hρ hnormV π hπ P Φ hΦ fP V₀ hΦV₀ hV₀
    c₀ f₀ d hd B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc Gc hGc c₁ hc₁ Mn η hη0 hη1 S hS hSΦ hSeq
    hSmeet (hvan a halt D₁ hdec hnef hbig)

end Model

section Generation

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X V : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral V] [IsLocallyNoetherian V]

/-- Section 6 as one statement with the centre in a closed set and the bigness taken from the
remainder: on a smooth proper simple normal crossing model π : X → V of a normal scheme V, with
d π*P − (d(K_X + div f₀) + B) = L_X + N_X, the multiples of m₀ L_X globally generated, the
pullbacks of N_X to models of X nef, every a L_X + b N_X with b ≥ 1 big and with
finite-dimensional sections, and the D_i linearly equivalent to j L_X with m₀ dividing j, the
data of the minimizer over the closed set Φ of V give, by the Kawamata–Viehweg statement, a global
section of P generating it with the local equation fP at a point of Φ. -/
theorem exists_section_generating_of_minimizer_data_of_kv_of_open
    (hKV : KawamataViehwegVanishingSNC K n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (Φ : Set V) (hΦ : IsClosed Φ) (fP : V.functionFieldˣ) (V₀ : V.Opens)
    (hΦV₀ : Φ ⊆ (V₀ : Set V)) (hV₀ : ∀ v ∈ V₀, P.IsLocalEquationAt v fP)
    {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hjm₀ : m₀ ∣ j)
    (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • LX))
    (hNnefPull : ∀ (T' : Scheme.{u}) [IsIntegral T'] [T'.Over (Spec (CommRingCat.of K))]
      (ρ' : T' ⟶ X) [IsDominant ρ'] [ρ'.IsOver (Spec (CommRingCat.of K))],
      CartierIsNef K (cartierPullback ρ' NX))
    (hABbig : ∀ a b : ℕ, 1 ≤ b → CartierIsBig K (a • LX + b • NX))
    (hABfin : ∀ a b : ℕ, FiniteDimensional K Γ((a • LX + b • NX).sheaf, ⊤))
    (y : X) (hy : π y ∈ Φ) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' Φ, InSNCProfilePolytope ξ d B Dv q p →
      ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' Φ).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ π ⁻¹' Φ)
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ v ∈ Φ, ∃ (g : V.functionField) (u : (V.presheaf.stalk v)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧
      algebraMap (V.presheaf.stalk v) V.functionField u = fP * g := by
  have hΦX : IsClosed (π ⁻¹' Φ) := hΦ.preimage π.continuous
  obtain ⟨c₁, q₀, Mn, nn, hc₁, hc₁rat, hq₀, hq₀rat, hc₁q₀, hbud₁, hMn, hI, hnn, hAeff, T, hTi, hTo,
    hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r', ξT, Gc, hGc, hinjT, hξT, hsncT, hTB, hTD, hTG,
    hGcI, hgg, hS⟩ := exists_isolation_model ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hDeff hD
      (π ⁻¹' Φ) hΦX y hy hc hcq hqy hpolyΦ hcentre (Nat.cast_nonneg (d * j)) hbudget
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hpropT : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  -- the member divisors of the family of T
  obtain ⟨E, hE, -, hEc⟩ := exists_snc_component_cartier ξT hξT hsncT
  -- the multiple u of A_X
  obtain ⟨j', rfl⟩ := hjm₀
  let U : ℕ := ∑ i, nn i * j'
  have hGG : CartierIsGloballyGenerated (cartierPullback ρ ((m₀ * U) • LX) - Gc) := by
    refine (hgg ((m₀ * U) • LX) fun k => ?_).1
    obtain ⟨h, hh⟩ := hDlin k.1
    have hle : nn k.1 * j' ≤ U :=
      Finset.single_le_sum (f := fun i => nn i * j') (fun i _ => Nat.zero_le _)
        (Finset.mem_univ k.1)
    obtain ⟨V', hV'⟩ : ∃ V', V' + nn k.1 * j' = U := ⟨U - nn k.1 * j', Nat.sub_add_cancel hle⟩
    have heq : (m₀ * U) • LX - nn k.1 • Dv k.1 =
        (V' * m₀) • LX + principalCartierDivisor X (h⁻¹ ^ nn k.1) := by
      rw [hh, principalCartierDivisor_power, principalCartierDivisor_inv, ← hV']
      module
    rw [heq]
    exact cartierIsGloballyGenerated_principal_shift _ _ (hLgg V')
  -- the integers of section 6.3
  obtain ⟨η, m', p, w, e₁, hη0, hη1, hm', he₁pos, hp, hw, he₁⟩ :=
    exists_isolation_integers c₁ hc₁ hc₁rat Mn hMn d hd (m₀ * j') (m₀ * U) hbud₁
  obtain ⟨S, hSne, hSprop, hSmeet⟩ := hS η hη0 hη1
  -- positivity on T
  have hLnef : CartierIsNef K (cartierPullback ρ LX) :=
    cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul ρ LX m₀ hm₀
      (by simpa using hLgg 1)
  have hNnef : CartierIsNef K (cartierPullback ρ NX) := hNnefPull T ρ
  have hdim : topologicalKrullDim T = topologicalKrullDim X :=
    (etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim c₀).symm
  have hpull : ∀ a b : ℕ, cartierPullback ρ (a • LX + b • NX) =
      a • cartierPullback ρ LX + b • cartierPullback ρ NX := fun a b => by
    rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul]
  have hABbigT : ∀ a b : ℕ, 1 ≤ b →
      CartierIsBig K (a • cartierPullback ρ LX + b • cartierPullback ρ NX) := fun a b hb => by
    rw [← hpull]
    exact cartierIsBig_cartierPullback hnormX hnormT ρ hρ hdim (hABbig a b hb)
  have hABfinT : ∀ a b : ℕ,
      FiniteDimensional K Γ((a • cartierPullback ρ LX + b • cartierPullback ρ NX).sheaf, ⊤) :=
    fun a b => by
      rw [← hpull]
      exact finiteDimensional_sections_cartierPullback hnormX ρ hρ _ (hABfin a b)
  exact isolation_model_exists_section_generating_of_kv_of_open ρ hρ hnormV π hπ P Φ hΦ fP V₀
    hΦV₀ hV₀ c₀ f₀ d hd B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc hTB hTD Gc hGc hTG c₁
    (fun i => (hc₁ i).le) Mn η hη0.le hη1.le S hSne (fun k hk => (hSprop k hk).1)
    (fun k hk => (hSprop k hk).2) hSmeet LX NX hLN (m₀ * j') hDlin m' hm' p w (m₀ * U) e₁ hp hw
    he₁ hLnef hNnef hABbigT hABfinT hGG
    (fun a halt D₁ hdec hnef hbig => hKV T cT r' ξT hinjT hξT hsncT E hEc _ (m' * d)
      (Nat.mul_pos hm' hd) a halt (by rw [hdec]; exact hnef) (by rw [hdec]; exact hbig))

end Generation

end MixedFujita
