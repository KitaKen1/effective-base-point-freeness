/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCartierCoordinateEquation
public import MixedFujita.ActualSNCJacobianBound

/-!
Include the additional transverse Cartier coordinate in the actual Jacobian
sum bound. It is distinct from every selected boundary coordinate, so the
old boundary orders plus the new order remain a subsum of the full chart.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Adding one unused selected coordinate preserves the nonnegative subsum inequality. -/
theorem option_selected_sum_add_le {ι α : Type*} [Fintype ι] [Fintype α]
    (σ : ι → Option α) (hσ : ∀ i k a, σ i = some a → σ k = some a → i = k)
    (j : α) (hj : ∀ i, σ i ≠ some j) (v : α → ℤ) (hv : ∀ a, 0 ≤ v a) :
    ∑ i, (σ i).elim 0 v + v j ≤ ∑ a, v a := by
  let τ : Option ι → Option α := fun i => i.elim (some j) σ
  have hτ : ∀ i k a, τ i = some a → τ k = some a → i = k := by
    intro i k a hi hk
    cases i with
    | none =>
      cases k with
      | none => rfl
      | some k =>
        have heq : σ k = some j := hk.trans hi.symm
        exact (hj k heq).elim
    | some i =>
      cases k with
      | none =>
        have heq : σ i = some j := hi.trans hk.symm
        exact (hj i heq).elim
      | some k => exact congrArg some (hσ i k a hi hk)
  have h := option_selected_sum_le τ hτ v hv
  simpa only [Fintype.sum_option, τ, Option.elim_none, Option.elim_some, add_comm] using h

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

include hρ in
/-- The actual boundary orders plus the new transverse coordinate satisfy the Jacobian bound. -/
theorem actual_snc_appended_coordinate_sum_le_jacobian (t : CodimensionOnePoint T)
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U) {r : ℕ}
    (ξ : Fin r → X) (σ : Fin r → Option (Fin n)) (Z : Set X) (j : Fin n)
    (hcsnc : IsSNCChartWith c ξ σ Z (some j))
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) :
    (∑ i, T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T)) +
        T.ord ((dominantFunctionFieldMap ρ).hom
          (etaleChartCoordinateRationalUnit c j : X.functionField)) (t : T) ≤
            1 + T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
  let v := fun a => T.ord ((dominantFunctionFieldMap ρ).hom
    (etaleChartCoordinateRationalUnit c a : X.functionField)) (t : T)
  have hi (i : Fin r) : T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T) = (σ i).elim 0 v := by
    cases hσ : σ i with
    | none => simp [sncChartComponentEquation, hσ]
    | some a => simp only [sncChartComponentEquation, hσ, Option.elim_some]; rfl
  have hv (a : Fin n) : 0 ≤ v a := by
    change 0 ≤ T.ord ((dominantFunctionFieldMap ρ).hom
      (etaleChartCoordinateRationalUnit c a : X.functionField)) (t : T)
    rw [chartCoordinate_pullback_eq_stalk ρ (t : T) c hc a]
    exact scheme_ord_nonneg_of_mem_stalk (t : T) _ ⟨_, rfl⟩
  simp_rw [hi]
  exact (option_selected_sum_add_le σ hcsnc.1.1 j
    (fun i hi => hcsnc.2.1 i j hi rfl) v hv).trans
      (actual_chart_coordinate_sum_le_jacobian ρ hρ t c hc c' hc')

end MixedFujita
