/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GeneralNefMixedEuler
public import MixedFujita.NefCartierPullbackRepresentatives
public import MixedFujita.SemiampleCartierRepresentatives

/-! 任意実引き戻し代表族の元nef保存と混合非負性。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Original nefness transports simultaneously to actual Cartier
representatives of every pulled direction, with no dominance condition. -/
theorem cartierNef_list_of_pullback_representatives
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [p.IsOver (Spec (CommRingCat.of K))]
    {D : List (CartierDivisor X)} {G : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun A B => Nonempty ((Scheme.Modules.pullback p).obj A.sheaf ≅ B.sheaf)) D G)
    (hD : ∀ A ∈ D, CartierIsNef K A) : ∀ B ∈ G, CartierIsNef K B := by
  induction h with
  | nil => simp
  | @cons A B D G hAB hDG ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · obtain ⟨a⟩ := hAB
      exact cartierIsNef_of_pullback_representative K p A _ a (hD A (List.mem_cons_self ..))
    · exact ih (fun A hA => hD A (List.mem_cons_of_mem _ hA)) C hC


/-- ANY original nef family has nonnegative pulled top coefficient on an
integral proper projective source, for an arbitrary actual morphism over K. -/
theorem proper_pulled_nef_unit_top_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (p : Y ⟶ X) [p.IsOver (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hlen : D.length = n + 1)
    (hD : ∀ F ∈ D, CartierIsNef K F) (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
  obtain ⟨DY, hDY⟩ := exists_cartier_direction_representations p D
  obtain ⟨EY, ⟨aE⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E p
  rw [cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K p hDY E EY aE]
  exact proper_nef_cartierMixedEuler_nonneg_of_dim_le K n hdim hProj DY
    (hDY.length_eq.symm.trans hlen) (cartierNef_list_of_pullback_representatives K p hDY hD) EY

end MixedFujita
