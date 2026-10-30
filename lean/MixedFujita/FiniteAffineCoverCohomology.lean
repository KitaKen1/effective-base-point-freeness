/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwoAffineCohomology
public import Mathlib.Data.Finset.Lattice.Fold

/-!
Mayer--Vietoris induction gives vanishing above the size of a finite
affine cover on a locally Noetherian scheme with affine diagonal.
The bound is the number of opens, not the intrinsic dimension.
No finite-dimensionality of cohomology is assumed or proved here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules
namespace MixedFujita
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  (M : X.Modules) [M.IsQuasicoherent]

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
theorem finiteAffine_cohomologyOn_vanish {U : X.Opens}
    (hU : IsAffineOpen U) (q : ℕ) (hq : 0 < q) :
    Subsingleton (cohomologyOn M q U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  exact Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen M hU k

theorem finiteAffineUnion_cohomologyOn_vanish {ι : Type*}
    (s : Finset ι) (U : ι → X.Opens) (hU : ∀ i ∈ s, IsAffineOpen (U i))
    (q : ℕ) (hq : s.card ≤ q) (hpos : 0 < q) :
    Subsingleton (cohomologyOn M q (s.sup U)) := by
  classical
  induction s using Finset.induction_on generalizing U q with
  | empty =>
    simp only [Finset.sup_empty]
    exact finiteAffine_cohomologyOn_vanish M (isAffineOpen_bot X) q hpos
  | @insert a s ha ih =>
    have hA := hU a (Finset.mem_insert_self a s)
    have hS : ∀ i ∈ s, IsAffineOpen (U i) :=
      fun i hi ↦ hU i (Finset.mem_insert_of_mem hi)
    by_cases hs : s = ∅
    · subst s
      simp only [Finset.sup_insert, Finset.sup_empty, sup_bot_eq]
      exact finiteAffine_cohomologyOn_vanish M hA q hpos
    · have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      rw [Finset.card_insert_of_notMem ha] at hq
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      rw [Finset.sup_insert]
      apply subsingleton_cohomologyOn_sup_succ M k
      · rw [Finset.sup_inf_distrib_left]
        exact ih (fun i ↦ U a ⊓ U i) (fun i hi ↦ hA.inf (hS i hi)) k (by omega) (by omega)
      · exact finiteAffine_cohomologyOn_vanish M hA (k + 1) (by omega)
      · exact ih U hS (k + 1) (by omega) (by omega)

theorem finiteAffineCover_cohomology_vanish {ι : Type*} [Fintype ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (q : ℕ) (hq : Fintype.card ι ≤ q) (hpos : 0 < q) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M q) := by
  have h := finiteAffineUnion_cohomologyOn_vanish M Finset.univ U
    (fun i _ ↦ hU i) q (by simpa using hq) hpos
  have htop : Finset.univ.sup U = ⊤ := by
    rw [Finset.sup_eq_iSup]
    simpa using hcover
  rw [htop] at h
  exact (cohomologyOnTopIso M q).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end MixedFujita
