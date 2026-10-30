/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CompleteIntersectionEquationProducts
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Fintype

/-! 実有限置換と適合微分基底による任意余次元留数。 check-290：任意の選択SNC座標を先頭へ移す実有限置換を内部構成し、元の一般IsSNCChartから実閉層の商環・微分基底・純正規化留数・元周囲frame単元を構成。先頭座標という追加仮定を除去した。全法線方程式の同時変更で留数が単元比の積により変換する厳密公式を証明。元SNC成分の実イデアルと実Cartier方程式から各単元比を内部取得し、元K_X+ΣE_iの積局所方程式と、その同じ元方程式に正規化された実SNC閉層留数を供給。切断側の基底・留数・置換・単元比や中間商環の整性は追加仮定ではない。最終成分の標準層との同型・大域SNC随伴・数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Any independent selected coordinate family can be moved into an ordered
prefix by an ACTUAL permutation, constructed with its finite complement. -/
theorem exists_fin_equiv_extending_prefix {m r : ℕ}
    (τ : Fin m → Fin (m + r)) (hτ : Function.Injective τ) :
    ∃ e : Fin (m + r) ≃ Fin (m + r), ∀ i, e (Fin.castAdd r i) = τ i := by
  classical
  let S := Set.range τ
  let e₁ : Fin m ≃ S := Equiv.ofInjective τ hτ
  have hc : Fintype.card (↥(Sᶜ) : Type) = r := by
    rw [Fintype.card_compl_set, Fintype.card_fin, ← Fintype.card_congr e₁, Fintype.card_fin]
    omega
  let e₂ : Fin r ≃ (Sᶜ : Set (Fin (m + r))) := (finCongr hc.symm).trans (Fintype.equivFin _).symm
  let e := finSumFinEquiv.symm.trans ((Equiv.sumCongr e₁ e₂).trans (Equiv.Set.sumCompl S))
  refine ⟨e, ?_⟩
  intro i
  simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  rfl


/-- An ACTUAL quotient with a genuine full differential basis internally supplies its injective
conormal map, exactness and quotient differential basis. The quotient ring
may be nonintegral; no target coordinates, smoothness, basis or exactness is input. -/
theorem basis_complete_intersection_differential_data
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    {m r : ℕ} (g : Fin m → A) (bA : Module.Basis (Fin (m + r)) A Ω[A⁄K])
    (hbg : ∀ i, bA (Fin.castAdd r i) = D K A (g i)) (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g)) :
    ∃ (j : (Fin m → B) →ₗ[B] B ⊗[A] Ω[A⁄K]) (c : Module.Basis (Fin r) B Ω[B⁄K]),
      (∀ i, j (Pi.basisFun B (Fin m) i) =
        (1 : B) ⊗ₜ[A] D K A (g i)) ∧
      Function.Injective j ∧ Function.Exact j (mapBaseChange K A B) ∧
      ∀ i, c i = KaehlerDifferential.map K K A B (bA (Fin.natAdd m i)) := by
  let b := bA.baseChange B
  have hnormal (i : Fin m) : b (Fin.castAdd r i) =
      (1 : B) ⊗ₜ[A] D K A (g i) := by
    rw [Module.Basis.baseChange_apply, hbg]
  have hv : (fun i : Fin m => b (Fin.castAdd r i)) =
      (fun i : Fin m => (1 : B) ⊗ₜ[A] D K A (g i)) := funext hnormal
  have hdiff : LinearMap.ker (mapBaseChange K A B) =
      Submodule.span B (Set.range fun i : Fin m => b (Fin.castAdd r i)) := by
    rw [hv]
    exact finite_quotient_differential_kernel_span _ hsurj hker
  obtain ⟨j, c, hj, hinj, hex, hc⟩ := finite_coordinate_quotient_basis_exact b
    (mapBaseChange K A B) (mapBaseChange_surjective K A B hsurj) hdiff
  refine ⟨j, c, fun i => (hj i).trans (hnormal i), hinj, hex, ?_⟩
  intro i
  rw [hc, Module.Basis.baseChange_apply, mapBaseChange_tmul, one_smul]


/-- Arbitrary-codimension ACTUAL quotient and adapted basis data construct a pure
normalized residue on the pulled ambient canonical line. Its target basis is
internally the remaining coordinate differentials, and its frame coefficient
is EXACTLY ONE. Intermediate quotient integrality is never assumed. -/
theorem basis_complete_intersection_pulled_residue
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    {m r : ℕ} (g : Fin m → A) (bA : Module.Basis (Fin (m + r)) A Ω[A⁄K])
    (hbg : ∀ i, bA (Fin.castAdd r i) = D K A (g i)) (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g)) :
    ∃ (c : Module.Basis (Fin r) B Ω[B⁄K])
      (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]),
      (∀ i, c i = KaehlerDifferential.map K K A B (bA (Fin.natAdd m i))) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) (bA)) =
        exteriorPower.ιMulti B r c := by
  obtain ⟨j, c, hj, hinj, hex, hc⟩ := basis_complete_intersection_differential_data g bA hbg hsurj hker
  let : Module.Free B Ω[B⁄K] := Module.Free.of_basis c
  obtain ⟨e, he⟩ := OAI.ReverseLogKodaira.CanonicalAdjunction.exact_canonical_adjunction
    j (mapBaseChange K A B) hinj hex (mapBaseChange_surjective K A B hsurj)
      (Pi.basisFun B (Fin m)) c
  let a := determinantCoordinate (Pi.basisFun B (Fin m))
  let t := (TensorProduct.congr a (LinearEquiv.refl B (⋀[B]^r Ω[B⁄K]))).trans
    (TensorProduct.lid B (⋀[B]^r Ω[B⁄K]))
  let e' := t.symm.trans e
  have ha : a (exteriorPower.ιMulti B m (Pi.basisFun B (Fin m))) = 1 := by
    rw [determinantCoordinate_wedge, Module.Basis.det_self]
  have he' (z : Fin r → B ⊗[A] Ω[A⁄K]) :
      e' (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
        exteriorPower.ιMulti B (m + r)
          (Fin.append (fun i : Fin m => (1 : B) ⊗ₜ[A] D K A (g i)) z) := by
    have ht : t (exteriorPower.ιMulti B m (Pi.basisFun B (Fin m)) ⊗ₜ[B]
        exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z) := by
      simp only [t, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, TensorProduct.lid_tmul, ha, one_smul]
    change e (t.symm _) = _
    rw [← ht, t.symm_apply_apply]
    simpa only [Function.comp_def, hj] using he (Pi.basisFun B (Fin m)) z
  let R := (finiteFreeExteriorBaseChangeEquiv (B := B) bA (m + r)).trans e'.symm
  have hR (z : Fin r → Ω[A⁄K]) :
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i : Fin m => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
    change e'.symm (finiteFreeExteriorBaseChangeEquiv (B := B) bA (m + r) _) = _
    rw [finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
    apply e'.injective
    rw [e'.apply_symm_apply]
    let w : Fin r → B ⊗[A] Ω[A⁄K] := fun i => (1 : B) ⊗ₜ[A] z i
    have hq : KaehlerDifferential.map K K A B ∘ z = mapBaseChange K A B ∘ w := by
      funext i
      simp only [Function.comp_apply, w, mapBaseChange_tmul, one_smul]
    rw [hq, he']
    congr 1
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, w]
  refine ⟨c, R, hc, hR, ?_⟩
  have hb : Fin.append (fun i : Fin m => D K A (g i))
      (fun i : Fin r => bA (Fin.natAdd m i)) = bA := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using (hbg k).symm
    · simp only [Fin.append_right]
  have h := hR (fun i : Fin r => bA (Fin.natAdd m i))
  rw [hb] at h
  have hv : KaehlerDifferential.map K K A B ∘
      (fun i : Fin r => bA (Fin.natAdd m i)) = c := by
    funext i
    exact (hc i).symm
  rw [hv] at h
  exact h

end MixedFujita
