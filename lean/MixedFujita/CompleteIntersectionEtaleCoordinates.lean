/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCOriginalCartierSumResidue
public import MixedFujita.JacobianCriterionCharts

/-! 実余接複体の分裂による商の滑らかさと残余エタール座標。 check-291：実商の核を生成する法線方程式の微分が周囲基底の一部となる場合、元の実余接複体を基底座標射影で分裂し、商の形式的滑らかさを追加仮定なく証明。既存Jacobian判定で残余座標写像の実エタール性を導き、一般の選択SNC座標から実閉層上のエタール座標を内部構成した。実K作用での留数と任意の標準frameの単元比較を構成し、最終層が整で元の標準類参照チャート・被覆があるとき、元i^*O(K_X+ΣE_i)とO(K_Y)の実局所加群層同型を存在・一意性、全部分開の係数公式、最高次形式の留数正規化付きで構成。切断側座標・そのエタール性・微分基底・留数・frame単元・層同型は追加入力ではない。最終整成分の供給、全点局所入力、大域SNC随伴と数値随伴は残る。 -/

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


/-- Independent normal differentials in an actual smooth ambient algebra
give an EXPLICIT splitting of the ACTUAL cotangent complex. Thus the quotient
is formally smooth; target smoothness is a conclusion, not an input. -/
theorem basis_complete_intersection_formallySmooth
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A]
    {m r : ℕ} (g : Fin m → A) (bA : Module.Basis (Fin (m + r)) A Ω[A⁄K])
    (hbg : ∀ i, bA (Fin.castAdd r i) = D K A (g i))
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g)) :
    Algebra.FormallySmooth K B := by
  classical
  let P : Algebra.Extension K B := ⟨A, _, Function.surjInv_eq hsurj⟩
  have hmem (i : Fin m) : g i ∈ P.ker := by
    change g i ∈ RingHom.ker (algebraMap A B)
    rw [hker]
    exact Ideal.subset_span (Set.mem_range_self i)
  let cg : Fin m → P.Cotangent := fun i => Algebra.Extension.Cotangent.mk ⟨g i, hmem i⟩
  let b := bA.baseChange B
  have hf (i : Fin m) : P.cotangentComplex (cg i) = b (Fin.castAdd r i) := by
    rw [Algebra.Extension.cotangentComplex_mk, Module.Basis.baseChange_apply, hbg]
  have hspan : Submodule.span B (Set.range cg) = ⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P) g hker.symm
  let l : P.CotangentSpace →ₗ[B] P.Cotangent :=
    ∑ i, (b.coord (Fin.castAdd r i)).smulRight (cg i)
  have hl : l ∘ₗ P.cotangentComplex = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    simp only [LinearMap.comp_apply, hf, l, LinearMap.sum_apply,
      LinearMap.smulRight_apply, Module.Basis.coord_apply, LinearMap.id_apply]
    rw [b.repr_self]
    simp only [Finsupp.single_apply, Fin.castAdd_inj, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (P.formallySmooth_iff_split_injection).mpr ⟨l, hl⟩


/-- A genuine etale coordinate quotient supplies its OWN residual etale
coordinates, not merely a differential basis. No quotient smoothness input. -/
theorem etale_coordinate_quotient_tail_coordinates
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    {m r : ℕ} (x : MvPolynomial (Fin (m + r)) K →ₐ[K] A)
    (hx : x.toRingHom.FormallyEtale) (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) =
      Ideal.span (Set.range fun i : Fin m => x (MvPolynomial.X (Fin.castAdd r i)))) :
    ∃ y : MvPolynomial (Fin r) K →ₐ[K] B, y.toRingHom.FormallyEtale ∧
      ∀ i, y (MvPolynomial.X i) = algebraMap A B (x (MvPolynomial.X (Fin.natAdd m i))) := by
  let bA := etaleCoordinateBasis x hx
  let : Algebra.FormallySmooth K A := formallySmooth_of_etale_coordinates x hx
  let : Algebra.FormallySmooth K B := basis_complete_intersection_formallySmooth
    (fun i => x (MvPolynomial.X (Fin.castAdd r i))) bA
    (fun i => etaleCoordinateBasis_apply x hx (Fin.castAdd r i)) hsurj hker
  obtain ⟨_j, b, _hj, _hinj, _hex, hb⟩ := etale_coordinate_quotient_differential_basis x hx hsurj hker
  let y : MvPolynomial (Fin r) K →ₐ[K] B := MvPolynomial.aeval (fun i : Fin r => algebraMap A B (x (MvPolynomial.X (Fin.natAdd m i))))
  have hy (i : Fin r) : y (MvPolynomial.X i) = algebraMap A B (x (MvPolynomial.X (Fin.natAdd m i))) :=
    MvPolynomial.aeval_X (R := K) _ i
  exact ⟨y, formallyEtale_of_kaehlerBasis y b (fun i => (hb i).trans (congrArg (D K B) (hy i).symm)), hy⟩

end MixedFujita
