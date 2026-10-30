/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FirstMixedZeroSectionRigidity
public import MixedFujita.NefNumericalZeroMixedPowers
public import MixedFujita.FiniteTypeClosedPointEvaluation

/-! 初期切断不要のν0全次数H0次元1上界。 check-269：proper整スキームで第一ample混合交点数が0なら、任意の実非零切断は全点で単元となり、元Cartier因子が主因子になることを証明。実零スキームが非空なら混合交点が正となる既存定理と矛盾させるため、正規性・滑らかさ・曲線判定数値自明性・半豊富性は不要。元nef数値次元ν=0からこの剛性へ接続し、一つの正倍数切断から実主因子倍数と曲線判定数値自明性を導いた。実閉点での係数評価の単射性から、初期切断なしに全倍数H0の有限性と次元1以下を証明。ν=0では一つの正倍数非零切断の存在と、主因子となる正倍数の存在、生成される正倍数の存在が同値となり、半豊富性への追加BPF工程を省ける。存在する元飯高指数は半豊富性を仮定せず0となる。さらにproper整曲線で構造層Euler標数が正ならν=0の元因子の非消滅・主因子性を内部構成。実H1(O)=0からそのEuler正値性を証明し、曲線上の元Lと全倍数の生成を得た。孤立した実lc曲線中心では、この内部非消滅を既存の正確な中心制限へ接続し、明示した中心H1(O)=0と通常H1版KVの下で元の空間の非零切断と中心内の基底外点まで構成。中心正規性は不要だが、中心上のH1(O)=0又はEuler正値性を元lc幾何から供給する部分は未完。一般の正次元ν0中心の初期非消滅、一般KV・無条件BPF・全F1/F2は未完。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower


/-- The ORIGINAL section space has dimension at most one from just the first
ample mixed vanishing. Evaluation at one actual closed point is injective;
no curve-test numerical triviality or normality is supplied. -/
theorem proper_first_mixed_zero_sections_finrank_le_one
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierMixedEulerDifference K (D :: List.replicate (n - 1) J) 0 = 0) :
    FiniteDimensional K Γ(D.sheaf, ⊤) ∧ Module.finrank K Γ(D.sheaf, ⊤) ≤ 1 := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, Set.mem_univ _⟩
  obtain ⟨β⟩ := finiteTypeScheme_closedPoint_has_localEvaluation (K := K) x hx
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  let L : Γ(D.sheaf, ⊤) →ₗ[K] K := β.toLinearMap.comp
    ((cartierLocalCoefficient D x f hf).restrictScalars K)
  have hinj : Function.Injective L := by
    intro a b hab
    by_contra hne
    have hu := proper_first_mixed_zero_nonzero_section_unit K n hdim hn D J hJ hzero
      (a - b) (sub_ne_zero.mpr hne) x f hf
    have hz : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact (hu.map β.toRingHom).ne_zero hz
  exact ⟨FiniteDimensional.of_injective L hinj,
    by simpa using LinearMap.finrank_le_finrank_of_injective hinj⟩


/-- ORIGINAL nef numerical zero bounds ALL graded section spaces, including
zero degree, without any supplied seed, global generation or normality. -/
theorem proper_nef_numerical_zero_graded_sections_bound
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0) (q : ℕ) :
    FiniteDimensional K Γ((q • D).sheaf, ⊤) ∧
      Module.finrank K Γ((q • D).sheaf, ⊤) ≤ 1 := by
  have hfirst := (proper_nef_cartierNumericalDimension_zero_iff_positive_mixed_powers_vanish
    K n hdim hn D J hD hJ).mp hzero ⟨1, by omega⟩ (show (1 : ℕ) ≤ 1 from le_rfl)
  change cartierMixedEulerDifference K (D :: List.replicate (n - 1) J) 0 = 0 at hfirst
  have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K n hdim.le []
    (List.replicate (n - 1) J) (by simp only [List.length_nil, List.length_replicate]; omega) D 0 q
  simp only [List.nil_append, hfirst, mul_zero] at hscale
  exact proper_first_mixed_zero_sections_finrank_le_one K n hdim hn (q • D) J hJ hscale

end MixedFujita
