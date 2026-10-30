/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FirstMixedZeroSectionRigidity
public import MixedFujita.NefNumericalZeroMixedPowers
public import MixedFujita.CartierNumericalDimensionInvariance
public import MixedFujita.CartierNumericalTriviality

/-! 元nef数値次元0の一切断から主因子倍数と曲線判定数値自明性。 check-269：proper整スキームで第一ample混合交点数が0なら、任意の実非零切断は全点で単元となり、元Cartier因子が主因子になることを証明。実零スキームが非空なら混合交点が正となる既存定理と矛盾させるため、正規性・滑らかさ・曲線判定数値自明性・半豊富性は不要。元nef数値次元ν=0からこの剛性へ接続し、一つの正倍数切断から実主因子倍数と曲線判定数値自明性を導いた。実閉点での係数評価の単射性から、初期切断なしに全倍数H0の有限性と次元1以下を証明。ν=0では一つの正倍数非零切断の存在と、主因子となる正倍数の存在、生成される正倍数の存在が同値となり、半豊富性への追加BPF工程を省ける。存在する元飯高指数は半豊富性を仮定せず0となる。さらにproper整曲線で構造層Euler標数が正ならν=0の元因子の非消滅・主因子性を内部構成。実H1(O)=0からそのEuler正値性を証明し、曲線上の元Lと全倍数の生成を得た。孤立した実lc曲線中心では、この内部非消滅を既存の正確な中心制限へ接続し、明示した中心H1(O)=0と通常H1版KVの下で元の空間の非零切断と中心内の基底外点まで構成。中心正規性は不要だが、中心上のH1(O)=0又はEuler正値性を元lc幾何から供給する部分は未完。一般の正次元ν0中心の初期非消滅、一般KV・無条件BPF・全F1/F2は未完。 -/

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


/-- ORIGINAL numerical dimension zero gives first mixed vanishing and hence
rigidity of any existing section. It does NOT assert existence of a section. -/
theorem proper_nef_numerical_zero_principal_of_nonzero_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ f : X.functionFieldˣ, D = principalCartierDivisor X f := by
  have hfirst := (proper_nef_cartierNumericalDimension_zero_iff_positive_mixed_powers_vanish
    K n hdim hn D J hD hJ).mp hzero ⟨1, by omega⟩ (show (1 : ℕ) ≤ 1 from le_rfl)
  change cartierMixedEulerDifference K (D :: List.replicate (n - 1) J) 0 = 0 at hfirst
  exact proper_first_mixed_zero_principal_of_nonzero_section K n hdim hn D J hJ hfirst s hs


/-- A SINGLE positive-power section of an ORIGINAL nef numerical-zero divisor
forces an actual principal multiple and the ORIGINAL curve-test numerical triviality,
even on a possibly nonnormal source. -/
theorem proper_nef_numerical_zero_section_seed_principal_multiple_and_numericallyTrivial
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (q : ℕ) (hq : 0 < q) (s : Γ((q • D).sheaf, ⊤)) (hs : s ≠ 0) :
    (∃ f : X.functionFieldˣ, q • D = principalCartierDivisor X f) ∧
      CartierIsNumericallyTrivial K D := by
  have hzq : cartierNumericalDimension K n hdim (q • D) J = 0 := by
    rw [cartierNumericalDimension_nsmul K n hdim D J q hq, hzero]
  have hprin := proper_nef_numerical_zero_principal_of_nonzero_section
    K n hdim hn (q • D) J (cartierIsNef_nsmul hD q) hJ hzq s hs
  exact ⟨hprin, cartierIsNumericallyTrivial_of_principal_multiple D hq hprin⟩

end MixedFujita
