/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveAmpleMixedIntersectionPositive
public import MixedFujita.CartierSectionZeroIdeal
public import MixedFujita.CartierSectionUnitPrincipality

/-! 第一混合交点0から非正規源の全点単元切断と主因子性。 check-269：proper整スキームで第一ample混合交点数が0なら、任意の実非零切断は全点で単元となり、元Cartier因子が主因子になることを証明。実零スキームが非空なら混合交点が正となる既存定理と矛盾させるため、正規性・滑らかさ・曲線判定数値自明性・半豊富性は不要。元nef数値次元ν=0からこの剛性へ接続し、一つの正倍数切断から実主因子倍数と曲線判定数値自明性を導いた。実閉点での係数評価の単射性から、初期切断なしに全倍数H0の有限性と次元1以下を証明。ν=0では一つの正倍数非零切断の存在と、主因子となる正倍数の存在、生成される正倍数の存在が同値となり、半豊富性への追加BPF工程を省ける。存在する元飯高指数は半豊富性を仮定せず0となる。さらにproper整曲線で構造層Euler標数が正ならν=0の元因子の非消滅・主因子性を内部構成。実H1(O)=0からそのEuler正値性を証明し、曲線上の元Lと全倍数の生成を得た。孤立した実lc曲線中心では、この内部非消滅を既存の正確な中心制限へ接続し、明示した中心H1(O)=0と通常H1版KVの下で元の空間の非零切断と中心内の基底外点まで構成。中心正規性は不要だが、中心上のH1(O)=0又はEuler正値性を元lc幾何から供給する部分は未完。一般の正次元ν0中心の初期非消滅、一般KV・無条件BPF・全F1/F2は未完。 -/

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


/-- A zero first ample mixed intersection makes EVERY actual nonzero section
nowhere vanishing, on an arbitrary proper INTEGRAL source, with no normality. -/
theorem proper_first_mixed_zero_nonzero_section_unit
    (K : Type u) [Field K] [Infinite K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierMixedEulerDifference K (D :: List.replicate (n - 1) J) 0 = 0)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    IsUnit (cartierLocalCoefficient D x f hf s) := by
  by_contra hnot
  let G := cartierSectionZeroDivisor D s hs
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective D s hs
  have hx : x ∈ (cartierSectionZeroIdeal D s hs).support := by
    change x ∈ ((cartierSectionZeroIdeal D s hs).support : Set X)
    rw [show ((cartierSectionZeroIdeal D s hs).support : Set X) =
      cartierSectionZeroLocus D s from cartierSectionZeroIdeal_support (K := K) D s hs]
    change x ∉ cartierSectionNonvanishingOpen D s
    rwa [mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f hf]
  have hne : Nonempty (effectiveCartierIdealSheaf G hG).subscheme := by
    have hx' : x ∈ Set.range (effectiveCartierIdealSheaf G hG).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y⟩
  have hdim' : topologicalKrullDim X = ((n - 1) + 1 : ℕ) := by
    simpa only [Nat.sub_add_cancel hn] using hdim
  have hpos := proper_effective_nonempty_ample_cartierMixedEuler_positive K (n - 1) hdim'
    G hG hne (List.replicate (n - 1) J) (List.length_replicate ..)
    (fun H hH => (List.mem_replicate.mp hH).2 ▸ hJ) 0
  change 0 < cartierMixedEulerDifference K
    ((D + principalCartierDivisor X (cartierSectionUnit D s hs)) :: List.replicate (n - 1) J) 0 at hpos
  rw [cartierMixedEulerDifference_direction_principal, hzero] at hpos
  exact lt_irrefl 0 hpos


/-- First mixed vanishing plus ONE actual section already proves principality;
neither nefness nor a smooth or normal source is needed. -/
theorem proper_first_mixed_zero_principal_of_nonzero_section
    (K : Type u) [Field K] [Infinite K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierMixedEulerDifference K (D :: List.replicate (n - 1) J) 0 = 0)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ f : X.functionFieldˣ, D = principalCartierDivisor X f :=
  principal_of_section_everywhere_unit D s hs
    (proper_first_mixed_zero_nonzero_section_unit K n hdim hn D J hJ hzero s hs)

end MixedFujita
