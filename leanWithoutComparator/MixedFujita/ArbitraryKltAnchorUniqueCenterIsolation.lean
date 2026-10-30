/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InternalUniqueLCCenterIsolation
public import MixedFujita.ArbitraryKltAnchorCenterIsolation

/-! 任意分母アンカーの一意中心孤立化と元mL持上げ。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u v
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- An ARBITRARY-denominator klt anchor internally isolates a UNIQUE actual lc center, retains the SAME ORIGINAL nef L and ALL large ample adjoints, and preserves explicit-usual-H1-KV original-mL lifting. New minimality/uniqueness is proved internally. -/
theorem minimal_lc_center_arbitrary_klt_anchor_unique_center_isolation_and_original_lifting
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hD : LogPairBoundaryEffective c f d D)
    (e : ℕ) (he : 1 ≤ e) (A : CartierDivisor X) (hA : LogPairBoundaryEffective c f e A)
    (hklt : LogPairIsKlt c f e A)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ d' : ℕ, 1 ≤ d' ∧ ∃ D' : CartierDivisor X,
      LogPairBoundaryEffective c f d' D' ∧ LogPairIsLogCanonical c f d' D' ∧
      LogPairIsLogCanonicalCenter c f d' D' Z ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V = Z) ∧
      (∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d' D') ↔ x ∈ Z) ∧
      ∀ (m : ℕ), b ≤ m → ∀ (_ : KawamataViehwegVanishingSNC K n),
        let I := Scheme.IdealSheafData.vanishingIdeal Z
        Subsingleton (Scheme.Modules.Cohomology ((m • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
          (∃ τ : (m • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
            ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf),
            Function.Surjective (Scheme.Modules.Hom.app τ ⊤)) ∧
          ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf, ⊤), t ≠ 0 →
            ∃ x : X, x ∈ Z ∧ x ∉ cartierBaseLocus (m • L) := by
  have hden : 1 ≤ e * d := Nat.mul_pos (by omega) (by omega)
  have hDs := (logPairBoundaryEffective_scale_denominator_iff c f d e he D).mpr hD
  have hAs : LogPairBoundaryEffective c f (e * d) (d • A) := by
    simpa only [Nat.mul_comm] using (logPairBoundaryEffective_scale_denominator_iff c f e d hd A).mpr hA
  have hklts : LogPairIsKlt c f (e * d) (d • A) := by
    simpa only [Nat.mul_comm] using (logPairIsKlt_scale_denominator_iff c f e d hd A).mpr hklt
  have hZs := (logPairIsLogCanonicalCenter_scale_denominator_iff c f d e he D Z).mpr hZ
  have hmins : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f (e * d) (e • D) V → V ≤ Z → V = Z := by
    intro V hV hVZ
    exact hmin V ((logPairIsLogCanonicalCenter_scale_denominator_iff c f d e he D V).mp hV) hVZ
  have hHs : CartierIsAmpleProj K (((e * d) * b) • L - e • D) := by
    have heq : ((e * d) * b) • L - e • D = e • ((d * b) • L - D) := by module
    rw [heq]
    exact cartierIsAmpleProj_nsmul hH he
  obtain ⟨d', hd', D', heff', hlc', hZ', hamp, hunique, hNK⟩ :=
    minimal_lc_center_klt_anchor_constructs_exact_nonKlt_isolation_with_unique_center K hn hnorm c f (e * d) hden (e • D) (d • A)
      hDs hAs hklts Z hZs hmins L hL b hHs
  refine ⟨d', hd', D', heff', hlc', hZ', hamp, hunique, hNK, fun m hm hKV => ?_⟩
  have hP : CartierIsAmpleProj K (d' • (m • L) - D') := by simpa only [smul_smul] using hamp m hm
  exact exact_nonKlt_lc_center_restriction_lifting_of_usual_KV K hn hnorm c f d' hd' D' heff' Z hZ' hNK
    ((d * b) • L - D) hH hKV (m • L) (cartierIsAmpleProj_isNef hP)
    (cartierIsAmpleProj_isBig (etaleChart_topologicalKrullDim c) hn hP)

end MixedFujita
