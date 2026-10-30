/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierAdjunctionOverlaps

/-! 実加群層写像の全部分開公式付き大域貼合せ。 check-288：元の周囲／切断etale被覆、有効Cartier因子の実局所正則方程式、閉埋め込みの実開持ち上げから、切断の全点に実随伴チャートを構成し全点被覆を証明。既存の層の一意貼合せで、任意の両立する実加群層写像を全部分開の正確な公式付きで大域化し、線形性・制限自然性も内部証明。元のCartier切断にこれを適用し、287の任意二チャート重なり一致とTauCetiの被覆上同型判定から、元のi^*O(K_X+D)とO(K_Y)の大域正規化Poincare留数層同型を存在・一意性付きで構成。実大域同型cartierGlobalAdjunctionIsoを定義し、各チャートへの制限が元の局所同型そのものであること、純dg留数と正確なcanonical frame単元による全部分開の正規化を証明。空開を含む。SNC反復随伴、正値性を伴う数値随伴、一般KV／BPF／F1F2は残る。 -/

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

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {D : CartierDivisor X} {hD : D.IsEffective}
  [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))]
  [(effectiveCartierIdealSheaf D hD).subschemeι.IsOver (Spec (CommRingCat.of K))]
  [IsIntegral (effectiveCartierIdealSheaf D hD).subscheme] {r : ℕ}



/-- Compatible ACTUAL module-sheaf maps on an open cover glue to an actual
module-sheaf map, with its exact formula on every subopen of every cover member. -/
theorem exists_moduleHom_of_compatible_over_cover
    {Z : Scheme.{u}} (M N : Z.Modules) {ι : Type u} (U : ι → Z.Opens)
    (hU : iSup U = ⊤) (f : ∀ j, M.over (U j) ⟶ N.over (U j))
    (hcompat : ∀ (i j : ι) (V : Z.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j) (s : Γ(M, V)),
      (f i).val.app (op (Over.mk (homOfLE hVi))) s =
        (f j).val.app (op (Over.mk (homOfLE hVj))) s) :
    ∃ F : M ⟶ N, ∀ (j : ι) (V : Z.Opens) (hVj : V ≤ U j) (s : Γ(M, V)),
      Scheme.Modules.Hom.app F V s = (f j).val.app (op (Over.mk (homOfLE hVj))) s := by
  classical
  have hnat (a : ι) {V W : Z.Opens} (hWU : W ≤ U a) (j : V ⟶ W) (s : Γ(M, W)) :
      (f a).val.app (op (Over.mk (homOfLE (j.le.trans hWU)))) (M.presheaf.map j.op s) =
        N.presheaf.map j.op ((f a).val.app (op (Over.mk (homOfLE hWU))) s) :=
    PresheafOfModules.naturality_apply (f a).val
      (Over.homMk j : Over.mk (homOfLE (j.le.trans hWU)) ⟶ Over.mk (homOfLE hWU)).op s
  let V (T : Z.Opens) (a : ι) : Z.Opens := T ⊓ U a
  have hcover (T : Z.Opens) : T ≤ iSup (V T) := by
    intro x hx
    have hxU : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxU
    exact Opens.mem_iSup.mpr ⟨a, hx, ha⟩
  let localValue (T : Z.Opens) (s : Γ(M, T)) (a : ι) : Γ(N, V T a) :=
    (f a).val.app (op (Over.mk (homOfLE (show V T a ≤ U a from inf_le_right))))
      (M.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op s)
  have hlocal (T : Z.Opens) (s : Γ(M, T)) :
      TopCat.Presheaf.IsCompatible N.presheaf (V T) (localValue T s) := by
    intro a b
    change N.presheaf.map (homOfLE (show V T a ⊓ V T b ≤ V T a from inf_le_left)).op
        (localValue T s a) =
      N.presheaf.map (homOfLE (show V T a ⊓ V T b ≤ V T b from inf_le_right)).op
        (localValue T s b)
    dsimp only [localValue]
    rw [← hnat a inf_le_right, ← hnat b inf_le_right]
    have hres : M.presheaf.map (homOfLE (show V T a ⊓ V T b ≤ V T a from inf_le_left)).op
        (M.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op s) =
      M.presheaf.map (homOfLE (show V T a ⊓ V T b ≤ V T b from inf_le_right)).op
        (M.presheaf.map (homOfLE (show V T b ≤ T from inf_le_left)).op s) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hres]
    exact hcompat a b (V T a ⊓ V T b) _ _ _
  have hex (T : Z.Opens) (s : Γ(M, T)) :
      ∃! t : Γ(N, T), ∀ a, N.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op t =
        localValue T s a :=
    TopCat.Sheaf.existsUnique_gluing' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Z)
      (V T) T (fun _a => homOfLE inf_le_left) (hcover T) (localValue T s) (hlocal T s)
  let value (T : Z.Opens) (s : Γ(M, T)) : Γ(N, T) := Classical.choose (hex T s)
  have hvalue (T : Z.Opens) (s : Γ(M, T)) (a : ι) :
      N.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op (value T s) = localValue T s a :=
    (Classical.choose_spec (hex T s)).1 a
  have huniq (T : Z.Opens) (s : Γ(M, T)) (t : Γ(N, T))
      (ht : ∀ a, N.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op t = localValue T s a) :
      t = value T s := (Classical.choose_spec (hex T s)).2 t ht
  have hadd (T : Z.Opens) (s t : Γ(M, T)) : value T (s + t) = value T s + value T t := by
    symm
    apply huniq
    intro a
    rw [map_add, hvalue, hvalue]
    dsimp only [localValue]
    rw [map_add, map_add]
  have hsmul (T : Z.Opens) (a : Γ(Z, T)) (s : Γ(M, T)) : value T (a • s) = a • value T s := by
    symm
    apply huniq
    intro j
    rw [N.map_smul, hvalue]
    dsimp only [localValue]
    rw [M.map_smul, map_smul]
  have hmap {T W : Z.Opens} (j : W ⟶ T) (s : Γ(M, T)) :
      value W (M.presheaf.map j.op s) = N.presheaf.map j.op (value T s) := by
    symm
    apply huniq
    intro a
    let k : V W a ⟶ V T a := homOfLE (inf_le_inf j.le le_rfl)
    calc
      _ = N.presheaf.map k.op
          (N.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op (value T s)) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      _ = N.presheaf.map k.op (localValue T s a) := by rw [hvalue]
      _ = (f a).val.app (op (Over.mk (homOfLE (show V W a ≤ U a from inf_le_right))))
          (M.presheaf.map k.op (M.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op s)) :=
        (hnat a inf_le_right k _).symm
      _ = localValue W (M.presheaf.map j.op s) a := by
        dsimp only [localValue]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
  let app (T : Z.Opens) : M.val.obj (op T) ⟶ N.val.obj (op T) :=
    { hom' := { toFun := value T, map_add' := hadd T, map_smul' := fun a s => hsmul T a s } }
  let F : M ⟶ N :=
    { val := { app := fun T => app T.unop
               naturality := fun {T W} j => by
                 ext s
                 exact hmap j.unop s } }
  refine ⟨F, ?_⟩
  intro a T hTa s
  have h := hvalue T s a
  let j : T ⟶ V T a := homOfLE (le_inf le_rfl hTa)
  have hc := congrArg (N.presheaf.map j.op) h
  have hn := hnat a inf_le_right j (M.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op s)
  change value T s = _
  have hl : N.presheaf.map j.op
      (N.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op (value T s)) = value T s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact N.presheaf.map_id_apply (op T) (value T s)
  have hr : M.presheaf.map j.op
      (M.presheaf.map (homOfLE (show V T a ≤ T from inf_le_left)).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact M.presheaf.map_id_apply (op T) s
  exact hl.symm.trans (hc.trans ((hn.symm.trans (congrArg (fun t =>
    (f a).val.app (op (Over.mk (homOfLE hTa))) t) hr))))

end MixedFujita
