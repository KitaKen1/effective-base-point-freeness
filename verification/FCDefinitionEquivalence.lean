/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FreeModule.Determinant
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Ring.Cast
@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace Before

variable {X : Scheme.{0}} [IsIntegral X]

/-- The units in the local ring, viewed as rational functions. -/
@[reducible]
noncomputable def localUnits (x : X) : Subgroup X.functionFieldˣ :=
  (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom).range

/-- Cartier divisors represented by compatible local equations. -/
@[reducible]
noncomputable def CartierDivisor (X : Scheme.{0}) [IsIntegral X] :
    AddSubgroup (X → Additive X.functionFieldˣ) where
  carrier D := ∀ x, ∃ U : X.Opens, x ∈ U ∧
    ∀ y ∈ U, (D y).toMul / (D x).toMul ∈ localUnits y
  zero_mem' := by
    intro x
    exact ⟨⊤, Opens.mem_top x, fun y _ => by simp⟩
  add_mem' := by
    intro D E hD hE x
    obtain ⟨U, hxU, hU⟩ := hD x
    obtain ⟨V, hxV, hV⟩ := hE x
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun y hy => ?_⟩
    simpa only [Pi.add_apply, toMul_add, mul_div_mul_comm] using
      (localUnits y).mul_mem (hU y hy.1) (hV y hy.2)
  neg_mem' := by
    intro D hD x
    obtain ⟨U, hxU, hU⟩ := hD x
    refine ⟨U, hxU, fun y hy => ?_⟩
    simpa only [Pi.neg_apply, toMul_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using
      (localUnits y).inv_mem (hU y hy)

/-- A chosen local equation of a Cartier divisor. -/
def equation (D : CartierDivisor X) (x : X) : X.functionFieldˣ :=
  (D.1 x).toMul

variable [X.Over (Spec (CommRingCat.of ℂ))]

/-- Complex scalars act through the structure morphism. -/
@[reducible]
noncomputable instance stalkAlgebra (x : X) : Algebra ℂ (X.presheaf.stalk x) :=
  (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X ↘ Spec (.of ℂ)).appTop ≫
    X.presheaf.germ ⊤ x (Opens.mem_top x)).hom).toAlgebra

/-- The complex algebra structure on the function field. -/
@[reducible]
noncomputable instance functionFieldAlgebra : Algebra ℂ X.functionField :=
  stalkAlgebra (genericPoint X)

instance stalkScalarTower (x : X) : IsScalarTower ℂ (X.presheaf.stalk x) X.functionField :=
  IsScalarTower.of_algebraMap_eq fun z => by
    let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, Opens.mem_top x⟩⟩
    change X.germToFunctionField ⊤ _ =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ ⊤ x _ _)
    exact (X.algebraMap_germ_eq_germToFunctionField (Opens.mem_top x) _).symm

/-- The rational sections of $\mathcal O_X(D)$. -/
noncomputable def sectionSpace (D : CartierDivisor X) : Submodule ℂ X.functionField where
  carrier := {f | ∀ x, f * (equation D x : X.functionField) ∈
    (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro f g hf hg x
    simpa only [add_mul] using
      (algebraMap (X.presheaf.stalk x) X.functionField).range.add_mem (hf x) (hg x)
  smul_mem' := by
    intro z f hf x
    obtain ⟨a, ha⟩ := hf x
    refine ⟨algebraMap ℂ (X.presheaf.stalk x) z * a, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply ℂ (X.presheaf.stalk x) X.functionField, ha]
    simp only [Algebra.smul_def, mul_assoc]

/-- Every point admits a global section that is a local generator. -/
def GloballyGenerated (D : CartierDivisor X) : Prop :=
  ∀ x, ∃ f : sectionSpace D, ∃ u : (X.presheaf.stalk x)ˣ,
    algebraMap (X.presheaf.stalk x) X.functionField u = f.1 * equation D x

/-- Positive powers have sections whose affine nonvanishing loci cover $X$. -/
def Ample (D : CartierDivisor X) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (m : ℕ) (_ : 1 ≤ m) (f : sectionSpace (m • D))
    (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X,
      y ∈ U ↔ ∃ u : (X.presheaf.stalk y)ˣ,
        algebraMap (X.presheaf.stalk y) X.functionField u = f.1 * equation (m • D) y

/-- Adding any positive integral multiple of $D$ preserves ampleness. -/
def Nef (D : CartierDivisor X) : Prop :=
  ∀ A : CartierDivisor X, Ample A → ∀ m : ℕ, Ample (A + m • D)

/-- Local regular top forms, expressed relative to a rational differential basis. -/
noncomputable def canonicalLattice {n : ℕ}
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ]) (x : X) :
    Submodule (X.presheaf.stalk x) X.functionField :=
  Submodule.span (X.presheaf.stalk x) (Set.range fun a : Fin n → X.presheaf.stalk x =>
    b.det (fun i => KaehlerDifferential.D ℂ X.functionField
      (algebraMap (X.presheaf.stalk x) X.functionField (a i))))

/-- $K$ is the divisor of the wedge of the rational basis $b$. -/
def IsCanonical {n : ℕ} (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (K : CartierDivisor X) : Prop :=
  ∀ x : X, canonicalLattice b x =
    Submodule.span (X.presheaf.stalk x) {(equation K x : X.functionField)⁻¹}

variable {T : Scheme.{0}} [IsIntegral T] [T.Over (Spec (CommRingCat.of ℂ))]

/-- The change of rational volume form under a function-field isomorphism. -/
noncomputable def relativeJacobian {n : ℕ} (γ : X.functionField ≃ₐ[ℂ] T.functionField)
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (c : Module.Basis (Fin n) T.functionField Ω[T.functionField⁄ℂ]) : T.functionField :=
  letI : Algebra X.functionField T.functionField := γ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ X.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq fun z => (γ.commutes z).symm
  c.det (fun i => KaehlerDifferential.map ℂ ℂ X.functionField T.functionField (b i))

/-- $\Delta=D'/r-\operatorname{div}(f\bigwedge b)$ is effective and klt. -/
def EffectiveKlt [IsLocallyNoetherian X] {n : ℕ}
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (f : X.functionFieldˣ) (r : ℕ) (D' : CartierDivisor X) : Prop :=
  (∀ (x : X), Order.coheight x = 1 → ∀ u : X.functionFieldˣ,
    canonicalLattice b x = Submodule.span (X.presheaf.stalk x) {(u : X.functionField)} →
    (r : ℤ) * X.ord ((f : X.functionField) / u) x ≤ X.ord (equation D' x) x) ∧
  ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of ℂ))]
    [SmoothOfRelativeDimension n (Y ↘ Spec (.of ℂ))]
    (π : Y ⟶ X) [IsDominant π] [IsProper π] [π.IsOver (Spec (.of ℂ))]
    (γ : X.functionField ≃ₐ[ℂ] Y.functionField),
    (∀ (y : Y) (a : X.presheaf.stalk (π y)),
      γ (algebraMap (X.presheaf.stalk (π y)) X.functionField a) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (π.stalkMap y a)) →
    ∀ (c : Module.Basis (Fin n) Y.functionField Ω[Y.functionField⁄ℂ]) (y : Y),
      Order.coheight y = 1 → ∀ u : Y.functionFieldˣ,
      canonicalLattice c y = Submodule.span (Y.presheaf.stalk y) {(u : Y.functionField)} →
      -(r : ℤ) < (r : ℤ) * Y.ord
        (γ f * relativeJacobian γ b c / u) y - Y.ord (γ (equation D' (π y))) y

/-- For large $\ell$, this finite difference is the intersection number $D^kJ^{n-k}$. -/
noncomputable def mixedDifference (n k ℓ : ℕ) (D J : CartierDivisor X) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (n - k + 1),
    (-1 : ℤ) ^ (n - i - j) * (Nat.choose k i : ℤ) * Nat.choose (n - k) j *
      (Module.finrank ℂ (sectionSpace (i • D + (ℓ + j) • J)) : ℤ)


end Before
@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace After

/-- Cartier divisors represented by compatible local equations. -/
@[reducible]
noncomputable def CartierDivisor (X : Scheme.{0}) [IsIntegral X] :
    AddSubgroup (X → Additive X.functionFieldˣ) :=
  let units (x : X) : Subgroup X.functionFieldˣ :=
    (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom).range
  { carrier D := ∀ x, ∃ U : X.Opens, x ∈ U ∧
      ∀ y ∈ U, (D y).toMul / (D x).toMul ∈ units y
    zero_mem' := by
      intro x
      exact ⟨⊤, Opens.mem_top x, fun y _ => by simp⟩
    add_mem' := by
      intro D E hD hE x
      obtain ⟨U, hxU, hU⟩ := hD x
      obtain ⟨V, hxV, hV⟩ := hE x
      refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun y hy => ?_⟩
      simpa only [Pi.add_apply, toMul_add, mul_div_mul_comm] using
        (units y).mul_mem (hU y hy.1) (hV y hy.2)
    neg_mem' := by
      intro D hD x
      obtain ⟨U, hxU, hU⟩ := hD x
      refine ⟨U, hxU, fun y hy => ?_⟩
      simpa only [Pi.neg_apply, toMul_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using
        (units y).inv_mem (hU y hy) }

@[reducible]
noncomputable instance functionFieldAlgebra {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] : Algebra ℂ X.functionField :=
  (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X ↘ Spec (.of ℂ)).appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _)).hom).toAlgebra

noncomputable def sectionSpace {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (D : CartierDivisor X) :
    Submodule ℂ X.functionField :=
  Submodule.span ℂ {f | ∀ x, f * ((D.1 x).toMul : X.functionField) ∈
    (algebraMap (X.presheaf.stalk x) X.functionField).range}

def GloballyGenerated {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (D : CartierDivisor X) : Prop :=
  ∀ x, ∃ f : sectionSpace D, ∃ u : (X.presheaf.stalk x)ˣ,
    algebraMap (X.presheaf.stalk x) X.functionField u = f.1 * (D.1 x).toMul

/-- Ampleness via affine nonvanishing loci of positive powers. -/
def Ample {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (D : CartierDivisor X) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (m : ℕ) (_ : 1 ≤ m) (f : sectionSpace (m • D))
    (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X,
      y ∈ U ↔ ∃ u : (X.presheaf.stalk y)ˣ,
        algebraMap (X.presheaf.stalk y) X.functionField u = f.1 * ((m • D).1 y).toMul

/-- Nefness via ampleness of $A+mD$ for every ample $A$ and $m\ge0$. -/
def Nef {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (D : CartierDivisor X) : Prop :=
  ∀ A : CartierDivisor X, Ample A → ∀ m : ℕ, Ample (A + m • D)

/-- Effectivity and discrepancy $>-1$ for $\Delta=D'/r-\operatorname{div}(f\bigwedge b)$. -/
def EffectiveKlt {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of ℂ))] {n : ℕ}
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (f : X.functionFieldˣ) (r : ℕ) (D' : CartierDivisor X) : Prop :=
  let volume {T : Scheme.{0}} [IsIntegral T] [T.Over (Spec (CommRingCat.of ℂ))]
      (c : Module.Basis (Fin n) T.functionField Ω[T.functionField⁄ℂ]) (x : T) :=
    Submodule.span (T.presheaf.stalk x) (Set.range fun a : Fin n → T.presheaf.stalk x =>
      c.det (fun i => KaehlerDifferential.D ℂ T.functionField
        (algebraMap (T.presheaf.stalk x) T.functionField (a i))))
  let jacobian {T : Scheme.{0}} [IsIntegral T] [T.Over (Spec (CommRingCat.of ℂ))]
      (γ : X.functionField ≃ₐ[ℂ] T.functionField)
      (c : Module.Basis (Fin n) T.functionField Ω[T.functionField⁄ℂ]) :=
    letI : Algebra X.functionField T.functionField := γ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ X.functionField T.functionField :=
      IsScalarTower.of_algebraMap_eq fun z => (γ.commutes z).symm
    c.det (fun i => KaehlerDifferential.map ℂ ℂ X.functionField T.functionField (b i))
  (∀ (x : X), Order.coheight x = 1 → ∀ u : X.functionFieldˣ,
    volume b x = Submodule.span (X.presheaf.stalk x) {(u : X.functionField)} →
    (r : ℤ) * X.ord ((f : X.functionField) / u) x ≤ X.ord (D'.1 x).toMul x) ∧
  ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of ℂ))]
    [SmoothOfRelativeDimension n (Y ↘ Spec (.of ℂ))]
    (π : Y ⟶ X) [IsDominant π] [IsProper π] [π.IsOver (Spec (.of ℂ))]
    (γ : X.functionField ≃ₐ[ℂ] Y.functionField),
    (∀ (y : Y) (a : X.presheaf.stalk (π y)),
      γ (algebraMap (X.presheaf.stalk (π y)) X.functionField a) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (π.stalkMap y a)) →
    ∀ (c : Module.Basis (Fin n) Y.functionField Ω[Y.functionField⁄ℂ]) (y : Y),
      Order.coheight y = 1 → ∀ u : Y.functionFieldˣ,
      volume c y = Submodule.span (Y.presheaf.stalk y) {(u : Y.functionField)} →
      -(r : ℤ) < (r : ℤ) * Y.ord (γ f * jacobian γ c / u) y -
        Y.ord (γ (D'.1 (π y)).toMul) y

/-- For large $\ell$, this finite difference is $D^kJ^{n-k}$. -/
noncomputable def mixedDifference {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n k ℓ : ℕ) (D J : CartierDivisor X) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (n - k + 1),
    (-1 : ℤ) ^ (n - i - j) * (Nat.choose k i : ℤ) * Nat.choose (n - k) j *
      (Module.finrank ℂ (sectionSpace (i • D + (ℓ + j) • J)) : ℤ)


end After

open AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{0}) [IsIntegral X] [X.Over (Spec (CommRingCat.of ℂ))]
example : Before.CartierDivisor X = After.CartierDivisor X := rfl
lemma sections (D : Before.CartierDivisor X) :
    After.sectionSpace D = Before.sectionSpace D := by
  change Submodule.span ℂ (Before.sectionSpace D : Set X.functionField) = Before.sectionSpace D
  exact Submodule.span_eq (Before.sectionSpace D)
example (D : Before.CartierDivisor X) :
    After.GloballyGenerated D ↔ Before.GloballyGenerated D := by
  unfold After.GloballyGenerated Before.GloballyGenerated
  rw [sections X D]
  rfl
lemma ample (D : Before.CartierDivisor X) : After.Ample D ↔ Before.Ample D := by
  change (CompactSpace X ∧ ∀ x : X, ∃ (m : ℕ) (_ : 1 ≤ m)
    (f : After.sectionSpace (m • D : Before.CartierDivisor X)) (U : X.Opens),
    x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X, y ∈ U ↔ ∃ u : (X.presheaf.stalk y)ˣ,
      algebraMap (X.presheaf.stalk y) X.functionField u = f.1 * Before.equation (m • D) y) ↔
    (CompactSpace X ∧ ∀ x : X, ∃ (m : ℕ) (_ : 1 ≤ m)
    (f : Before.sectionSpace (m • D)) (U : X.Opens),
    x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X, y ∈ U ↔ ∃ u : (X.presheaf.stalk y)ˣ,
      algebraMap (X.presheaf.stalk y) X.functionField u = f.1 * Before.equation (m • D) y)
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply exists_congr
  intro m
  apply exists_congr
  intro hm
  rw [sections X (m • D)]
example (D : Before.CartierDivisor X) : After.Nef D ↔ Before.Nef D := by
  constructor
  · intro h A hA m
    exact (ample X (A + m • D)).mp (h A ((ample X A).mpr hA) m)
  · intro h (A : Before.CartierDivisor X) hA m
    exact (ample X (A + m • D)).mpr (h A ((ample X A).mp hA) m)
example (n k ℓ : ℕ) (D J : Before.CartierDivisor X) :
    After.mixedDifference n k ℓ D J = Before.mixedDifference n k ℓ D J := by
  change (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (n - k + 1),
    (-1 : ℤ) ^ (n - i - j) * (Nat.choose k i : ℤ) * Nat.choose (n - k) j *
      (Module.finrank ℂ (After.sectionSpace
        (i • D + (ℓ + j) • J : Before.CartierDivisor X)) : ℤ)) = _
  unfold Before.mixedDifference
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sections X (i • D + (ℓ + j) • J)]
variable [IsLocallyNoetherian X]
example {n : ℕ} (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (f : X.functionFieldˣ) (r : ℕ) (D' : Before.CartierDivisor X) :
    After.EffectiveKlt b f r D' ↔ Before.EffectiveKlt b f r D' := Iff.rfl
