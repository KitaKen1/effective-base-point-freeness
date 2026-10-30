/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FormalConjecturesUtil

/-!
# Effective base point freeness

For a projective klt pair, $aD-(K_X+\Delta)$ nef and big should imply that
$(a+n+1)D$ is globally generated [Kol93, p.596].
The statements below concern complex projective pairs and integers $a\ge1$.

*References:*
- [Kol93] J. Kollár, *Effective base point freeness*, Math. Ann. 296 (1993),
  595–605, p.596 (after Theorem 1.1).
  https://doi.org/10.1007/BF01445123
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace EffectiveFreeness

/-- Cartier divisors represented by compatible local equations. -/
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

/-- The complex projective, integral $a\ge1$ case of [Kol93, p.596]. -/
@[category research open, AMS 14]
theorem kollar (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : Ample J)
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (f : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r) (D' : CartierDivisor X)
    (hΔ : EffectiveKlt b f r D') (D : CartierDivisor X) (hD : Nef D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : Nef ((r * a) • D - D'))
    (hbig : ∃ c : ℝ, 0 < c ∧ ∃ᶠ m : ℕ in atTop,
      c * (m : ℝ) ^ n ≤ Module.finrank ℂ (sectionSpace (m • ((r * a) • D - D')))) :
    GloballyGenerated ((a + n + 1) • D) := by
  sorry

namespace variants

open scoped Classical in
/-- The numerical variant, with $D\sim0$ when $\nu(D)=0$. -/
@[category research open, AMS 14]
theorem numerical (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : Ample J)
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (f : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r) (D' : CartierDivisor X)
    (hΔ : EffectiveKlt b f r D') (D : CartierDivisor X) (hD : Nef D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : Nef ((r * a) • D - D'))
    (hbig : ∃ c : ℝ, 0 < c ∧ ∃ᶠ m : ℕ in atTop,
      c * (m : ℝ) ^ n ≤ Module.finrank ℂ (sectionSpace (m • ((r * a) • D - D')))) :
    let ν := ((Finset.univ : Finset (Fin (n + 1))).filter fun k =>
      ∀ᶠ ℓ : ℕ in atTop, 0 < mixedDifference n k.val ℓ D J).sup Fin.val
    (∀ m : ℕ, a + ν + 1 ≤ m → GloballyGenerated (m • D)) ∧
    (ν = 0 → ∃ f : X.functionFieldˣ, ∀ x : X,
      (D.1 x).toMul / f ∈
        (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom).range) := by
  sorry

end variants

end EffectiveFreeness
