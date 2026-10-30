/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalRoundupDirectImageCoherence
public import MixedFujita.IdealSheafModuleFunctor
public import SGA.Foundations.Cohomology.QuasiCoherentAbelian

/-! 局所Noether源の全実イデアルmoduleの内部連接性。 See reports/check-256-natural-center-concentration-extension.json for the verified scope. On proper integral targets a nonzero endomorphism of a Cartier line is an isomorphism, using the actual global-functions field and TauCeti global scalar action. Any section-surjective morphism to a restricted Cartier pushforward therefore implies surjectivity of the NATURAL restriction. Every actual ideal module on a locally Noetherian source is coherent. High ample powers restrict naturally and surjectively to integral closed sources and actual lc centers by unconditional Serre vanishing. In the positive restricted original numerical-dimension branch, all large powers of one original nef-ample pencil have nonzero ambient sections with naturally restricted sections of arbitrarily high linear order at every smooth closed point. No center normality, KV or initial original L-section is assumed. Original mL center lifting, appropriate center adjoint vanishing/nonvanishing, nu=0, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- EVERY ideal-sheaf module on a locally Noetherian scheme is coherent.
Quasi-coherence comes from the actual closed-immersion quotient kernel. -/
theorem locallyNoetherian_idealSheafDataModule_isCoherent
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    (idealSheafDataModule I).IsCoherent := by
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward I.subschemeι _
  let : (idealSheafDataModule I).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_kernel (schemeUnitToPushforwardUnit I.subschemeι)
  let := invertible_module_sheaf_isFiniteType (SheafOfModules.unit X.ringCatSheaf)
  exact quasicoherent_module_isCoherent_of_mono (idealSheafDataModuleInclusion I)

end MixedFujita
