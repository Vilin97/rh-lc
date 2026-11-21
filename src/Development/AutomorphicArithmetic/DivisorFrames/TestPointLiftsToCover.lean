import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

open GlobalTheory.LineNorm.Chart in
private theorem chart' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (β : Γ(S, U) →+* O)
    (hβ : spMap β ≫ hU.fromSpec = yt) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    (∀ r, ψ (α r) = ioO.comp β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap (ioO.comp β)) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

private theorem val_sum {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] (z : Sp K ⟶ Z) {M : ℕ}
    (c : Fin M → Z.functionField) (hc : ∀ k, RegAt (below z) (c k)) (b : Fin M → Z.presheaf.stalk (below z)) :
    TrueGeo.valAt z (∑ k, c k * algebraMap _ Z.functionField (b k)) =
      ∑ k, TrueGeo.valAt z (c k) * (Scheme.stalkClosedPointTo z).hom (b k) := by
  choose c' hc' using hc
  simp only [← hc', ← map_mul, ← map_sum, Res.valAt_algebraMap]

open GlobalTheory.LineNorm.Chart in
