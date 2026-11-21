module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem glue {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (κ : X.functionField →+* K) {U : X.Opens}
    (hU : genericPoint X ∈ U) {m : ℕ} (T₀ : Matrix (Fin m) (Fin m) K)
    (h : ∀ x ∈ U, ∃ T : Matrix (Fin m) (Fin m) (X.presheaf.stalk x),
      T₀ = T.map (κ.comp (algebraMap _ X.functionField))) :
    ∃ T : Matrix (Fin m) (Fin m) Γ(X, U), T₀ = T.map (κ.comp (fnOf U hU)) := by
  obtain ⟨T₁, h₁⟩ : ∃ T₁ : Matrix (Fin m) (Fin m) X.functionField, T₀ = T₁.map κ :=
    have ⟨T₁, h₁⟩ := h _ hU
    ⟨_, h₁.trans (Matrix.map_map).symm⟩
  have key (a b : Fin m) : ∃ s : Γ(X, U), fnOf U hU s = T₁ a b :=
    exists_fnOf_eq hU fun x hx => by
      obtain ⟨T, hT⟩ := h x hx
      exact ⟨T a b, κ.injective (congrFun (congrFun (hT.symm.trans h₁) a) b)⟩
  choose s hs using key
  refine ⟨Matrix.of s, h₁.trans ?_⟩
  ext a b
  exact congrArg κ (hs a b).symm
