module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
public import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicPAdicPointLifts
public import Development.AutomorphicArithmetic.DivisorFrames.LevelReductionTorsionCharacter
public import Development.AutomorphicArithmetic.DivisorFrames.TateModulePairingCongruence
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

private theorem comp_pow' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

private theorem norm_le_of_mem {p : ℕ} [Fact p.Prime] {n : ℕ} {y : 𝓞_ℂ_[p]}
    (hmem : y ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] y‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨d, hd'⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [← hd', map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  have e2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  rw [e2]
  have e3 : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] d‖ ≤ 1 := (GlobalTheory.PadicComplexHost.mem_iff_norm _ _).1 d.2
  exact mul_le_of_le_one_left (by positivity) e3
