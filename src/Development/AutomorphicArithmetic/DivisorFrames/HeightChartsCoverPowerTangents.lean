import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AutomorphicArithmetic.DivisorFrames.CutLatticeNormBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem small {p : ℕ} [Fact p.Prime] {n : ℕ} {δ c : ℂ_[p]} (hδ : δ ≠ 0)
    (hn : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ n * ‖δ‖) (hc : ‖δ * p * c‖ ≤ (p : ℝ)⁻¹ ^ n) : ‖c‖ ≤ (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have := PadicComplex.norm_extends' (p := p) (p : ℚ_[p])
    simpa using this
  rw [norm_mul, norm_mul, hpn, inv_pow, ← one_div ((p : ℝ) ^ n), le_div_iff₀ (by positivity)] at hc
  have h1 : (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ * ‖c‖) ≤ 1 := by
    calc _ ≤ ((p : ℝ) ^ n * ‖δ‖) * ((p : ℝ)⁻¹ * ‖c‖) := by gcongr
      _ = ‖δ‖ * (p : ℝ)⁻¹ * ‖c‖ * (p : ℝ) ^ n := by ring
      _ ≤ 1 := hc
  have h2 : (p : ℝ) ^ 2 * ((p : ℝ)⁻¹ * ‖c‖) = ‖c‖ * p := by field_simp
  rw [← one_div, le_div_iff₀ hp0]
  linarith
