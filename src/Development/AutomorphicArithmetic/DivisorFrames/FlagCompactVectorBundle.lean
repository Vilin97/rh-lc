import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AutomorphicArithmetic.DivisorFrames.ExistsChartTransition
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem tri_mul {K : Type} [CommRing K] {r : ℕ} {A B : Matrix (Fin r) (Fin r) K} (hA : IsTri A) (hB : IsTri B) :
    IsTri (A * B) := by
  have h : (A * B).BlockTriangular id :=
    BlockTriangular.mul (b := id) (fun _ _ h => hA _ _ h) (fun _ _ h => hB _ _ h)
  exact fun _ _ h' => h h'

private theorem tri_inv {K : Type} [CommRing K] {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (hA : IsTri A)
    (hu : IsUnit A.det) : IsTri A⁻¹ := by
  have := invertibleOfIsUnitDet A hu
  have h : A⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular fun _ _ h => hA _ _ h
  exact fun _ _ h' => h h'

private theorem unit_sub {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {A : Matrix (Fin r) (Fin r) K}
    (hu : IsUnit A.det) : IsUnit (A.submatrix (pos dual) id).det ∧ IsUnit (A.submatrix id (pos dual)).det := by
  cases dual
  · exact ⟨hu, hu⟩
  · constructor
    · change IsUnit (A.submatrix Fin.revPerm id).det
      rw [det_permute]
      exact (Units.isUnit _ |>.map (Int.castRingHom K)).mul hu
    · change IsUnit (A.submatrix id Fin.revPerm).det
      rw [det_permute']
      exact (Units.isUnit _ |>.map (Int.castRingHom K)).mul hu

private theorem tri_of_mul {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {A T : Matrix (Fin r) (Fin r) K}
    (hu : IsUnit A.det) (hA : IsTri (A.submatrix (pos dual) id)) (hA' : IsTri ((A * T).submatrix (pos dual) id)) :
    IsTri T := by
  have hu' := (unit_sub dual hu).1
  have e : (A * T).submatrix (pos dual) id = A.submatrix (pos dual) id * T := rfl
  have := tri_mul (tri_inv hA hu') hA'
  rwa [e, ← Matrix.mul_assoc, nonsing_inv_mul _ hu', Matrix.one_mul] at this
