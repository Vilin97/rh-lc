import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AutomorphicArithmetic.DivisorFrames.StalkMatrixLeftInverse
import Development.AutomorphicArithmetic.DivisorFrames.ExistsDivisorFrameGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_leftInv {R : Type} [CommRing R] [IsLocalRing R] {m g : ℕ} (a : Fin m → Fin g → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R) fun l i => IsLocalRing.residue R (a l i)) :
    ∃ a' : Matrix (Fin m) (Fin g) R, a' * (Matrix.of fun k l => a l k) = 1 := by
  obtain ⟨s, hs⟩ := GlobalTheory.LineNorm.Chart.exists_minor_ne_zero _ h le_rfl
  rw [← GlobalTheory.LineNorm.Chart.map_minor, IsLocalRing.residue_ne_zero_iff_isUnit] at hs
  let A : Matrix (Fin g) (Fin m) R := Matrix.of fun k l => a l k
  have hu : IsUnit (A.submatrix s id).det := by
    rw [← Matrix.det_transpose]; exact hs
  refine ⟨(A.submatrix s id)⁻¹ * (1 : Matrix (Fin g) (Fin g) R).submatrix s id, ?_⟩
  have e1 : (1 : Matrix (Fin g) (Fin g) R).submatrix s id * A = A.submatrix s id := by
    conv_rhs => rw [← Matrix.one_mul A]
    rfl
  rw [Matrix.mul_assoc]
  exact (congrArg _ e1).trans (Matrix.nonsing_inv_mul _ hu)

section SlopeTestRemainingChoices

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem isTanBasis_map {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X}
    {g : ℕ} {b : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x b) (β : R →+* S) :
    IsTanBasis t (spMap β ≫ x) fun i => spMap (dualMap β) ≫ b i := by
  refine ⟨fun i => GlobalTheory.LieMet.isTan_map _ rfl (h.1 i), fun T _ φ w hw => ?_⟩
  rw [← Category.assoc, spMap_comp'] at hw ⊢
  simp only [GlobalTheory.LineNorm.Chart.dual_comp]
  exact h.2 T _ w hw

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : Var F}
  {ρ : Y.X ⟶ gen Z}

omit [NumberField F] in

omit [NumberField F] in
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in

end SlopeTestRemainingChoices
