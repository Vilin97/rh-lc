module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
public import GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb

@[expose] public section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LeviRed

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rE (s : ℝ) : AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E) (GlobalTheory.TorusTheta.infScale F s)

omit [NumberField E] in
theorem rE_mul (a b : ℝ) : rE F E (a * b) = rE F E a * rE F E b := by
  rw [rE, rE, rE, ← map_mul]
  congr 1
  refine Prod.ext ?_ (mul_one _).symm
  show _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
  rw [← map_mul, ← map_mul]
  rfl

omit [NumberField E] in
theorem rE_one : rE F E 1 = 1 := by
  rw [rE, ← map_one (algebraMap (AF F) (AF F ⊗[F] E))]
  congr 1
  simp only [GlobalTheory.TorusTheta.infScale, map_one]
  rfl

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

variable {F E} (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

end GlobalTheory.LeviRed
