module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) :
    Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)

def half : AE F E := algebraMap (AF F) (AE F E) (⅟(2 : AF F))

def diagonalFixingDoublingMatrix (c : AE F E) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  1 + (half * c) • (dC F E d ⬝ₘ (GlobalTheory.InertDbl.antiCols d)ᵀ)

def splitDoublingNBlock {d : ℕ} (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  ((half : AE F E) * half * half) • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))

def nMat {d : ℕ} (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  1 + (GlobalTheory.InertDbl.antiCols d ⬝ₘ splitDoublingNBlock c K K') ⬝ₘ (dC F E d)ᵀ

def tMat {d : ℕ} (c : AE F E) (K : Matrix (Fin d) (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  1 + (half * (1 + c)) • (K - 1)

end GlobalTheory.SplitDblGen
end
