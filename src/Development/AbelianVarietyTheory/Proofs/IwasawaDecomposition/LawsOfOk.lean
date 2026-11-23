module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDecoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoicesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  first | exact @GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | exact GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | (intros; apply GlobalTheory.Mem.Col2.LevelLaw.atIn_ok <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditionsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_chains_satisfy_conditions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L := by
  first | exact @GlobalTheory.Mem.Col2.TC.ok_chains | exact GlobalTheory.Mem.Col2.TC.ok_chains | (intros; apply GlobalTheory.Mem.Col2.TC.ok_chains <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) := by
  first | exact @GlobalTheory.Mem.Col2.PerLaw.perIn_laws | exact GlobalTheory.Mem.Col2.PerLaw.perIn_laws | (intros; apply GlobalTheory.Mem.Col2.PerLaw.perIn_laws <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem laws_of_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws := by
  intro B X I h
  have hch := GlobalTheory.T.trueColumn_chains_satisfy_conditions I h
  have hlev := GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices I h
  have hper := GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (GlobalTheory.T.cl0_bijective_and_deco_eq I h u a b).1
      lat := fun u a => (hch u a).2.2 }

end GlobalTheory.Mem.Col2.TC
end
end
