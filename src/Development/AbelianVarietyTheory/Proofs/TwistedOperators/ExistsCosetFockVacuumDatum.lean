module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalfStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRepresentativesHalfQuotientPairingTrivialD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSumStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExistsStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.PairLift (adjO)
noncomputable section
namespace GlobalTheory.ExchLatPf

theorem exchLat : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  intro D hOff T L μ0 hLi sc G W M hM hEx hLat i hi r r' hr hr' g hg
  have hAdj := GlobalTheory.AdjLawPf.adjLaw D W.ψ W.ψ_std (G.V (.core i)) (G.V (.core (i+1)))
  have hE := (hEx W.ψ (G.V (.core i)) (G.V (.core (i+1))) W.ψ_std).2.1
  have hL := hLat D hOff T L μ0 hLi sc G W M hM i hi r r' hr hr' (fun _ => True)
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · refine (hE _ _).trans (congrArg _ ?_)
    have h2 : adjO (G.V (.core i)) (G.V (.core (i+1))) (2 • u) = 2 • adjO (G.V (.core i)) (G.V (.core (i+1))) u := by
      rw [two_smul, two_smul, hAdj.add]
    rw [h2]
    exact hg.1 _ ((hL u).1 hu)
  · refine (hE _ _).trans (congrArg _ ?_)
    exact hg.2 (cA D e) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isSplitIdem_cA he) _ ((hL u).1 hu) (hAdj.half e u hue)

end GlobalTheory.ExchLatPf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChainStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  first | exact @GlobalTheory.ExchLatPf.exchLat | exact GlobalTheory.ExchLatPf.exchLat | (intros; apply GlobalTheory.ExchLatPf.exchLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coreChain_adjoint_latticeExchange : LatExch := by
  first | exact @GlobalTheory.LatExchPf.latExch | exact GlobalTheory.LatExchPf.latExch | (intros; apply GlobalTheory.LatExchPf.latExch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUniqueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotentSum_over_finite_places_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  first | exact @GlobalTheory.IdemSumUniq.idemSum_unique | exact GlobalTheory.IdemSumUniq.idemSum_unique | (intros; apply GlobalTheory.IdemSumUniq.idemSum_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombination

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombFockTranslate

theorem isFockVacAt_comb : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  intro D ψ θ S T hψ hθ J τ g hg hv ι R c t ht
  exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ g hg τ J hv ι R t c ht

end GlobalTheory.CombFockTranslate

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombinationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.CombFockTranslate.isFockVacAt_comb | exact GlobalTheory.CombFockTranslate.isFockVacAt_comb | (intros; apply GlobalTheory.CombFockTranslate.isFockVacAt_comb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | exact GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | (intros; apply GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CosDatum in
theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hLE : LatExch := GlobalTheory.T.coreChain_adjoint_latticeExchange
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'
    exact GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
end
end
