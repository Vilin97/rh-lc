module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemicharaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r) f₀ = alV D.host.d sc (embH (tauE D) δ y') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀ := by
  first | exact @GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq | exact GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq | (intros; apply GlobalTheory.ConjHalfHeis.heisO_conjHalf_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  first | exact @GlobalTheory.AdForm.HalfPairing.char_sympl_halfB | exact GlobalTheory.AdForm.HalfPairing.char_sympl_halfB | (intros; apply GlobalTheory.AdForm.HalfPairing.char_sympl_halfB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfFourier

theorem thetaAt_eq_sum_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  intro D ψ S T e Λ f₀ Φ f ι s K xs ys k hk hθ hx hy hΛ hΦ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac

  set g : ι → WO S T → ℂ := fun i t => ψ (symplO S T t (ys i)) * halfInd e Λ t with hg
  have hhalf : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := by
    intro t ht
    by_contra h
    exact ht (by simp [halfInd, h])
  have hSB : ∀ i ∈ s, IsSBHalf e Λ (g i) := by
    intro i hi
    refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
    · exact (hhalf t (right_ne_zero_of_mul ht)).2
    · have hku : k • u ∈ Λ := Λ.nsmul_mem hu k
      have hkh : IsHalf e (k • u) := by
        intro a b
        change e * ((k • u : Matrix _ _ (AE D)) a b) = (k • u : Matrix _ _ (AE D)) a b
        rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh a b]
      have hind : halfInd e Λ (t + k • u) = halfInd e Λ t := by
        have : (t + k • u ∈ Λ ∧ IsHalf e (t + k • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
          rw [Λ.add_mem_cancel_right hku]
          refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
          rw [Matrix.add_apply, mul_add, hkh a b, add_left_inj]
        simp only [halfInd, this]
      simp only [hg, hind, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hΛ i hi u hu, mul_one]
    · exact Λ.nsmul_mem (hhalf t (right_ne_zero_of_mul ht)).1 k
  have hΦ' : Φ = ∑ i ∈ s, K i • fun t => g i (t + xs i) := by
    funext t
    rw [hΦ t, Finset.sum_apply]
    rfl

  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hTm.trans _ (hSB i hi) (xs i) (hx i hi)]
  congr 2
  have : g i = fun t => ψ (symplO S T t (ys i)) * halfInd e Λ t := rfl
  rw [this, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) (ys i) (hy i hi), hvac]

end GlobalTheory.HalfFourier
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  first | exact @GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | exact GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | (intros; apply GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalTheta

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumRead

theorem reads_datum_eq_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT f₀ Φ f Ξ hV hSB hTh hΦ hΞ1 hΞ2
  classical
  obtain ⟨ΛS, hΛS, hΛS'⟩ := id hdS
  obtain ⟨ΛT, hΛT, hΛT'⟩ := id hdT
  obtain ⟨hRX, hRA, hRB⟩ := GlobalTheory.T.periodLatticeHalves_reps_finite_index D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa
  set SX := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSXd
  set SA := repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)
    (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSAd
  set SB := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSBd
  set MA := halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  set MB := halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  have hpx : ∀ x ∈ SX, ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x := fun x hx => by
    obtain ⟨x', hx', h⟩ := AddSubgroup.mem_map.1 (hRX.1 x hx)
    exact ⟨x', hx', h⟩
  have hpy : ∀ y ∈ SB, ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y := fun y hy => by
    obtain ⟨y', hy', h⟩ := AddSubgroup.mem_map.1 (hRB.1 y hy)
    exact ⟨y', hy', h⟩
  let px : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun x =>
    if h : ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x then h.choose else 0
  let py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun y =>
    if h : ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y then h.choose else 0
  have hpx' : ∀ x ∈ SX, px x ∈ MA ∧ embH (tauE D) δ (px x) = x := fun x hx => by
    simp only [px, dif_pos (hpx x hx)]; exact (hpx x hx).choose_spec
  have hpy' : ∀ y ∈ SB, py y ∈ MB ∧ embH (tauE D) δ (py y) = y := fun y hy => by
    simp only [py, dif_pos (hpy y hy)]; exact (hpy y hy).choose_spec
  let mt : Formalism.L2.Col.HomE D.host.E a b → Matrix (Fin T.rank) (Fin S.rank) D.host.E := fun x =>
    (LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)
  have hmt : ∀ x, toHom S T hS hT (mt x) = x := fun x => by
    simp only [mt]
    unfold toHom
    have h : ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)).reindex (finCongr hT) (finCongr hS) =
        LinearMap.toMatrix' x := by
      ext i j; simp [Matrix.reindex_apply]
    rw [h, Matrix.toLin'_toMatrix']
  let K : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - p.1) * (brk (HV sc) p.2 s)⁻¹
  have hF := GlobalTheory.T.finite_fourier_expansion_half_split_places D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx' hpy'
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hf1 : f = ∑ p ∈ SX ×ˢ SB, K p • heisO ψ S T ((mt (px p.1)).map fun r => e * incA D r)
      (heisO ψ S T ((mt (py p.2)).map fun r => cA D e * incA D r) f₀) := by
    refine GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates D ψ S T e _ f₀ Φ f _ (SX ×ˢ SB) K (fun p => (mt (px p.1)).map fun r => e * incA D r)
      (fun p => (mt (py p.2)).map fun r => cA D e * incA D r) c hc hTh ?_ ?_ ?_ ?_
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, hee]
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
    · intro p hp u hu
      exact GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT (py p.2) (hpy' _ (Finset.mem_product.1 hp).2).1 u hu
    · intro t
      rw [hF t, Finset.sum_product]

  have hV' := hV
  obtain ⟨hstd, hvac⟩ := hV'
  have h0 : IsThetaFunO ψ S T f₀ := hvac.theta
  have hψ : IsCharAF D.host.F ψ := hstd.1
  set G : VV D.what₂.Tau a b × VV D.what₂.Tau a b → WO S T := fun p =>
    GlobalTheory.VacUnique.finRat S T (mt (px p.1)) + GlobalTheory.VacUnique.finRat S T (mt (py p.2)) with hG
  set C : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    K p * (alV D.host.d sc p.1 * alV D.host.d sc p.2) with hC
  have hf2 : f = ∑ p ∈ SX ×ˢ SB, C p • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) := by
    rw [hf1]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
    rw [GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (py p.2) (hpy' _ h2').1,
      GlobalTheory.LatVac.heisO_smul,
      GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (px p.1) (hpx' _ h1).1 (py p.2) (hpy' _ h2').1,
      (hpx' _ h1).2, (hpy' _ h2').2, smul_smul, smul_smul, hC]
    congr 1
    ring
  have hf3 : f = ∑ p ∈ SX ×ˢ SB, (C p * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (GlobalTheory.VacUnique.finRat S T (mt (py p.2))))) • heisO ψ S T (G p) f₀ := by
    rw [hf2]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LatVac.heisO_heisO, smul_smul]
  have hGi : ∀ p ∈ SX ×ˢ SB, (G p).map (infPart D) = 0 := fun p _ => by
    simp only [hG, ← map_add (f := _)]
    exact GlobalTheory.VacUnique.finRat_inf S T _
  refine ⟨⟨?_, fun τ => ?_⟩, ?_⟩
  · rw [hf3]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ h0 _ _ G _ hGi
  · rw [hf3]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ hP.inf f₀ h0 τ _ (hvac.fock τ) _ _ G _ hGi
  · have hread : ∀ p ∈ SX ×ˢ SB, xiN θ S T hS hT δ sc (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) =
        Formalism.L2.Th1.H.opU (HV sc) p.1 (Formalism.L2.Th1.H.opU (HV sc) p.2 (xiN θ S T hS hT δ sc f₀)) := by
      intro p hp
      obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
      have hfin : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.VacUnique.finRat S T γ) := fun γ =>
        ⟨GlobalTheory.VacUnique.finRat_inf S T γ, GlobalTheory.VacUnique.finRat_fin S T γ⟩
      have ht1 : IsThetaFunO ψ S T (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) :=
        GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.VacUnique.finRat_inf S T _) h0
      rw [GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ ht1 _ _ (hfin _), GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ h0 _ _ (hfin _),
        hmt, hmt, (hpx' _ h1).2, (hpy' _ h2').2]
    funext z
    have hlin : xiN θ S T hS hT δ sc f z = ∑ p ∈ SX ×ˢ SB, C p * xiN θ S T hS hT δ sc
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
          (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) z := by
      rw [hf2]
      simp only [xiN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hlin]
    rw [Finset.sum_congr rfl fun p hp => by rw [hread p hp]]
    show _ = xiL (HV sc) (alV D.host.d sc) 1 SX SA SB (onV (tauE D) δ Ξ) (xiN θ S T hS hT δ sc f₀) z
    rw [GlobalTheory.ThetaCosetSum.xiL_eq_kernel, Finset.sum_product]
    simp only [hC, K, Formalism.L2.Th1.H.opU, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
    ring

end GlobalTheory.AdForm.DatumRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalThetaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  first | exact @GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC | exact GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC | (intros; apply GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalTheta

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf.CoreG

theorem om_inv_om {D : D7} (S T : HSp D) (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (g⁻¹, h⁻¹) (om (g, h) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
  rfl

theorem selfDual_latFr {D : D7} (V : HSp D) (hV : V.gram = 1) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hN : Moves V hn g N) :
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), IsSelfDualC V Λ ∧
      (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N := by
  subst hn
  exact ⟨N, GlobalTheory.SplitMove.selfDual_move V hV g N hN, rfl⟩

theorem thC_const_mul (D : D7) {a b : ℕ} (δ : ℂ) (sc : ℝ) (SS : Finset (Formalism.L2.DIV.Pl D.host.E))
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ)
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ) :
    thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (fun z => κ * E z) =
      fun z => κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
  funext z
  simp only [thC, xiV, xiL, xiS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.KJInf.CoreG

namespace GlobalTheory.KJInf.CoreG

theorem thetaKernel_eq_jet_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  intro D ψ θ S T a b hS hT δ sc hP s hs μ om hW e SS hE vac Φ w hV hSB hTh g hg h hh N N' hN hN' c hc hcP h2 hLa Ξ hΦ hΞ1 hΞ2 κ E hκ P
  obtain ⟨hSBm, hThm⟩ := GlobalTheory.SplitMove.isThetaAt_move D ψ θ S T a b hS hT δ sc hP μ om hW e SS hE vac Φ w hV.2.theta hV.2.lat
    hSB hTh g hg h hh N N' hN hN'
  obtain ⟨hVm, -, -⟩ := GlobalTheory.MovedVac.vac_moved D ψ θ S T a b hS hT δ sc hP μ om hW vac hV g hg h hh N N' hN hN'
  have hD : IsHol θ S T ψ (om (g, h) w) ∧ xiN θ S T hS hT δ sc (om (g, h) w) =
      thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc (om (g, h) vac)) := by
    exact GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa (selfDual_latFr S hP.gS hS g N hN)
        (selfDual_latFr T hP.gT hT h N' hN') _ _ _ Ξ hVm hSBm hThm hΦ hΞ1 hΞ2
  obtain ⟨hHolm, hxi⟩ := hD
  have hHolw : IsHol θ S T ψ w := by
    have := (GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g⁻¹ (inv_mem hg) h⁻¹ (inv_mem hh)
      _ hHolm).1
    rwa [om_inv_om] at this
  have hcomm := ((GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh w hHolw).2 P).2
  have hdiff : Differentiable ℂ fun z =>
      κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
    rw [← thC_const_mul, ← hκ, ← hxi]
    exact (GlobalTheory.AdForm.VacRead.xiN_entire_and_injective D ψ θ S T a b hS hT δ sc hP).1 _ hHolm
  unfold thetaKO
  rw [hcomm, hs _ hHolm P, hxi, hκ, thC_const_mul]
  unfold jetP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.ColNorms.jetC_const_mul _ _ _ hdiff]
  ring

end GlobalTheory.KJInf.CoreG
end
end
