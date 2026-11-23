module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.WhitSide

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MonoSch

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem monoFock (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ) (h : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  exact Submodule.subset_span ⟨_, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, rfl⟩

def MonoSchPos : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, l τ ≠ 0) → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchPos : MonoSchPos := by
  intro D n V θ l s hl hs φ h
  refine ⟨?_, monoFock D n V θ l s φ h⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.WhitAdd.exists_schwartz_polyGauss V l hl s hs (MvPolynomial.monomial e c)
  refine Submodule.subset_span ⟨f, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, ?_⟩
  funext x
  rw [hf]
  rfl

def MonoSchStd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchStd : MonoSchStd := fun D n V _ _ θ _ _ _ l s _ _ hS φ h =>
  monoSchPos D n V θ l s (GlobalTheory.CompanionTheory.WhitAdd.par_ne_zero hS) hS.hs φ h

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Assembly

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND


theorem matchMono_of' (hψ : PsiPlaces) (hR : RealMatch) (hRc : RealConj) (hH : HeightWN) (hF : FinMatch)
    (hM : ConjMod) (hT : ValueSide) (hU : Unfold) (hK : HeightKInv) (hA : HaarFam) : MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ a k hk φ hφ
  obtain ⟨hchar, hpl⟩ := hψ D n V ψ χ θ μ ω H l s ν Φ hstd
  obtain ⟨hsch, hfock⟩ := monoSchStd D n V ψ χ θ μ ω H l s ν Φ hstd φ hφ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφeq⟩ := hφ
  obtain ⟨εG, frG, PG, hfr, hreal⟩ := hR D n V ψ θ l s hstd.hθ hstd.hl hstd.hs e c a
  obtain ⟨L, hLco, hLstd, hLnu⟩ := hH D n H hstd.hH θ hstd.hθ nb hcd.1 w hw
  obtain ⟨lamS, hlamS⟩ := hA D n
  obtain ⟨L₁, L₂, Φf, Φv, hco, hstd', hpure', hΦf, hnu2⟩ :=
    hF D n V.rank a d bs g gv hpure lamS L hlamS hLco (hLstd d bs)
  obtain ⟨𝓕μ, hμ⟩ := hstd.hμ
  refine ⟨d, bs, θ, l, εG, frG, aTau θ a, PG, lamS, L₁, L₂, fun X => φ (HMul.hMul (tupOf X) a.1), Φf, Φv,
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ?_, ?_⟩
  · constructor
    · exact GlobalTheory.DefiniteQuotient.cmExt D
    · exact GlobalTheory.DefiniteQuotient.gram_hermND V
    · exact hrange.1
    · intro i j
      exact congrFun (congrFun β.2 i) j
    · exact hβ
    · exact hchar
    · exact hpl
    · exact hfr
    · exact hlamS
    · exact hco
    · exact hstd'
    · exact hpure'
    · intro X
      have h1 := hreal (tupOf X)
      have h2 := hΦf (tupOf X)
      rw [tupInv_tupOf] at h1 h2
      change φ (HMul.hMul (tupOf X) a.1) = _
      rw [hφeq]
      simp only
      rw [h1, h2]
    · exact sdW_map V hchar hμ
    · exact sdHerm_map hchar hcd.2
  · exact whit_side hRc hM hU hK hstd hrange hcd hw hβ a hk hsch hfock lamS hlamS L L₁ L₂ hLnu hnu2 𝓕μ hμ
  · intro μH 𝓕 hHaar hFD
    exact congrArg _ (hT D n V ν hstd.hν (fun x => φ (HMul.hMul x a.1)) β hβ μH 𝓕 hHaar hFD)

end PositivityTheory.PfSWUS.SwMatch

end
end
end
