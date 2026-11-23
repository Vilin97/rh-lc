module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseTau
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsUnitaryDiag
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitSt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasTemperateGrowthEvalPoly
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PhiSVal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigTop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntSmul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ValZeroOfTens

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRightOf

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem convRight_of (hE : EisStrong) : ConvRight := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR
  have hn : 0 < n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hsec : IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) :=
    GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 h𝓕 ω hS.hω l hS.hl s hS.hs Φ
      hS.hΦ
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ :=
    hE D n hn χ V.rank hS.hχ hS.hη H hS.hH (s0 V n) _ hsec (s0 V n)
  refine ⟨σ, fun z hz g => ?_⟩
  obtain ⟨u, hu, hb⟩ := (hconv z hz).1 {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hb g rfl q) hu

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIautoOf

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dite_eq_left hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIk

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dite_eq_left hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIwasawa

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gIwasawa : GIwasawa := GlobalTheory.StdUnn.Iwasawa.exists_mul

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LinSecOf

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (a : ℂ) (g : G D n) :
    thetaInt ω ν (a • Φ) g = a * thetaInt ω ν Φ g := by
  have h : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (a • Φ) g) = fun q => a * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q := by
    funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend, theta, map_smul, tsum_mul_left]
  simp only [thetaInt, h, MeasureTheory.average, MeasureTheory.integral_const_mul]

theorem tens_fP_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (P Q : PX m n) :
    tens θ τ fr (fP c (P + Q)) Ψ = tens θ τ fr (fP c P) Ψ + tens θ τ fr (fP c Q) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), Pi.add_apply]
  ring

theorem tens_fP_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (a : ℂ) (P : PX m n) :
    tens θ τ fr (fP c (a • P)) Ψ = a • tens θ τ fr (fP c P) Ψ := by
  funext x
  simp only [tens, fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
  ring

theorem linSec_of : ThLin → LinSec := by
  intro hTL D n V ψ χ θ μ ω H l s ν τ ε fr ι c Ψ hΨ
  have hl0 : ∀ τ, l τ ≠ 0 := lNZ D ψ θ l c.hψ c.hθ c.hl
  have hm : ∀ P, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s :=
    fun P => tensMem D n V θ l s τ ε fr c.hθ hl0 c.hs c.hfr Ψ hΨ P
  have hphi : ∀ P, phiS θ τ fr (cLoc l τ) Ψ P = ⟨_, (hm P).1⟩ := fun P => dif_pos (hm P).1
  have hadd : ∀ P Q, phiS θ τ fr (cLoc l τ) Ψ (P + Q) = phiS θ τ fr (cLoc l τ) Ψ P + phiS θ τ fr (cLoc l τ) Ψ Q := by
    intro P Q
    rw [hphi, hphi, hphi]
    exact Subtype.ext (tens_fP_add θ τ fr _ Ψ P Q)
  have hsmul : ∀ (a : ℂ) P, phiS θ τ fr (cLoc l τ) Ψ (a • P) = a • phiS θ τ fr (cLoc l τ) Ψ P := by
    intro a P
    rw [hphi, hphi]
    exact Subtype.ext (tens_fP_smul θ τ fr _ Ψ a P)
  have hstd : ∀ P, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ P) := fun P =>
    ⟨c.hψ, c.hχ, c.hη, c.hθ, c.hμ, c.hω, c.hH, c.hl, c.hs, c.hν, by rw [hphi]; exact (hm P).2⟩
  refine ⟨{ toFun := fun P => secF ω τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [secF, hadd, map_add (f := _), Submodule.coe_add, Pi.add_apply]
            map_smul' := fun a P => by
              funext g
              simp only [secF, hsmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] },
          { toFun := fun P => thF ω ν τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [thF, Pi.add_apply]
              rw [hadd]
              exact hTL D n V ψ χ θ μ ω H l s ν _ _ (hstd P) (hstd Q) c.hr g
            map_smul' := fun a P => by
              funext g
              simp only [thF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [hsmul]
              exact thetaInt_smul ω ν _ a g }, fun P => rfl, fun P => rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem locOpEx_of_locFact (hF : LocFact) : LocOpEx := locOpEx_of_fact hF awayIn schFP lNe

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SummableOfAbsTheta

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem summable_of_absTheta {D : D7} {V : HSp D} {n : ℕ} (φ : Mx D V.rank n → ℂ) (h : GA D V)
    (hh : GlobalTheory.SiegelFormula.absTheta V φ h < ⊤) :
    Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => φ (GlobalTheory.SiegelFormula.invPt V h ξ) :=
  Summable.of_enorm hh.ne

theorem thLin_of (hP : GlobalTheory.Published.WeilThetaConvergence) : ThLin := by
  intro D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g
  obtain ⟨h1, h2, hr⟩ := hR
  have hn : 1 ≤ n := by omega
  have hI := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g
  have hI' := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g
  have hae : ∀ φ : schwartzA θ V.rank n,
      ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ := by
    intro φ
    have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ
    have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hS.hθ _ _ φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1
    exact ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
  have heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν]
      fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q := by
    filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'
    simp only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢
    have s1 := summable_of_absTheta (ω g Φ).1 _ hq
    have s2 := summable_of_absTheta (ω g Φ').1 _ hq'
    show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) =
      (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)
    rw [← s1.tsum_add s2]
    congr 1
    funext ξ
    simp [map_add (f := _)]
  unfold thetaInt
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq,
    integral_add hI hI', smul_add]

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem top (hA : AbsThm) (hLF : LocFact) (hAA : AwayAct)
    (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hE : EisStrong) (hC : PositivityTheory.PfSWUS.CoefND)
    (hW : GlobalTheory.Published.WeilThetaConvergence) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) := by
  have hTM := tensMem
  have hTL := thLin_of hW
  exact main hA sFrame sEmb sigOK splitFock hTM (locOpEx_of_locFact hLF) hLi (linSec_of hTL)
    (gSplit_of gIwasawa hAA hLF awayIn schFP hTM lNZ) (gIauto_of hTA hTM) gIk
    (gIinv_of hTM hTL hLC hDO) hId hE gLamBd (gLsing PositivityTheory.Rg.Sw.twoSided' denseTau) hC
    (convRight_of hE) hTL lNZ

end PositivityTheory.Rg.Sw.Glob
end
end
