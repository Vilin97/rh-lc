module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAdmExact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnPer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilAnn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilSubq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PStOfCr

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBoundSt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.boundSt_of :
    BoundSt := by
  intro l _ P AI hT K LL
  obtain ⟨T⟩ := hT
  refine ⟨?_, fun f g => ?_⟩
  · intro U _ _ _ _ _ ρ
    rw [dinv_σSt]
    haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] U := Module.Finite.trans ↥LL.1 U
    obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
    have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
      ext x
      simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
    have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
        finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
      rw [hD, finrank_mul_finrank]
      rfl
    have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
    haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
    haveI hL : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
      Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
    refine ⟨hL, ?_⟩
    have hV : finrank ℚ_[l] U = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U :=
      (finrank_mul_finrank ℚ_[l] ↥LL.1 U).symm
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 U) := by ring
  · refine Commute.pow_right ?_ f
    exact LinearMap.ext fun p => (phiSt_actSt P (g : GQ l) p).symm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PJoinAbs

section

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact

section

@[expose] public section

namespace UpperTheory.Gal.crystallineComparison

theorem admissible_sequence_exact : AdmExact := admissibleExact_of_dualInvariantExact dinvExact_of
theorem joinAbs_holds : JoinAbs :=
  joinAbs_of nilEmb_of (nilSubq_of admissible_sequence_exact nilEmb_of) nilAnn_of annSub_of (annExt_of dinvExt_of) admissible_sequence_exact
theorem boundSt_holds : BoundSt := boundSt_of
theorem stOfCr_holds : StOfCr := stOfCr_of annPer_of boundSt_of

end UpperTheory.Gal.crystallineComparison
end
end
