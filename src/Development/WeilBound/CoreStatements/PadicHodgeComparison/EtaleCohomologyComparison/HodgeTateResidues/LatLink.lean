module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSubStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegersStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSubStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPowStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesFieldStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegersStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMapStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToBStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisAStatement
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphismStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapFieldStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvdStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompatStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpanStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.galois_preserves_t_power_span : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | exact GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | (intros; apply GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem iota_algebraMap_OK : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  intro l _ K M h k a
  rfl

end GlobalTheory.CompanionTheory.LatC
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegersStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_iota_algebraMap_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | exact GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBaseStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_lattice_base : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  first | exact @GlobalTheory.CompanionTheory.LatCBase.latBase_lev | exact GlobalTheory.CompanionTheory.LatCBase.latBase_lev | (intros; apply GlobalTheory.CompanionTheory.LatCBase.latBase_lev <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dB_sigmaB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) =
      ((levSys h).L m).σB g ((levSys h).dB m b) := by
  intro m g b
  change Bk l (m + 1 + 1) at b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  show dk l (m + 1) (gB h (m + 1 + 1) g (Ideal.Quotient.mk _ x)) =
    gB h (m + 1) g (dk l (m + 1) (Ideal.Quotient.mk _ x))
  simp only [gB, dk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

end GlobalTheory.CompanionTheory.LatLevel
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisBStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_system_transition_galois_B : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) = ((levSys h).L m).σB g ((levSys h).dB m b) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | exact GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open DividedPowers

namespace CrystallineSemistableComparison.Pb.Lat

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dp_ι (hc : DPClosed (ι f ξ l M) (γB f ξ)) : IsDPMorphism (γ f ξ l M hc) (γB f ξ) (ι f ξ l M) :=
  ⟨Ideal.map_le_iff_le_comap.2 fun _ hx => hx, fun {n} a ha => (ι_γ f ξ l M hc ha).symm⟩

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

end Map

end CrystallineSemistableComparison.Pb.Lat
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (GlobalTheory.T.exists_lattice_bound_integers l K).imp fun M h => ⟨h, GlobalTheory.T.acris_mem_lattice_sub l M, GlobalTheory.T.fontaine_lattice_dpow_closed l M, GlobalTheory.T.galois_preserves_t_power_span l K,
    fun k g => GlobalTheory.T.galois_preserves_lattice_sub l K M k g _, GlobalTheory.T.lattice_sub_reduction_mem l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good := by
  exact {
    pos := hk
    lat := GlobalTheory.T.level_lattice_base h k hk
    toB_surj := GlobalTheory.T.level_toB_surjective h k
    toB_ker := GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd h k
    toB_K := GlobalTheory.T.level_toB_algebraMap_field h k
    ι_inj := ι_injective (fk l k) (xi0 l) l M
    ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
    ι_I := rfl
    IB_eq := GlobalTheory.T.level_ideal_eq_map h k
    ι_O := GlobalTheory.T.level_iota_algebraMap_integers h k
    ι_lam := GlobalTheory.T.level_iota_lam_eq_toB h k
    σB_toB := GlobalTheory.T.level_toB_galois_equivariant h k
    σ_ι := lev_σ_ι h k
    σ_lam := GlobalTheory.T.level_lam_galois_equivariant h k
    σ_O := GlobalTheory.T.level_galois_fixes_integers h k
    σ_dp := GlobalTheory.T.level_galois_isDPMorphism h k
    σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
      (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_galois_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
    σB_K := GlobalTheory.T.level_galois_fixes_field h k
    pdP_B := GlobalTheory.T.level_filtration_span_t_pow h k
  }

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good := by
  exact {
    lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
    dB_toB m x := dk_pk (m + 1) (pInv l x)
    dι := sys_dι h
    dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
    dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
    dK m k := dk_pk (m + 1) (kP l K k)
    ddp := GlobalTheory.T.level_system_transition_isDPMorphism h
    ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
      ((levSys h).dA m) ((levSys h).dB m) (GlobalTheory.T.level_ideal_eq_map h (m + 2)) (GlobalTheory.T.level_ideal_eq_map h (m + 1)) (GlobalTheory.T.level_system_transition_isDPMorphism h m).1 (sys_dι h m)
    dσ := GlobalTheory.T.level_system_transition_galois_A h
    dσB := GlobalTheory.T.level_system_transition_galois_B h
    cpl := GlobalTheory.T.existsUnique_period_of_compatible h
  }

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => GlobalTheory.T.level_xi_mem_ideal_and_theta_compat h (m + 1)⟩

end CrystallineSemistableComparison.HT
end
end
end
