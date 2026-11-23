module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBoundStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetGenerators

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LocalIntegers

theorem exists_finset_generators (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ s : Finset (OK l K), ∀ a : OK l K, ∃ c : OK l K → ℤ_[l],
      (((a : K) : PadicAlgCl l)) = ∑ i ∈ s, ((c i : ℚ_[l]) • (((i : K) : PadicAlgCl l))) := by
  classical
  haveI : Algebra.IsSeparable ℚ_[l] K := Algebra.IsSeparable.of_integral ℚ_[l] K
  haveI : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := integralClosure ℤ_[l] K)
  have hmem : ∀ x : K, x ∈ OK l K ↔ x ∈ integralClosure ℤ_[l] K := by
    intro x
    rw [OK_eq]
    rfl
  let e : integralClosure ℤ_[l] K → OK l K := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : OK l K => (z : K)) hxy)
  refine ⟨t.image e, fun a => ?_⟩
  have ha : (⟨(a : K), (hmem _).1 a.2⟩ : integralClosure ℤ_[l] K) ∈ Submodule.span ℤ_[l] (t : Set _) := by
    rw [ht]
    trivial
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp ha
  refine ⟨fun o => f ⟨(o : K), (hmem _).1 o.2⟩, ?_⟩
  rw [Finset.sum_image fun x _ y _ hxy => he hxy]
  have h1 : (a : K) = ∑ j ∈ t, ((f j • j : integralClosure ℤ_[l] K) : K) := by
    rw [← AddSubmonoidClass.coe_finsetSum, hf]
  rw [h1, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (((f j • j : integralClosure ℤ_[l] K) : K) : PadicAlgCl l) = ((f j : ℚ_[l]) • ((j : K) : PadicAlgCl l))
  rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] (f j) (j : K)]
  rfl

end GlobalTheory.CompanionTheory.LocalIntegers
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PadicIntMemSub

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCZp

theorem padicInt_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) (z : ℤ_[l]) :
    Lat.pk l k (algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))) ∈
      Lat.sub (Lat.fk l k) (xi0 l) l M := by
  have h1 : algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z) :=
    ((algClToBdR l).commutes (z : ℚ_[l])).trans
      (IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l z)
  rw [h1]
  exact Subring.subset_closure (Or.inl ⟨IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z, rfl⟩)

end GlobalTheory.CompanionTheory.LatCZp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl

    rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl

  rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegersStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.exists_lattice_bound_integers : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K), Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | exact GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub <;> assumption)
end
end
