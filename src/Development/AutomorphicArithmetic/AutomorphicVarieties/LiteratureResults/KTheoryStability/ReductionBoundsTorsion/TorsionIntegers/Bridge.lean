module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStarOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.SGapOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.SHtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MeanLatticeCounts.CountableLatS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddSpanRank.SBStarOddOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.SWtOddOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SinvOfSwt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SwtAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SStokesOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SStokesOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SurjectivityCase.SSurjOf

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.ExistsPrincipal

section

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace PositivityTheory.KB.PrincipalPrimes

theorem exists_principal (L : Type) [Field L] [NumberField L] (T : Set (HeightOneSpectrum (𝓞 L)))
    (hT : T.Finite) : ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T ∧ v.asIdeal.IsPrincipal := by
  let Ω := AlgebraicClosure L
  let H := GroundTheory.Global.hilbertClassField L Ω
  have : NumberField H := NumberField.of_module_finite L H
  have : IsGalois L H := inferInstance
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := L) (L := H)
    ({1} : Set (H ≃ₐ[L] H)) (by
      intro σ hσ τ
      rw [Set.mem_singleton_iff] at hσ ⊢
      rw [hσ, mul_one, mul_inv_cancel])
  have hpos : (0 : ℝ) < (Nat.card ({1} : Set (H ≃ₐ[L] H)) : ℝ) / Nat.card (H ≃ₐ[L] H) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨-, w, hw, hF⟩, hvT, -⟩ :=
    ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity hd hpos hT
  refine ⟨v, hvT, ?_⟩
  have := hw
  have h1 := GroundTheory.Global.hilbertClassFieldArtinEquiv_mk0 L Ω v w
  rw [Set.mem_singleton_iff.1 hF, MulEquiv.map_eq_one_iff] at h1
  exact (ClassGroup.mk0_eq_one_iff _).1 h1

theorem finite_small (L : Type) [Field L] [NumberField L] (B : ℕ) :
    {v : HeightOneSpectrum (𝓞 L) | Ideal.absNorm v.asIdeal ≤ B}.Finite :=
  Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h) (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) B)

theorem exists_prime (L : Type) [Field L] [NumberField L] (B : ℕ) :
    ∃ π : 𝓞 L, Prime π ∧ B ≤ Ideal.absNorm (Ideal.span {π}) := by
  obtain ⟨v, hv, π, hπ⟩ := exists_principal L _ (finite_small L B)
  have hπ' : v.asIdeal = Ideal.span {π} := hπ
  have hne : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hπ', Ideal.span_singleton_eq_bot])
  refine ⟨π, (Ideal.span_singleton_prime hne).1 (hπ' ▸ v.isPrime), ?_⟩
  rw [← hπ']
  simp only [Set.mem_ofPred_eq, not_le] at hv
  omega

end PositivityTheory.KB.PrincipalPrimes
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.SPrimeOf

section

@[expose] public section

namespace PositivityTheory.KB

theorem sPrime_of : SPrime := fun L _ _ => PrincipalPrimes.exists_prime L 25

end PositivityTheory.KB
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SInvOf

section

@[expose] public section

namespace PositivityTheory.KB

theorem sInv_of : SChain → SEv → SPsi → SStokes → SInv := fun hC hE hP hS =>
  BlockInvariants.sinv_of_swt hC hP hS BlockInvariants.aGood (BlockInvariants.swt_all hE hS)

end PositivityTheory.KB
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SInv

section

@[expose] public section

namespace PositivityTheory.KB

theorem sInv : SInv := sInv_of sChain sEv sPsi sStokes_of

end PositivityTheory.KB
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FinalOdd

section

@[expose] public section

namespace PositivityTheory.KB

theorem bStarOdd : BStarOdd :=
  sBStarOdd_of sChain sSep' sBridge sStab
    (sSurj_of sPrime_of sHecke sHt_of sPU sMom sWhit sCen sGap_of sLoc sMean_of sInv)
    (sWtOdd_of sChain sEv sPsi sStokes_of)

end PositivityTheory.KB
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.TorsionIntegers.Bridge

section

@[expose] public section

open UpperTheory.V.KL

namespace PositivityTheory.KB

theorem lev_zk (l n : ℕ) : ∀ t, UpperTheory.V.ZK.lev l n t = lev l n t
  | 0 => rfl
  | t + 1 => congrArg (l * ·) (lev_zk l n t)

private theorem step_heq (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) (m c : ℕ) {a b : ℕ} (e : a = b)
    (u : grpH (GL (Fin a) R) m) (v : grpH (GL (Fin b) R) m) (h : HEq u v) :
    HEq ((grpHMap (UpperTheory.V.ZK.psi R l a) m).hom u -
        c • (grpHMap (stab R a (l * a) (Nat.le_mul_of_pos_left _ hl)) m).hom u)
      ((grpHMap (psi R l b) m).hom v - c • (grpHMap (stab R b (l * b) (Nat.le_mul_of_pos_left _ hl)) m).hom v) := by
  subst e
  obtain rfl := eq_of_heq h
  rfl

theorem zSeq_zk (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (x : grpH (GL (Fin n) R) m) :
    ∀ t, HEq (UpperTheory.V.ZK.zSeq R hl x t) (zSeq R hl x t)
  | 0 => HEq.rfl
  | t + 1 => step_heq R hl m (l ^ (t + 2)) (lev_zk l n t) _ _ (zSeq_zk R hl x t)

private theorem rank_heq (R : Type) [CommRing R] (m : ℕ) {X : Type} {a b : ℕ} (e : a = b)
    (f : X → grpH (GL (Fin a) R) m) (g : X → grpH (GL (Fin b) R) m) (h : ∀ x, HEq (f x) (g x)) :
    Module.rank ℤ (Submodule.span ℤ (Set.range f)) = Module.rank ℤ (Submodule.span ℤ (Set.range g)) := by
  subst e
  obtain rfl : f = g := funext fun x => eq_of_heq (h x)
  rfl

theorem bOdd_zk : UpperTheory.V.ZK.BOdd := fun L _ _ hL k hk hr l hl n hn =>
  (rank_heq _ _ (lev_zk l n k) _ _ fun x => zSeq_zk _ hl x k).le.trans (bStarOdd L hL k hk hr l hl n hn)

end PositivityTheory.KB
end
end
