module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplUniq
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaMvpsCot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplReg

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.regular :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (B : Type) [CommRing B] [IsLocalRing B]
      [Algebra R B], IsCplAt R p B → IsRegularLocalRing (Localization.AtPrime p) →
      IsRegularLocalRing B ∧ ringKrullDim B = ringKrullDim (Localization.AtPrime p) := by
  intro R _ _ p _ B _ _ _ hB hT
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) hB (isCplAt_cplAt R p)
  have hC : IsRegularLocalRing (CplAt R p) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion (Localization.AtPrime p)
  refine ⟨IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← hC.spanFinrank_maximalIdeal,
    ← hT.spanFinrank_maximalIdeal]
  exact congrArg _ (AdicCompletion.spanFinrank_maximalIdeal_eq (R := Localization.AtPrime p))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaRegPrime

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_localization_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (R ⧸ p)],
      IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro R _ _ p _ _
  obtain ⟨r, x, hx, hsp⟩ := exists_cotInd_of_regular_quotient R p
  obtain ⟨-, hdim, -⟩ := regular_quotient_cotInd R _ x hx
  obtain ⟨hh, hreg⟩ := regular_localization_cotInd R _ x hx p hsp.symm
  refine ⟨hreg, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hh, add_comm]
  rw [hsp] at hdim
  rw [← hdim]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LaDimArith

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem laDim_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := IsLocalHom.of_surjective _ h, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem laDim_surj (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Algebra O K] (σ : Type) [Finite σ] (s : σ)
    (g : MvPowerSeries σ O →ₐ[O] PowerSeries K) (h : Function.Surjective (algebraMap O K))
    (hg : g (MvPowerSeries.X s) = PowerSeries.X) : Function.Surjective g := by
  haveI : IsCO O K := laDim_co O K h
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : IsCO O (PowerSeries K) := co_mvps O K Unit
  refine co_surj O _ _ g (le_trans ?_ le_sup_left)
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le, Set.singleton_subset_iff, ← hg]
  refine Ideal.mem_map_of_mem _ fun hu => ?_
  have := MvPowerSeries.isUnit_constantCoeff _ hu
  simp at this

private theorem laDim_arith (x : WithBot ℕ∞) (n : ℕ) (h : x + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    x = (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    have h' : y + 1 = ((n : ℕ∞) + 1) := by exact_mod_cast h
    have : y = (n : ℕ∞) := WithTop.add_right_cancel ENat.one_ne_top h'
    rw [this]; rfl

private theorem laDim_gen (R : Type) [CommRing R] [IsRegularLocalRing R] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (p : Ideal R) (e : (R ⧸ p) ≃+* S) (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra R La),
      IsCplAt R p La ∧ IsRegularLocalRing La ∧ ringKrullDim La = (n : WithBot ℕ∞) := by
  haveI : IsDomain (R ⧸ p) := e.toMulEquiv.isDomain _
  haveI hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 inferInstance
  haveI : IsRegularLocalRing (R ⧸ p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hq : ringKrullDim (R ⧸ p) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsDiscreteValuationRing.ringKrullDim_eq_one]
  obtain ⟨h1, h2⟩ := regular_localization_of_regular_quotient R p
  have hc := isCplAt_cplAt R p
  obtain ⟨h3, h4⟩ := IsCplAt.regular _ _ _ hc h1
  refine ⟨CplAt R p, inferInstance, inferInstance, inferInstance, hc, h3, ?_⟩
  rw [h4]
  apply laDim_arith
  rw [hq] at h2
  rw [h2, hdim]

theorem UpperTheory.V.Pa.Core.laDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Finite K] [Algebra O K] (D : ℕ) (g : abelian₂ O Unit D →ₐ[O] PowerSeries K), Function.Surjective (algebraMap O K) → g (MvPowerSeries.X (.inl ())) = PowerSeries.X → ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra (abelian₂ O Unit D) La), IsCplAt (abelian₂ O Unit D) (RingHom.ker g) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ((1 + D : ℕ) : WithBot ℕ∞) := by
  intro O _ _ _ _ K _ _ _ D g h hg
  have hs : Function.Surjective g := laDim_surj O K _ _ g h hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hreg, hdim, -⟩ := mvPowerSeries_cotInd O ϖ hϖ (Unit ⊕ Fin D)
  haveI : IsRegularLocalRing (abelian₂ O Unit D) := hreg
  refine laDim_gen (abelian₂ O Unit D) (PowerSeries K) (RingHom.ker g)
    (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv (1 + D) ?_
  rw [hdim, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
end
end
