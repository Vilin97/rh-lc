module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHoldsStatement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
public import Mathlib.Topology.Algebra.MvPolynomial
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBundleRadicalAway
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalOrder

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem LocalOrder.proof (hL : SliceLength.Statement) (hS : SliceBranches.Statement)
    (hC : CurveBranchLength.Statement) : LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨U, hUo, hUd, hU⟩ := hL n d J W u hJ hdim hu hW
  obtain ⟨q, _, L, ⟨hrad, hlen⟩, c, hccov, hcdisj, hcord⟩ :=
    hS n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U
      (fun q => {L | IsRadicalAt (sliceIdeal J L q) q ∧
        localMult (J ⊔ Ideal.span {linForm u}) W =
          localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))})
      hUo hUd hU
  rw [hlen]
  exact hC n (sliceIdeal J L q) u q m c ord hrad hccov hcdisj hcord

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L (hL : L ∈ O₁ ∩ O₂) => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAwayZariski

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem eq_ker_eval_of_X_sub_C_mem {n : ℕ} (q : Fin n → ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : P.IsPrime) (h : ∀ k, X k - C (q k) ∈ P) : P = RingHom.ker (eval q) := by
  have hext : Ideal.Quotient.mk P = ((Ideal.Quotient.mk P).comp C).comp (eval q) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun i => ?_)
    simp only [RingHom.comp_apply, eval_X]
    exact Ideal.Quotient.eq.2 (h i)
  have hle : RingHom.ker (eval q) ≤ P := by
    intro f hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, hext]
    simp [RingHom.mem_ker.1 hf]
  have hmax : (RingHom.ker (eval q)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  exact (hmax.eq_of_le hP.ne_top hle).symm

theorem SliceReducedAwayZariski.proof (hG : GenericFibreRadicalAway.Statement)
    (hB : SliceBundleRadicalAway.Statement) : SliceReducedAwayZariski.Statement := by
  intro n d J q hJ
  choose F hF0 hF using fun k : Fin n =>
    hG (Fin d × Fin n) n (universalSliceIdeal J d q) (X k - C (C (q k))) (hB n d J q hJ k)
  refine ⟨∏ k, F k, Finset.prod_ne_zero_iff.2 fun k _ => hF0 k, ?_⟩
  intro L hL P hP hIP hPq g hg
  rw [map_prod, Finset.prod_ne_zero_iff] at hL
  obtain ⟨k, hk⟩ : ∃ k, X k - C (q k) ∉ P := by
    by_contra h
    push Not at h
    exact hPq (eq_ker_eval_of_X_sub_C_mem q P hP h)
  have hk' := hF k _ (hL k (Finset.mem_univ k))
  rw [fibreIdeal_universalSliceIdeal] at hk'
  obtain ⟨m, hm⟩ := hk' g hg
  refine ⟨(X k - C (q k)) ^ m, fun h => hk (hP.mem_of_pow_mem m h), ?_⟩
  simpa using hm

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength GlobalTheory.T.slice_branches_holds GlobalTheory.T.curve_branch_length_holds

end GlobalTheory.CompanionTheory.Heights.BranchOrder
end
end
