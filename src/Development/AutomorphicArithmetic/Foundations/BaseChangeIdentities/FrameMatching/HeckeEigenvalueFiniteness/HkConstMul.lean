module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients

section

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.JHMult
open PositivityTheory.Rg.BcN.F2 (FinSubq)

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotientsStatement

section

@[expose] public section

theorem _root_.GlobalTheory.T.finite_subquotients :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (ι : Type) [Fintype ι] [DecidableEq ι], PositivityTheory.Rg.BcN.F2.FinSubq F ι :=
  GlobalTheory.CompanionTheory.RepFinSubq.finSubq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacterStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

theorem _root_.GlobalTheory.T.isolate_representation_at_character : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], IsolateAt F ι := by
  first | exact @GlobalTheory.CompanionTheory.Isolate.isolateAt | exact GlobalTheory.CompanionTheory.Isolate.isolateAt | (intros; apply GlobalTheory.CompanionTheory.Isolate.isolateAt <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.FixedEquiv

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hk_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (v : V) :
    φ.toLinearEquiv (hk ρ K e v) = hk σ K e (φ.toLinearEquiv v) := by
  unfold hk
  refine (φ.toLinearEquiv.toAddEquiv.map_finsum (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)).trans
    (finsum_congr fun q => ?_)
  change φ.toLinearEquiv (e q.out • ρ q.out v) = e q.out • σ q.out (φ.toLinearEquiv v)
  rw [map_smul, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply,
    φ.toIntertwiningMap.isIntertwining]

theorem fixed_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W} (φ : ρ.Equiv σ)
    (K : Subgroup (GL ι F)) (v : V) (hv : v ∈ fixed ρ K) : φ.toLinearEquiv v ∈ fixed σ K := by
  intro h
  have h1 : ρ (h : GL ι F) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v := hv h
  rw [Representation.Equiv.toLinearEquiv_apply, ← φ.toIntertwiningMap.isIntertwining,
    ← Representation.Equiv.toLinearEquiv_apply, h1, map_smul]
  rfl

end SlopeTestRemainingChoices

theorem choiceS_of
    (hI : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.IsolateAt (w.adicCompletion E) (Fin n))
    (hF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.FinSubq (w.adicCompletion E) (Fin n))
    (hP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
      PositivityTheory.Rg.BcN.F2.ProdFinLen (w.adicCompletion E) (Fin n)) : ChoiceS := by
  intro E _ _ _ n w K' hKo hKc P hP0 k D
  have hs : ∀ j, IsSmooth (prodAt (D j) w) := fun j => GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : ∀ j, GlobalTheory.SmGL.HasFiniteLength (prodAt (D j) w) := fun j =>
    hP E n w (Fin (D j).c) (fun i => Fin ((D j).N i)) (GlobalTheory.SmGL.stdBlocks (D j).N (D j).h)
      (fun i => ((D j).σ i w).V) (fun i => ((D j).σ i w).ρ) (fun i => ((D j).σ i w).smooth)
      (fun i => ((D j).σ i w).irred)
  choose J hJ W hW1 hW2 τ hτ hcov using fun j => hF E n w _ (prodAt (D j) w) (hs j) (hfl j)
  let _ : ∀ j, Fintype (J j) := hJ
  let _ : ∀ j i, AddCommGroup (W j i) := hW1
  let _ : ∀ j i, Module ℂ (W j i) := hW2
  let I : Type := Σ j : Fin k, {i : J j // IsEmpty ((τ j i).Equiv P.ρ)}
  obtain ⟨e, hIk, v₀, hv₀, l, hl1, hl, hkill⟩ :=
    hI E n w K' hKo hKc P.V P.ρ P.smooth P.irred hP0 I (fun x => W x.1 x.2.1) (fun x => τ x.1 x.2.1)
      (fun x => (hτ x.1 x.2.1).1) (fun x => (hτ x.1 x.2.1).2.1) (fun x => x.2.2)
  refine ⟨e, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, ?_⟩
  intro j τ' hsub hne v hv
  obtain ⟨i, ⟨φ⟩⟩ := hcov j τ'.V τ'.ρ τ'.irred hsub
  have hi : IsEmpty ((τ j i).Equiv P.ρ) := ⟨fun ψ => hne.false (φ.trans ψ)⟩
  apply φ.toLinearEquiv.injective
  rw [hk_equiv, map_zero]
  exact hkill ⟨j, i, hi⟩ _ (fixed_equiv φ K' v hv)

end PositivityTheory.Rg.BcB.F.Choice

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.HkConstMul

section

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hk_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (c : ℂ) (e : GL ι F → ℂ) (v : V) :
    PositivityTheory.Rg.BcN.F2.hk ρ K (fun g => c * e g) v = c • PositivityTheory.Rg.BcN.F2.hk ρ K e v := by
  unfold PositivityTheory.Rg.BcN.F2.hk
  rw [smul_finsum]
  exact finsum_congr fun q => mul_smul _ _ _

theorem UpperTheory.HeckeLevelFrameExistence.locE :
    UpperTheory.HeckeLevelFrameExistence.LocE := by
  intro E _ _ _ n w hw K' hKo hKle hlev σ hσ k D
  have hUL : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hKc : IsCompact (K' : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K' hKo) hKle
  obtain ⟨P, T, hT, hcomp, hdict⟩ := GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ
  have hd := hdict (K'.subgroupOf (UL n w)) hlev
  rw [hmap] at hd
  obtain ⟨y₀, hy₀, hy₀0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ) :=
    ⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩
  have hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0 :=
    ⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩
  have hchoice : PositivityTheory.Rg.BcB.F.Choice.ChoiceS :=
    PositivityTheory.Rg.BcB.F.Choice.choiceS_of
      (fun E _ _ _ n w => GlobalTheory.T.isolate_representation_at_character (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_subquotients (w.adicCompletion E) (Fin n))
      (fun E _ _ _ n w => GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n))
  obtain ⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩ :=
    hchoice E n w K' hKo hKc P hP0 k D
  set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr
  have hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g) :=
    ⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by
      simp only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩
  have hH := (hd _ hIk').1
  refine ⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩
  · have hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w)) := by
      rintro ⟨x, hx⟩
      apply T.injective
      have h1 := hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      rw [map_smul, hT, T.apply_symm_apply]
      simpa using h1
    refine ⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩
    · have h0 : T.symm v₀ = 0 := congrArg Subtype.val h
      have h1 : v₀ = 0 := T.symm.map_eq_zero_iff.1 h0
      rw [h1, map_zero] at hl1
      exact zero_ne_one hl1
    · apply Subtype.ext
      rw [(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]
      apply T.injective
      have h2 := ((hd e₀ hIk).2 _ hy).2
      rw [T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul] at h2
      rw [h2, T.apply_symm_apply]
  · intro j τ hs hne v hv
    rw [hk_const_mul, hkill j τ hs hne v hv, smul_zero]
end
end
