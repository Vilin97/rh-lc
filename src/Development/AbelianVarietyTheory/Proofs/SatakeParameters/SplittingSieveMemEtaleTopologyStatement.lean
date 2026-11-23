module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffineStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPrStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplementStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtale

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem diagComplHom_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  intro Z X f _ _
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hcl : IsClosedImmersion (diagCompl f).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hopen.isClosed_compl)
  unfold diagComplHom
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.EtC.Tr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtaleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem isEmpty_of_fibrePointsLE_zero {Z X : Scheme.{0}} (f : Z ⟶ X) (h : FibrePointsLE f 0) :
    IsEmpty Z := by
  refine ⟨fun z => ?_⟩
  exact h (Z.residueField z) (Z.fromSpecResidueField z ≫ f) (fun _ => Z.fromSpecResidueField z)
    (fun _ => rfl) (fun a b _ => Fin.subsingleton_one.elim a b)

end GlobalTheory.EtC.Tr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZeroStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X), GlobalTheory.EtC.Tr.FibrePointsLE f 0 → IsEmpty Z := by
  first | (exact @GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (exact GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (intros; apply GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullback

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X),
    IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  intro Z X V f y hE
  have hP : IsInitial (pullback f y) := isInitialOfIsEmpty
  refine ⟨0, Fin.elim0, fun j => j.elim0, ?_⟩
  refine ⟨⟨hP.to _, ?_, hP.hom_ext _ _⟩⟩
  apply Sigma.hom_ext
  intro j
  exact j.elim0

end GlobalTheory.EtC.Tr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfIsEmptyPullbackStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X), IsEmpty (pullback f y : Scheme.{0}) → GlobalTheory.EtC.Tr.Splits f y := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (exact GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback) | (intros; apply GlobalTheory.EtC.Tr.splits_of_isEmpty_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSnd

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_splits_pullback_snd {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S) :
    GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  rintro ⟨m, s, hs, hiso⟩
  refine ⟨m, fun j => s j ≫ pullback.fst f x, fun j => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs j]
  · have heq : (Sigma.desc (fun j => pullback.lift (s j ≫ pullback.fst f x) (𝟙 V)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback f (v ≫ x)) =
        (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback (pullback.snd f x) v) ≫
          (pullbackLeftPullbackSndIso f x v).hom := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
      · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [heq]
    infer_instance

end GlobalTheory.EtC.Tr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSndStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd : ∀ {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S), GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (exact GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (intros; apply GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitSieve_mem_of_fibrePointsLE : ∀ (n : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    FibrePointsLE f n → splitSieve f (𝟙 X) ∈ Scheme.etaleTopology X := by
  intro n
  induction n with
  | zero =>
    intro Z X f _ _ h
    have : IsEmpty Z := GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero f h
    have hs : Splits f (𝟙 X ≫ 𝟙 X) := GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f _ (Function.isEmpty (pullback.fst f (𝟙 X ≫ 𝟙 X)))
    have hmem : splitSieve f (𝟙 X) (𝟙 X) := ⟨X, 𝟙 X, 𝟙 X, hs, Category.id_comp _⟩
    rw [Sieve.id_mem_iff_eq_top] at hmem
    rw [hmem]; exact (Scheme.etaleTopology).top_mem X
  | succ n ih =>
    intro Z X f _ _ h
    obtain ⟨hfin, het⟩ := GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale f
    have hg := ih (diagComplHom f) (GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection f n h)
    refine GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale f _ ?_ (fun {V} v hv => ?_)
    · refine (Scheme.etaleTopology).superset_covering ?_ hg
      rintro V u ⟨W, w, v, hv, rfl⟩
      have h1 : Splits (pullback.snd f f) (v ≫ 𝟙 Z) := GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement f _ hv
      have h2 : Splits f ((v ≫ 𝟙 Z) ≫ f) := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f f _ h1
      exact ⟨W, w, v ≫ f, by simpa using h2, by simp⟩
    · exact ⟨V, 𝟙 V, v, by simpa using GlobalTheory.T.splitsFinitelyOverScheme_of_isEmpty_pullback f v hv, Category.id_comp _⟩

theorem splitSieve_mem : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X),
    splitSieve f x ∈ Scheme.etaleTopology S := by
  intro Z X S f _ _ x
  let 𝒰 := S.affineCover
  have hU : Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.etaleTopology S :=
    Scheme.zariskiTopology_le_etaleTopology _ (𝒰.mem_grothendieckTopology)
  refine (Scheme.etaleTopology).transitive hU _ ?_
  rintro Y u ⟨W, w, _, ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable w ?_
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine (pullback.snd f (𝒰.f i ≫ x))
  have hi := splitSieve_mem_of_fibrePointsLE n (pullback.snd f (𝒰.f i ≫ x)) hn
  refine (Scheme.etaleTopology).superset_covering ?_ hi
  rintro V u ⟨W', w', v, hv, rfl⟩
  have h1 := GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd f (𝒰.f i ≫ x) (v ≫ 𝟙 _) hv
  exact ⟨W', w', v ≫ 𝒰.f i, by simpa using h1, by simp⟩

end GlobalTheory.EtC.Tr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopologyStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splittingSieve_mem_etaleTopology : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X), GlobalTheory.EtC.Tr.splitSieve f x ∈ Scheme.etaleTopology S := by
  first | exact @GlobalTheory.EtC.Tr.splitSieve_mem | exact GlobalTheory.EtC.Tr.splitSieve_mem | (intros; apply GlobalTheory.EtC.Tr.splitSieve_mem <;> assumption)
end
end
