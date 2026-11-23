module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
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
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Localization.Cardinality
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import ReciprocityTheory.Automorphisms.PlaceA

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosedContinuumRingEquivComplexExtending

section

@[expose] public section

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem algClosed_continuum_ringEquiv_complex_extending :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C], Cardinal.mk C = Cardinal.continuum →
      ∀ (K : Type) [Field K] [NumberField K] (i : K →+* C) (s : K →+* ℂ),
        ∃ e : C ≃+* ℂ, ∀ x, e (i x) = s x := by
  intro C _ _ _ hC K _ _ i s
  obtain ⟨e₀⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
    (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [hC, Cardinal.mk_complex]))
  haveI : Countable K :=
    Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K (e₀.toRingHom.comp i) s
  exact ⟨e₀.trans τ, fun x => hτ x⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoe

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ReadingEmb

theorem exists_ringHom_complex_extending (A : Type) [Field A] (hA : Cardinal.mk A ≤ Cardinal.continuum)
    (K : Type) [Field K] [NumberField K] (i : K →+* A) (s : K →+* ℂ) :
    ∃ ι : A →+* ℂ, ∀ x, ι (i x) = s x := by
  haveI : CharZero A := (RingHom.charZero_iff i.injective).1 inferInstance
  let B := FractionRing (MvPolynomial ℝ A)
  have hB : Cardinal.mk B = Cardinal.continuum := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hA,
      max_eq_left Cardinal.aleph0_le_continuum]
  let C := AlgebraicClosure B
  have hC : Cardinal.mk C = Cardinal.continuum := by
    refine le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max B C).trans
      (max_le hB.le Cardinal.aleph0_le_continuum)) ?_
    rw [← hB]
    exact Cardinal.mk_le_of_injective (algebraMap B C).injective
  let j : A →+* C := (algebraMap B C).comp ((algebraMap (MvPolynomial ℝ A) B).comp MvPolynomial.C)
  haveI : CharZero C := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e, he⟩ := GlobalTheory.algClosed_continuum_ringEquiv_complex_extending C hC K (j.comp i) s
  exact ⟨e.toRingHom.comp j, fun x => he x⟩

theorem mk_le_of_finite (R S : Type) [CommRing R] [AddCommGroup S] [Module R S] [Module.Finite R S]
    (h : Cardinal.mk R ≤ Cardinal.continuum) : Cardinal.mk S ≤ Cardinal.continuum := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk R ^ (n : Cardinal) ≤ Cardinal.continuum ^ (n : Cardinal) := Cardinal.power_le_power_right h
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero (Cardinal.natCast_le_aleph0)
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem exists_complex_emb : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  intro D F i k b v ρ
  haveI := D.ntw.lPrime i
  have h1 : Cardinal.mk (D.ntw.Ok i k) ≤ Cardinal.continuum := by
    have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
      Subtype.val_injective.comp (F.eOk i k).injective
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]
  haveI := ρ.fin
  have h2 : Cardinal.mk ρ.Oe ≤ Cardinal.continuum := mk_le_of_finite (D.ntw.Ok i k) ρ.Oe h1
  exact exists_ringHom_complex_extending (FractionRing ρ.Oe) (by rw [Cardinal.mk_fractionRing]; exact h2)
    D.what₂.LL ρ.emb D.what₂.embLL

end GlobalTheory.ReadingEmb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  first | exact @GlobalTheory.ReadingEmb.exists_complex_emb | exact GlobalTheory.ReadingEmb.exists_complex_emb | (intros; apply GlobalTheory.ReadingEmb.exists_complex_emb <;> assumption)
end
end
