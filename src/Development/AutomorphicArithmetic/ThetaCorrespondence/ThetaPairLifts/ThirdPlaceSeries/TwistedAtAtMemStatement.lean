module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

-- Source module: Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Survey.PeriodBoundOfPlaceBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

theorem vAdd_unit (D : D7) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    vAdd (D.plEq w) (s : D.what₂.LL) = 0 := by
  have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
    have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
    rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
  unfold vAdd
  rw [h1]; simp

theorem exists_place (D : D7) (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 D.what₂.LL) := by
    intro h
    have : IsUnit (algebraMap ℤ (𝓞 D.what₂.LL) (p : ℤ)) := by simpa using h
    have h2 := Int.isUnit_iff.1 (isUnit_of_map_unit (algebraMap ℤ (𝓞 D.what₂.LL)) _ this)
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 D.what₂.LL)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hpM : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ M := hle (Ideal.subset_span rfl)
  have hne : M ≠ ⊥ := by
    rintro rfl
    have : ((p : ℕ) : 𝓞 D.what₂.LL) = 0 := hpM
    exact hp.ne_zero (by exact_mod_cast this)
  let v : HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨M, hM.isPrime, hne⟩
  refine ⟨D.plEq.symm v, ?_⟩
  set w := D.plEq.symm v with hw
  have hv : D.plEq w = v := by simp [hw]
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    rw [hv]
    intro hin
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hp).2 hq)
    obtain ⟨a, b, hab⟩ := hc
    apply hM.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : 𝓞 D.what₂.LL) * (p : ℕ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [this]
    exact M.add_mem (M.mul_mem_left _ hin) (M.mul_mem_left _ hpM)
  have h0 := vAdd_unit D w _ hnot
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h1
  have h2 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h1
  have h3 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    simp
  rw [h3, h2] at h0
  have := D.what₂.places.ramIdx_pos w
  omega

end GlobalTheory.Survey.PeriodBoundOfPlaceBound

end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h

section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z

end GlobalTheory.Mem.Top.Bl.Model3

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMem

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem twistedAt_atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  obtain ⟨v, hv⟩ := GlobalTheory.Survey.PeriodBoundOfPlaceBound.exists_place (w.D Z) (B.host.g 0) (B.host.g_prime 0)
  have hW := GlobalTheory.Mem.Top.Bl.Model3.type_mem t v 0 hv
  exact ⟨v, (GlobalTheory.Mem.Top.V4.Model.mem_iff t.mu v).1 hW⟩
end GlobalTheory.GalLoc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMemStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.exists_twisted_place_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  first | exact @_root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | exact _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | (intros; apply _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt <;> assumption)
end
end
end
