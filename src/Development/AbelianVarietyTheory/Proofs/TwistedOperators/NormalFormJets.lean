module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedDefiniteKernelEntriesIsAlgebraicStatement
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.IsCyclotomicExtensionFourSlopeModelField

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.RowTest.CosetFin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem finDatum_eq {t : T} {p : Pair T} {k : ℕ} {a b : FinDatum G t p} (ha : IsCosetDatum k a) (hb : IsCosetDatum k b)
    (hP : a.P = b.P) (he : a.e = b.e) (hz : a.z = b.z) {u} (hu : a.fn u ≠ 0) (hu' : b.fn u ≠ 0) : a = b := by
  have hf := ha.fn_eq hb he hu hu'
  cases a
  cases b
  simp only at hP he hz hf
  subst hP he hz hf
  rfl

theorem pureDat_eq {t : T} {k : ℕ} {e : AE D} {d d' : PureDat G t}
    (hc : (∀ j, IsCosetDatum k (d.1 j)) ∧ ∀ i, IsCosetDatum k (d.2 i))
    (hc' : (∀ j, IsCosetDatum k (d'.1 j)) ∧ ∀ i, IsCosetDatum k (d'.2 i))
    (hp : (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hp' : (∀ j, (d'.1 j).P = locPl G t ∧ (d'.1 j).e = e ∧ (d'.1 j).z = 1) ∧
      ∀ i, (d'.2 i).P = locPl G t ∧ (d'.2 i).e = e ∧ (d'.2 i).z = 1)
    (hx : ∀ j, ∃ u, (d.1 j).fn u ≠ 0 ∧ (d'.1 j).fn u ≠ 0) (hy : ∀ i, ∃ u, (d.2 i).fn u ≠ 0 ∧ (d'.2 i).fn u ≠ 0) : d = d' := by
  refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
  · obtain ⟨a1, a2, a3⟩ := hp.1 j
    obtain ⟨b1, b2, b3⟩ := hp'.1 j
    obtain ⟨u, hu, hu'⟩ := hx j
    exact finDatum_eq (hc.1 j) (hc'.1 j) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'
  · obtain ⟨a1, a2, a3⟩ := hp.2 i
    obtain ⟨b1, b2, b3⟩ := hp'.2 i
    obtain ⟨u, hu, hu'⟩ := hy i
    exact finDatum_eq (hc.2 i) (hc'.2 i) (a1.trans b1.symm) (a2.trans b2.symm) (a3.trans b3.symm) hu hu'

end GlobalTheory.RowTest.CosetFin

namespace GlobalTheory.RowTest.CosetFin

section Sums

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
  {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t}

theorem mem_support_of {k : ℕ} {τ₀ τ : PureDat G t →₀ ℂ} (h₀ : IsCosetExpansion S t Φ β k τ₀)
    (h : IsCosetExpansion S t Φ β k τ) {d : PureDat G t} (hd : d ∈ τ.support) : d ∈ τ₀.support := by
  obtain ⟨-, ⟨e, he, h1, h2⟩, h3⟩ := h
  obtain ⟨-, ⟨e₀, he₀, h1₀, h2₀⟩, h3₀⟩ := h₀
  have hee : e₀ = e := GlobalTheory.StepVecSum.idemSum_eq (G.V (.top 0)) he he₀
  subst hee
  choose x hx _ hx' using (h3 d hd).1
  choose y hy _ hy' using (h3 d hd).2
  have ex : ∀ j, (d.1 j).fn (x j) = 1 := fun j => by rw [hx', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have ey : ∀ i, (d.2 i).fn (y i) = 1 := fun i => by rw [hy', Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]; rfl
  have hs : (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = τ d := by
    rw [Finsupp.sum, Finset.sum_eq_single_of_mem d hd]
    · simp [ex, ey]
    · intro d' hd' hne
      by_contra h0
      obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
      exact hne (pureDat_eq (h3 d' hd') (h3 d hd) (h1 d' hd') (h1 d hd)
        (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
        (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩))
  have hxe := fun j => ((h1 d hd).1 j).2.1 ▸ hx j
  have hye := fun i => ((h1 d hd).2 i).2.1 ▸ hy i
  have hne : (τ₀.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) ≠ 0 := by
    rw [h2₀ x y hxe hye, ← h2 x y hxe hye, hs]
    exact Finsupp.mem_support_iff.1 hd
  obtain ⟨d', hd', h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 h0
  have hdd : d' = d := pureDat_eq (h3₀ d' hd') (h3 d hd) (h1₀ d' hd') (h1 d hd)
    (fun j => ⟨x j, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h4) j (Finset.mem_univ _), by rw [ex]; exact one_ne_zero⟩)
    (fun i => ⟨y i, Finset.prod_ne_zero_iff.1 h5 i (Finset.mem_univ _), by rw [ey]; exact one_ne_zero⟩)
  exact hdd ▸ hd'

end Sums

theorem finite_pureDat_of_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  intro D T L sc G W U S t Φ β k
  by_cases h : ∃ τ₀, IsCosetExpansion S t Φ β k τ₀
  · obtain ⟨τ₀, h₀⟩ := h
    exact τ₀.support.finite_toSet.subset fun d ⟨τ, hτ, hd⟩ => mem_support_of h₀ hτ hd
  · refine Set.finite_empty.subset ?_
    rintro d ⟨τ, hτ, -⟩
    exact h ⟨τ, hτ⟩

end GlobalTheory.RowTest.CosetFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePureDataOfCosetIndicatorExpansionsDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ), {d : PureDat G t | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}.Finite := by
  first | exact @GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth | exact GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth | (intros; apply GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

namespace GlobalTheory.ChoiceSurjectivity

theorem choice_phi_surj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F _ ch _ Φ
  obtain ⟨i⟩ := GlobalTheory.TestLat.SlopeModel.nonempty_idx (LaP ch.G)
  refine ⟨ch.e.symm ((Φ, Quotient.mk'' 1), i), ?_⟩
  simp [Choice.Phi, datumOf]

end GlobalTheory.ChoiceSurjectivity
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.rowTestChoice_datum_surjective : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  first | exact @GlobalTheory.ChoiceSurjectivity.choice_phi_surj | exact GlobalTheory.ChoiceSurjectivity.choice_phi_surj | (intros; apply GlobalTheory.ChoiceSurjectivity.choice_phi_surj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.NFJetProof

theorem exists_nf_of_finite (E : Set ℂ) (hE : E.Finite) (hA : ∀ z ∈ E, IsAlgebraic ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ E ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite E := hE.to_subtype
  refine ⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩

def dset {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) : Set (PureDat G t) :=
  {d | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}

end GlobalTheory.NFJetProof

namespace GlobalTheory.NFJetProof

theorem jetCl_of_choice {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (hI : GlobalTheory.NormSum.Inp D) (hok : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hD : GlobalTheory.SumSize.DictAt ch) : InNF fun _ σ => JetCl σ ch.S.toGridChoice := by
  have hok' : ∀ t Φ, ch.S.SumOK t Φ := fun t Φ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
    exact hok t a
  haveI : Finite T := hS.fin
  haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
  set S := ch.S.toGridChoice with hSdef
  let E : Set ℂ := ⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β,
    ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪
      (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))
  have hE : E.Finite := by
    refine Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ =>
      Set.Finite.biUnion (GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth S t Φ β _) fun d _ => ?_
    haveI := (hok' t Φ).cls β
    exact Set.finite_iUnion fun c => Set.Finite.union
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
  have hA : ∀ z ∈ E, IsAlgebraic ℚ z := by
    intro z hz
    simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩ := hz
    obtain ⟨hk, hexp, hcos⟩ := hτ
    obtain ⟨e, -, hP, -⟩ := id hexp
    have hw := (hok' t Φ).wts
    have hv := (hok' t Φ).vec β τ hexp d hdτ
    rcases h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk
        ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _
        (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b
  obtain ⟨M, hM, hsub⟩ := exists_nf_of_finite E hE hA
  refine ⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩

theorem nfJet_holds : SumOKK → (∀ D, GlobalTheory.NormSum.Inp D) → (Big fun ch => GlobalTheory.SumSize.DictAt ch) → NFJet := by
  intro h1 h2 h3
  obtain ⟨C, hC⟩ := Big.and h1 h3
  refine ⟨C, fun ε CF hCF => ?_⟩
  obtain ⟨x, hx⟩ := hC ε CF hCF
  exact ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1
      (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩

end GlobalTheory.NFJetProof
end
end
end
