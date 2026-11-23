module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CohomologicalCsdTemperedOfUsed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPowStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumeration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRep

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_of_isL_singleton : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  intro k _ _ _ _ Δ N V _ _ π h
  obtain ⟨h', x, hd, ⟨Δ', ⟨hm, -⟩, hL⟩, hc⟩ := h
  have hcard : h' = 1 := by
    have := congrArg Multiset.card hm
    simpa using this
  subst hcard
  have hΔ : Δ' 0 = Δ := by
    have hmem : Δ' 0 ∈ Finset.univ.val.map Δ' := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [hm] at hmem
    simpa using hmem
  have hL0 : IsLSeg Δ (x 0).rep := hΔ ▸ hL 0
  obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hN : y.1 = N := by simpa using hd
  subst hN
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y hd
  obtain ⟨φ⟩ := hc.unique ((isCosocle_self y.2.rep.irr).of_equiv (.refl _) ψ)
  exact hL0.of_equiv φ

end GlobalTheory.CompanionTheory.LocGL
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRepStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.langlands_single_segment_is_segment_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  first | exact @GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | exact GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | (intros; apply GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedAntitoneLastNonpos

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Inequalities

theorem weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by
  intro h d e hh hd he hs
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  refine ⟨Fin.last (n + 1), by simp, ?_⟩
  have hf : Finset.univ.filter (fun i : Fin (n + 2) => Fin.last (n + 1) ≤ i)
      = {Fin.last (n + 1)} := by
    ext i
    simp [Fin.last_le_iff]
  rw [hf, Finset.sum_singleton]
  have hle : (∑ i, d i) * e (Fin.last (n + 1)) ≤ 0 := by
    rw [Finset.sum_mul, ← hs]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (he (Fin.le_last i)) (hd i).le
  have hpos : 0 < ∑ i, d i :=
    Finset.sum_pos (fun i _ => hd i) ⟨Fin.last _, Finset.mem_univ _⟩
  have hel : e (Fin.last (n + 1)) ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hpos (not_le.mp hc)) (not_lt.mpr hle)
  exact mul_nonpos_of_nonneg_of_nonpos (hd _).le hel

end GlobalTheory.CompanionTheory.Inequalities
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SquareIntegrableSegments

theorem length_le_one_of_partial_products {h : ℕ} (d e f : Fin h → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : ∀ i, 0 < d i) (he : Antitone e) (hf : ∀ i, f i = q ^ (d i * e i))
    (hpart : ∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), f (Fin.rev i) < 1)
    (hfull : ∏ i, f (Fin.rev i) = 1) : h ≤ 1 := by
  by_contra hh
  have h2 : 2 ≤ h := by omega
  have hlog : Real.log q ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hprod : ∀ s : Finset (Fin h), ∏ i ∈ s, f i = q ^ (∑ i ∈ s, d i * e i) := fun s => by
    rw [Real.rpow_sum_of_pos hq0]
    exact Finset.prod_congr rfl fun i _ => hf i
  have htot : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, f i = 1 := by
      rw [← hfull]
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [hprod] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_one] at h3
    exact (mul_eq_zero.1 h3).resolve_right hlog
  obtain ⟨j, hj0, hj⟩ := GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos h d e h2 hd he htot
  have hlt := hpart (Fin.rev j) (by have := j.isLt; rw [Fin.val_rev]; omega)
  have hrw := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h f (Fin.rev j)
  rw [Fin.rev_rev] at hrw
  rw [hrw, hprod] at hlt
  exact absurd hlt (not_lt.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1.le hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isLSeg {Δ : Segment k} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  rw [← hd, Segment.sum_term_fst]

theorem sum_deg_of_listing {h : ℕ} {D : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (hD : Finset.univ.val.map D = 𝔪) : ∑ i, (D i).deg = (𝔪.map Segment.deg).sum := by
  rw [← hD, Multiset.map_map]
  rfl

theorem exists_class (hE : Zc.LSegExists k) (Δ : Segment k) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨π, hd, hc⟩ := hE Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hd,
    hc.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (Representation.Equiv.refl _)⟩

theorem card_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type}
      [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible →
        IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  intro k _ _ _ _ hS hC hE 𝔪 N V _ _ π hN hsm hirr hsq hL
  choose y hy using exists_class hE
  have hdeg : ∀ Δ, (y Δ).1 = Δ.deg := fun Δ => (deg_eq_of_isLSeg (hy Δ)).symm
  have hpos : ∀ Δ, 0 < (y Δ).1 := fun Δ => by
    rw [hdeg]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  choose s hs using fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hpos Δ)
  obtain ⟨h, D, hD, hanti, hno⟩ := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing 𝔪 s Segment.Precedes
    fun a b hab => GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (s a) (s b) (hy a) (hy b) (hs a) (hs b) hab
  let x : Fin h → IrrGL (k := k) := fun i => y (D i)
  have hLF : LFactors 𝔪 x := ⟨D, ⟨hD, hno⟩, fun i => hy (D i)⟩
  have hsum : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨D', ⟨hD', -⟩, hx'⟩, -⟩ := hL
    rw [← hd']
    have e1 : ∑ a, (x a).1 = ∑ a, (D a).deg := Finset.sum_congr rfl fun a _ => hdeg (D a)
    have e2 : ∑ a, (x' a).1 = ∑ a, (D' a).deg :=
      Finset.sum_congr rfl fun a _ => (deg_eq_of_isLSeg (hx' a)).symm
    rw [e1, e2, sum_deg_of_listing hD, sum_deg_of_listing hD']
  have hsumrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hsum]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hsoc := hS 𝔪 h N x hsumrev hLF π hL
  have hposrev : ∀ a, 0 < ((x ∘ Fin.rev) a).1 := fun a => hpos _
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hsumrev π hsm hposrev hsoc
  have hex := hC N π hN hsm hirr hsq h (x ∘ Fin.rev) hsumrev hposrev hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hnabs := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  choose c hc using fun i => GlobalTheory.T.central_character_exists k (x i) t
  obtain ⟨hpart, hfull⟩ := hex t ht (c ∘ Fin.rev) fun i => hc (Fin.rev i)
  have hle : h ≤ 1 := length_le_one_of_partial_products (fun i => ((x i).1 : ℝ)) (fun i => s (D i))
    (fun i => ‖c i‖) (nabs_pos' k t) hnabs (fun i => by exact_mod_cast hpos (D i)) hanti
    (fun i => hs (D i) t (c i) (hc i)) hpart hfull
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hcard : 𝔪.card = h := by
    rw [← hD]
    simp
  omega

end GlobalTheory.CompanionTheory.SquareIntegrableSegments
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegmentStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.square_integrable_single_segment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | exact GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | (intros; apply GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.Development

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

noncomputable section

namespace Zz

theorem zblsegsingle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := GlobalTheory.T.langlands_single_segment_is_segment_rep

theorem zbz1core : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := GlobalTheory.T.square_integrable_single_segment

theorem sqInt_isLSeg (hE : GlobalTheory.Published.LanglandsExhaustionGL) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (hS : Zc.LSocleGL k)
    (hC : Zl.CasselmanNecSq k) (hL : Zc.LSegExists k) (δ : IrrGL (k := k)) (h1 : 1 ≤ δ.1) (hδ : IsSqIntCoeff δ.rep) :
    ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  obtain ⟨𝔪, h𝔪⟩ := hE k δ
  have hc := zbz1core k hS hC hL 𝔪 δ.1 δ.rep h1 δ.2.rep.smooth δ.2.rep.irr hδ h𝔪
  obtain ⟨Δ, rfl⟩ := Multiset.card_eq_one.1 hc
  exact ⟨Δ, zblsegsingle k Δ δ.1 δ.rep h𝔪⟩

end Zz

end
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TempProdUsedOf

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.Zltwo

theorem essSqIntUsed_of (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      Zc.LSegExists k) : EssSqIntUsed := by
  intro k _ _ _ _ _ δ h1 hδ
  exact Zz.sqInt_isLSeg hE k (hS k) (Zl.JC.casselmanNecSq_holds k) (hL k) δ h1 hδ

end PositivityTheory.Zltwo
end
end
end
