module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalarStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMulStatement
public import Mathlib.Basic.Real.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOne
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormulaStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalar

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalarStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.central_character_eq_of_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
  first | exact @GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | exact GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique | (intros; apply GlobalTheory.CompanionTheory.ScalarUniq.scalarBy_unique <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree

section

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel Matrix

namespace GlobalTheory.CompanionTheory.ScalarTwist

theorem acts_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ g (φ.toIntertwiningMap v) = c • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem scalarBy_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ) (h : Zl.ScalarBy x t c) :
    Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext; simp [GeneralLinearGroup.scalar]
  refine acts_of_equiv (x.twEquiv (absPow k s) (isSmoothChar_absPow s)) (g := GeneralLinearGroup.scalar (Fin x.1) t) ?_
  intro v
  rw [twist_apply, h v, detChar_apply, hdet, smul_smul]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.ScalarTwist
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegreeStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.central_character_twist_pow_degree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | exact GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | (intros; apply GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealPowPartialSegmentLtOneStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.real_pow_partial_segment_lt_one : ∀ (α r : ℝ) (d l0 l1 : ℕ), 0 < α → α < 1 → 0 < r → 1 ≤ d → 1 ≤ l0 → 1 ≤ l1 → r ^ (l0 + l1) * α ^ (d * ((l0 + l1) * (l0 + l1 - 1) / 2)) = 1 → r ^ l0 * α ^ (d * (l0 * l1 + l0 * (l0 - 1) / 2)) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | exact GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one | (intros; apply GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplit

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegJacquet

theorem exists_isTopCut_two_of_jhMult_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π →
    ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 →
    ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  intro k _ _ _ _ Δ N V _ _ π hJ hπ x hd hpos hne
  by_contra hno
  exact hne ((hJ Δ π hπ 2 x hd hpos).2 hno)

end GlobalTheory.CompanionTheory.SegJacquet
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetTwoFactorSplitStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.segment_jacquet_two_factor_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π → ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  first | exact @GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | exact GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SegJacquet.exists_isTopCut_two_of_jhMult_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrable

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegLink

theorem one_le_deg_of_isLSeg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Δ : Segment k} {y : IrrGL (k := k)} (hL : IsLSeg Δ y.rep) : 1 ≤ y.1 := by
  obtain ⟨hd, -⟩ := hL
  have hterm : ∀ a, (Δ.term a).fst = Δ.d := fun a => rfl
  rw [← hd]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem norm_top_eq (r A : ℝ) (d d0 l0 l1 m : ℕ) (h : d0 = d) :
    (r * (A ^ l1) ^ d) ^ l0 * (A ^ d0) ^ m = r ^ l0 * A ^ (d * (l0 * l1 + m)) := by
  subst h
  ring

theorem centredSegSqInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  intro k _ _ _ _ hCas hIA hLJ Δ y hL hU
  have hN : 1 ≤ y.1 := one_le_deg_of_isLSeg hL
  have hmax : Zls.MaxExpStrict y.rep := by
    intro x hd hpos hjm t ht c hc
    obtain ⟨Γ, ⟨hlen, hfirst⟩, hΓ⟩ := GlobalTheory.T.segment_jacquet_two_factor_split k Δ y.1 _ y.rep hLJ hL x hd hpos hjm
    obtain ⟨hα0, hα1, hnorm⟩ := GlobalTheory.T.contracting_unit_abs_pow_bounds k t ht
    obtain ⟨c0, hc0⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k Δ.first.fst _ Δ.first.rep Δ.first.snd.rep.smooth
      Δ.first.snd.rep.irr (hIA k _ _ _ Δ.first.snd.rep.smooth Δ.first.snd.rep.irr) t
    obtain ⟨cy, hcy⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k y.fst _ y.rep y.snd.rep.smooth y.snd.rep.irr
      (hIA k _ _ _ y.snd.rep.smooth y.snd.rep.irr) t
    have hprod := GlobalTheory.T.jacquet_two_factor_central_character_mul k y.fst _ y.rep x hd hjm t cy (c 0) (c 1) hcy (hc 0) (hc 1)
    have hcy1 : ‖cy‖ = 1 := hU t cy hcy
    have hy1 := hU t _ (GlobalTheory.T.segment_rep_central_character_formula k Δ y hL t c0 hc0)
    rw [norm_mul, norm_pow, norm_pow, hnorm, ← pow_mul] at hy1
    have hr : 0 < ‖c0‖ := by
      rcases (norm_nonneg c0).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (Nat.pos_iff_ne_zero.mp Δ.len_pos), zero_mul] at hy1
        exact zero_ne_one hy1
    have hlen2 : (Γ 0).len + (Γ 1).len = Δ.len := by rw [← hlen, Fin.sum_univ_two]
    rw [← hlen2] at hy1
    have hb0 : Zc.below Γ 0 = (Γ 1).len := by
      simp [Zc.below, Finset.sum_filter, Fin.sum_univ_two]
    have hf0 : (Γ 0).first.fst = Δ.first.fst := by rw [hfirst 0]; rfl
    have hG0 : Zl.ScalarBy (Γ 0).first t
        (c0 * ↑((GlobalTheory.SmGL.absPow k ↑(Zc.below Γ 0)) t) ^ Δ.first.fst) := by
      rw [hfirst 0]
      exact GlobalTheory.T.central_character_twist_pow_degree k Δ.first t c0 _ hc0
    have he0 := GlobalTheory.T.central_character_eq_of_scalar k (x 0) t _ _ (hc 0) (GlobalTheory.T.segment_rep_central_character_formula k (Γ 0) (x 0) (hΓ 0) t _ hG0)
    have hn0 : ‖c 0‖ = ‖c0‖ ^ (Γ 0).len * GlobalTheory.SplitWeil.nabs k t ^
        (Δ.first.fst * ((Γ 0).len * (Γ 1).len + (Γ 0).len * ((Γ 0).len - 1) / 2)) := by
      rw [he0, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hnorm, hnorm, hb0]
      exact norm_top_eq _ _ _ _ _ _ _ hf0
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have hp : (∏ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ‖c i‖) = ‖c 0‖ := by
        simp [Finset.prod_filter, Fin.prod_univ_two]
      rw [hp, hn0]
      exact GlobalTheory.T.real_pow_partial_segment_lt_one _ _ _ _ _ hα0 hα1 hr Δ.d_pos (Γ 0).len_pos (Γ 1).len_pos hy1
    · rw [Fin.prod_univ_two, ← norm_mul, hprod, hcy1]
  exact @hCas y.1 _ _ _ y.rep hN y.snd.rep.smooth y.snd.rep.irr (fun t c hc => hU t c hc) hmax

end GlobalTheory.CompanionTheory.SegLink
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrableStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.centred_segment_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  first | exact @GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | exact GlobalTheory.CompanionTheory.SegLink.centredSegSqInt | (intros; apply GlobalTheory.CompanionTheory.SegLink.centredSegSqInt <;> assumption)
end
end
