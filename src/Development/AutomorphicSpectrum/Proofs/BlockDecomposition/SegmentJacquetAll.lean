module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatApplyEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import GroundTheory.LocalFields.PadicLogSeries
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInductionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwoStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.JacStages

namespace GlobalTheory.CompanionTheory.CoarseOcc

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  haveI : Nontrivial W := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  refine ⟨(v : V), 0, fun h0 => hu ?_⟩
  have hv0 : v = 0 := Subtype.ext h0
  rw [hv0, map_zero]

theorem sum_concat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s : ℕ}
    (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ i, (x a i).1 := by
  calc ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
        Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
    _ = ∑ a, ∑ i, (x a i).1 := Fintype.sum_sigma _

theorem exists_one_le_jm_coarse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  intro k _ _ _ _ hA s N c x _ hcat V _ _ π hs _ h1
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := (sum_concat c x).symm.trans hcat
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s N d e c (fun a b => (x a b).1) e' V π
  have hsub : IsSubquotient (piTensor fun l => (concat c x l).rep) (jac (refinePlace e e') π) := by
    rw [hE]
    exact jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
  have hnt := nontrivial_of_isSubquotient (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (concat c x)) hsub
  have hnt2 := @Function.Surjective.nontrivial _ _ hnt _ φS.symm.surjective
  have hnt3 := @Function.Surjective.nontrivial _ _ hnt2 _
    (Submodule.Quotient.mk_surjective (twKer (jac e π) (relUnipD k e') 1))
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hnt3
  let T : IrrRep (Levi k fun a => Fin (d a)) := ⟨Y, τ, hτs.isSmooth (isSmooth_jac e hs), hτ⟩
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d T
  refine ⟨fun a => ⟨d a, σ a⟩, hd, fun _ => rfl, ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)⟩
  exact (isSubquotient_of_equiv φ.symm).trans hτs

end GlobalTheory.CompanionTheory.CoarseOcc

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.concatenated_jacquet_multiplicity_factorization : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  first | exact @GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | exact GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | (intros; apply GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.SegCoarse

end
end
end
