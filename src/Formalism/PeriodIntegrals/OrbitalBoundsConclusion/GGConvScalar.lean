module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.AveragingOperatorIdempotent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.ConvScalarOfLitOf

section

@[expose] public section

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem convScalar_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff) (h5 : RankLeOne)
    (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) (hm : GelfandGraevMultOne) :
    ConvScalar := by
  intro F _ _ k ψ₀ hψ V _ _ _ π hπ
  have hu : IsUni k (1 : GL (Fin k) F) :=
    ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩
  have hpsi1 : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    simp only [psiNat, if_pos hu, psiU]
    have hs : superdiag k ((1 : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = 0 := by
      unfold superdiag
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hij : i ≠ j := by
          intro e
          rw [e] at h
          omega
        simp [Matrix.one_apply_ne hij]
      · rfl
    rw [hs, AddChar.map_zero_eq_one]
  have hgam : gam ψ₀ (1 : GL (Fin k) F) =
      (cardU F k : ℂ)⁻¹ * (Fintype.card (GL (Fin k) F) : ℂ) := by
    unfold gam
    simp [hpsi1]
  have hG0 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU0 : (cardU F k : ℂ) ≠ 0 := by
    haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, hu⟩⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdim := h9 F k V π hπ
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  obtain ⟨c, hc⟩ := h6 F k V π hπ (repGam ψ₀ π) fun g => h2 F k ψ₀ V π g
  have htr := h7 F k ψ₀ V π
  rw [hc, h8 V (projQ ψ₀ π) (h3 F k ψ₀ V π), map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hc, hgam]
  split_ifs with hgen
  · have hne := (h4 F k ψ₀ V π).mp hgen
    have hr1 : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) = 1 := by
      have hle := h5 hm F k ψ₀ hψ V π hπ
      have hpos : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≠ 0 := fun h0 =>
        hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
      omega
    rw [hr1, Nat.cast_one, mul_one] at htr
    have hcv : c = (Fintype.card (GL (Fin k) F) : ℂ) / (Module.finrank ℂ V : ℂ) := by
      rw [eq_div_iff hd0]
      exact htr
    rw [smul_smul, hcv]
    congr 1
    field_simp
  · have hz : projQ ψ₀ π = 0 := by
      by_contra h
      exact hgen ((h4 F k ψ₀ V π).mpr h)
    rw [hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero] at htr
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp htr with h | h
      · exact h
      · exact absurd h hd0
    rw [hc0, zero_smul, smul_zero]

theorem convScalarOfLit_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm

end PI.GGConvScalarW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.IntertwinerRankLeOne

section

@[expose] public section

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_sgn_mul (π : Representation ℂ (GL (Fin k) F) V) (x : GL (Fin k) F) (v : V) :
    π (sgn k) (π x v) = π (sgn k * x * sgn k) (π (sgn k) v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc (sgn k * x),
    sgn_mul_self, mul_one]

theorem pi_sgn_sgn (π : Representation ℂ (GL (Fin k) F) V) (v : V) : π (sgn k) (π (sgn k) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, sgn_mul_self, map_one, Module.End.one_apply]

theorem whit_sgn_projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V)
    (hℓ : IsWhit ψ₀ π ℓ) (v : V) : ℓ (π (sgn k) (projQ ψ₀ π v)) = ℓ (π (sgn k) v) := by
  have hterm : ∀ x : GL (Fin k) F, psiNat ψ₀ x * ℓ (π (sgn k) (π x v)) =
      (if IsUni k x then (1 : ℂ) else 0) * ℓ (π (sgn k) v) := by
    intro x
    rw [pi_sgn_mul]
    by_cases hx : IsUni k x
    · rw [hℓ _ (isUni_sgn_conj hx), ← mul_assoc, if_pos hx]
      unfold psiNat
      rw [if_pos hx, mul_comm (psiU ψ₀ x), psiU_sgn_conj]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_mul, zero_mul]
  unfold projQ

  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_boole_uni, ← mul_assoc, inv_mul_cancel₀ (cardU_ne_zero F k), one_mul]

theorem isWhit_of_dual (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (f : Module.Dual ℂ V) :
    IsWhit ψ₀ π (f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k))) := by
  intro u hu v
  have hq := LinearMap.congr_fun (projQ_comp_pi ψ₀ π (isUni_sgn_conj hu)) (π (sgn k) v)
  simp only [LinearMap.comp_apply] at hq ⊢
  rw [pi_sgn_mul, hq, LinearMap.smul_apply, map_smul, smul_eq_mul,
    inv_eq_of_mul_eq_one_right (psiU_sgn_conj ψ₀ u)]

theorem generic_iff_criterion : GenericIff := by
  intro F _ _ k ψ₀ V _ _ π
  constructor
  · rintro ⟨ℓ, hne, hw⟩ hQ
    apply hne
    ext v
    have := whit_sgn_projQ ψ₀ π ℓ hw (π (sgn k) v)
    rw [hQ, LinearMap.zero_apply, map_zero, map_zero, pi_sgn_sgn] at this
    rw [← this, LinearMap.zero_apply]
  · intro hQ
    obtain ⟨v, hv⟩ : ∃ v, projQ ψ₀ π v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (LinearMap.ext h)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f (projQ ψ₀ π v) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    refine ⟨f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k)), ?_, isWhit_of_dual ψ₀ π f⟩
    intro h0
    apply hf
    have := LinearMap.congr_fun h0 (π (sgn k) v)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, pi_sgn_sgn] at this
    exact this

theorem intertwiner_rank_le_one : RankLeOne := by
  intro hm F _ _ k ψ₀ hψ V _ _ _ π hirr
  set T : V →ₗ[ℂ] V := projQ ψ₀ π ∘ₗ π (sgn k) with hTdef
  have hsurj : LinearMap.range (π (sgn k)) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨π (sgn k) v, pi_sgn_sgn π v⟩
  have hrT : LinearMap.range T = LinearMap.range (projQ ψ₀ π) :=
    LinearMap.range_comp_of_range_eq_top _ hsurj
  rw [← hrT, ← LinearMap.finrank_range_dualMap_eq_finrank_range T]
  by_cases h : ∃ ℓ₁ ∈ LinearMap.range T.dualMap, ℓ₁ ≠ 0
  · obtain ⟨ℓ₁, ⟨f₁, rfl⟩, hne⟩ := h
    have hle : LinearMap.range T.dualMap ≤ Submodule.span ℂ {T.dualMap f₁} := by
      rintro _ ⟨f₂, rfl⟩
      obtain ⟨c, hc⟩ := hm F k ψ₀ hψ V π hirr _ _ (isWhit_of_dual ψ₀ π f₁) (isWhit_of_dual ψ₀ π f₂) hne
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton hne).le
  · push_neg at h
    rw [(Submodule.eq_bot_iff _).2 h, finrank_bot]
    omega

end PI.GGConvScalarW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.RepresentationDimensionPos

section

@[expose] public section

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  congr 1
  exact Subsingleton.elim a b

theorem representation_dimension_pos : DimPos := by
  intro F _ _ k V _ _ _ π hπ
  haveI := nontrivial_of_irreducible π hπ
  exact Module.finrank_pos

theorem schur_lemma_complex : SchurC := by
  intro F _ _ k V _ _ _ π hπ f hf
  haveI := nontrivial_of_irreducible π hπ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) →
      π g v ∈ LinearMap.ker (f - c • LinearMap.id) := by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
    have h1 := congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← map_smul, ← map_sub, hv, map_zero]
  let W : Subrepresentation π := ⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rcases hs.eq_bot_or_eq_top W with hW | hW
  · exfalso
    apply hv.2
    have hvW : v ∈ LinearMap.ker (f - c • LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul, sub_self]
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    rw [h2] at hvW
    have h3 : v ∈ (⊥ : Submodule ℂ V) := hvW
    simpa using h3
  · apply LinearMap.ext
    intro x
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    have hx : x ∈ LinearMap.ker (f - c • LinearMap.id) := by
      rw [h2]
      exact (show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa [sub_eq_zero] using hx

end PI.GGConvScalarW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar

section

@[expose] public section

theorem convolution_scalar : Formalism.L2.SG.GGMirabolic.ConvScalarOfLit :=
  PI.GGConvScalarW.convScalarOfLit_of PI.GGConvScalarW.representation_conjugate_gamma PI.GGConvScalarW.representation_commutes_gamma
    PI.GGConvScalarW.averaging_operator_idempotent PI.GGConvScalarW.generic_iff_criterion PI.GGConvScalarW.intertwiner_rank_le_one
    PI.GGConvScalarW.schur_lemma_complex PI.GGConvScalarW.trace_representation_gamma PI.GGConvScalarW.idempotent_trace_formula
    PI.GGConvScalarW.representation_dimension_pos
end
end
