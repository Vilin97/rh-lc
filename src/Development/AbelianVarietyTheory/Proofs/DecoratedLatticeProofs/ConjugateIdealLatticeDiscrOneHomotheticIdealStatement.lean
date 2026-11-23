module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedAreaClassInvariant

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise


open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dite_eq_left (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdeal

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ConjLatticeCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem conj_lattice_core :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hC := GlobalTheory.ConjLattice.containsData hM
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := hC.1
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => GlobalTheory.ConjLattice.lamConj_spec GlobalTheory.ConjLattice.uniformization_holds M ρ'
    (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  have hfix : ∀ ρ' : M →ₐ[ℚ] ℂ, EquidistributedConjugates.FixesK D M ρ' → ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ,
      x ≠ 0 ∧ lamConj M ρ' (lamOf D cc δ) = lamOf D c x := by
    intro ρ' hρ'
    obtain ⟨cc', δ', hc', -, he⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ ⟨hcc, hδ⟩ M ρ'
      (GlobalTheory.ConjEquidistrib.fixK_of_fixesK D M ρ' hm hρ') h2 h3 1 one_pos
    exact ⟨cc', hc'.1.1, δ', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc' hc'.1 δ' hc'.2, he⟩
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · exact hfix ρ hρ
  · have hρ' : EquidistributedConjugates.FixesK D M (EquidistributedConjugates.conjEmb M ρ) :=
      (GlobalTheory.ConjEquidistrib.fixesK_conjEmb_iff D M ρ hm).2 hρ
    obtain ⟨c, hc, x, hx, hxe⟩ := hfix _ hρ'
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds
        GlobalTheory.ConjLattice.uniformization_holds
    have hmap : (lamConj M ρ (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj =
        lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [GlobalTheory.ConjLattice.discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [GlobalTheory.ConjLattice.eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [GlobalTheory.ConjLattice.eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj := by
      rw [← hmap, GlobalTheory.ConjLattice.map_cj_map_cj]
    refine ⟨c.map (GlobalTheory.ConjLattice.conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx,
      by rw [hback, hxe, GlobalTheory.ConjLattice.lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (GlobalTheory.ConjLattice.conjO D).injective] at hbot
    exact hc hbot

end GlobalTheory.ConjLatticeCore
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdealStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem _root_.GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧ lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  first | exact @GlobalTheory.ConjLatticeCore.conj_lattice_core | exact GlobalTheory.ConjLatticeCore.conj_lattice_core | (intros; apply GlobalTheory.ConjLatticeCore.conj_lattice_core <;> assumption)
end
end
