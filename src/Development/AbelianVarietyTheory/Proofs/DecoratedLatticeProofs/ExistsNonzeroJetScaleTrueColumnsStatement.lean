module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.GoodLatCM

section

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

section Lat

variable {E : Type} [Field E] [NumberField E]

end Lat

end Formalism.MainNotions.Ext

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

theorem discr_K {R : Ranks} (H : Host R) : discr H.K = -(H.d : ℤ) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hm : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx : (⟨H.sqd, hm⟩ : H.K) ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) := by
    apply Subtype.ext
    push_cast
    exact H.sqd_sq
  refine Formalism.HF.P.quadDiscr_ne_one H.K (-(H.d : ℤ)) _ hx ?_ ?_ ?_ ?_
  · have key : @IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {⟨H.sqd, hm⟩} = ⊤ := by
      apply IntermediateField.map_injective (IntermediateField.val H.K)
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
        Set.image_singleton]
      first
      | rfl
      | (simp only [IntermediateField.val_mk]; rfl)
      | simp [Formalism.HC.HostRaw.K]
    convert key
    all_goals first
      | exact Subsingleton.elim _ _
      | (apply Algebra.algebra_ext; intro r; simp [Algebra.algebraMap_eq_smul_one])
  · exact Int.squarefree_natAbs.mp (by simpa using hdp.prime.squarefree)
  · omega
  · omega

end Formalism.MainNotions.Ext
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiZeroEmbeddingValue

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical
namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xi_zero_embedding_value (D : D7) (hc : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℝ) :=
    ((Formalism.BasicNotions.factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 D.host.hyp.2.1.pos)
  rw [Host.xi0, hc, Ideal.absNorm_top, map_div₀, map_mul, h1, map_natCast, map_neg, map_one]
  have : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  push_cast
  field_simp
  simp

theorem stdPair_world {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (hψ : IsStdChar (I.rec7 l Z) ψ (-1)) (hθ : IsInfFam θ)
    (i : ℕ) : StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ := by
  obtain ⟨hs, hX, -⟩ := hI.spaces
  have hg : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]
    refine Matrix.ext fun a b => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs (B.R.N j) (fun _ => false) (B.R.N j) 0 a b).trans ?_
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn]; rfl)
    · rw [Matrix.one_apply_ne h]
      exact if_neg h
  have hr : ∀ j, ((I.rec7 l Z).sp.X j).rank = B.R.N j := fun j => by
    have e : (I.rec7 l Z).sp.X j = Formalism.BasicNotions.Examples₂.posSpace hs (B.R.N j) := hX j
    rw [e]; rfl
  have hev : ∀ j, Even (B.R.N j) := fun j =>
    B.R.k_even.add (Even.mul_left (B.R.t_odd.add_one) j)
  have hδ : I.J.δ ≠ 0 := I.J.δ_ne_zero
  have hd : 0 < Real.sqrt B.host.d := Real.sqrt_pos.2 (Nat.cast_pos.2 B.host.hyp.2.1.pos)
  refine ⟨hψ, hθ, hg _, hg _, (I.rec7 l Z).sp.X_sig _, (I.rec7 l Z).sp.X_sig _, ?_, B.ccK_top, hδ,
    xi_zero_embedding_value _ B.ccK_top, ?_⟩
  · rw [hr, hr]
    refine ⟨?_, ?_, hev _, hev _⟩
    · have := B.R.m_add_three_le_k; unfold Ranks.N; omega
    · unfold Ranks.N; nlinarith
  · have hA := Formalism.MainNotions.Ext.area_lamOf (I.rec7 l Z) ⊤ top_ne_bot I.J.δ hδ
    rw [Formalism.MainNotions.Ext.discr_K (I.rec7 l Z).host, Ideal.absNorm_top] at hA
    have hA' : Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ) = ‖I.J.δ‖ ^ 2 * Real.sqrt B.host.d / 2 := by
      refine hA.trans ?_
      simp
      exact Or.inl rfl
    show (Formalism.MainNotions.TaylorLogMetric.area (Th.lamOf B.host ⊤ I.J.δ))⁻¹ * ‖I.J.δ‖ ^ 2 = 2 * (Real.sqrt B.host.d)⁻¹
    rw [hA']
    have : ‖I.J.δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
    field_simp

end GlobalTheory.AdForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns

section

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumnsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonzero_jetScale_trueColumns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∃ s, JetS I l Z ψ θ s := by
  first | exact @GlobalTheory.AdForm.JetScales.exists_jetS | exact GlobalTheory.AdForm.JetScales.exists_jetS | (intros; apply GlobalTheory.AdForm.JetScales.exists_jetS <;> assumption)
end
end
