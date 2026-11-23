module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.InfCharAct
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
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
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import Formalism.RealPlaceAnalysis.StatementE
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyAdj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CapCoefGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTFr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyExponentOfFormalDegree
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.InfCharDSGOf

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Finset
open scoped InnerProductSpace ContDiff Convolution ComplexOrder

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.S.UnitaryLevelOperators Formalism.QuantumDeterminants

def InfCharDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
    ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → thrX ε < h →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

end Formalism.MainNotions.GapDS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyCapA

section

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem anyCap_word_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (w : List (Fin n × Fin n)) {x : M} (hx : x ∈ genSub E V) :
    (w.map fun p => E p.1 p.2).prod x ∈ genSub E V := by
  induction w with
  | nil => simpa using hx
  | cons p w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact ICD.gen_stable ih p.1 p.2

theorem anyCap_adj {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (V : Submodule ℂ M) (u : ℂ) :
    ∃ C : Module.End ℂ M, (∀ x ∈ genSub E V, C x ∈ genSub E V) ∧
      ∀ x y : M, inner ℂ x (Formalism.REAL.qdet E u y) = inner ℂ (C x) y := by
  classical
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  refine ⟨(l.map fun c => (starRingEnd ℂ c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod).sum, ?_, ?_⟩
  · intro x hx
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
      exact add_mem (Submodule.smul_mem _ _ (anyCap_word_mem _ hx)) ih
  · intro x y
    rw [hl]
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
      rw [ih]
      congr 1
      have h := eword_adjoint hU c.2 y x
      have h' : inner ℂ x ((c.2.map fun p => E p.1 p.2).prod y) =
          starRingEnd ℂ (c.2.map fun p => adjSign ε p.1 p.2).prod *
            inner ℂ (((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod x) y := by
        rw [← inner_conj_symm, h, map_mul, inner_conj_symm]
      rw [h', map_mul, starRingEnd_self_apply]
      ring

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyCap

section

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem anyCap (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (v : smD ε σ) :
    Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  classical
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨V, hV, hV0, hVK, hc, htop⟩ := cf_datum_of_copies hDS hgap
    (fun V hV hVK => casOnDatum_of_isDS hDS hgap hD hV hVK)

  have hM : ∀ x ∈ genSub (smE ε σ) V, Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) x =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x :=
    fun x hx => capelli_data hgap hσ hD hV hc hVK hV0 hP hcap Y x hx

  obtain ⟨C, hCM, hC⟩ := anyCap_adj hU V (Y + ((n : ℂ) - 1) / 2)
  have hCv : ∀ x ∈ genSub (smE ε σ) V,
      C x = starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x := by
    intro x hx
    have hmem : C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x ∈ genSub (smE ε σ) V :=
      sub_mem (hCM x hx) (Submodule.smul_mem _ _ hx)
    have h0 : inner ℂ (C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x)
        (C x - starRingEnd ℂ (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y) • x) = 0 := by
      rw [inner_sub_left, ← hC, hM _ hmem, inner_smul_right, inner_smul_left, starRingEnd_self_apply, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

  rw [← sub_eq_zero]
  have hperp : ((Formalism.REAL.qdet (smE ε σ) (Y + ((n : ℂ) - 1) / 2) v -
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v : smD ε σ) : H) ∈
      ((genSub (smE ε σ) V).map (smD ε σ).subtype)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
    rw [Submodule.subtype_apply, ← Submodule.coe_inner, inner_sub_right, hC, hCv x hx, inner_smul_left,
      inner_smul_right, starRingEnd_self_apply, sub_self]
  have htop' : ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure = ⊤ := htop
  rw [Submodule.topologicalClosure_eq_top_iff.1 htop'] at hperp
  exact Subtype.ext ((Submodule.mem_bot ℂ).1 hperp)

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.InfCharG

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory

namespace Formalism.MainNotions.BesselDiscreteSeries

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem infChar_of_model {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ)
    (hgap : StdGap ε lam) {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g) :
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  haveI : CompleteSpace H := hDS.1
  intro v hv Y
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hm : v ∈ smD ε σ := mem_smD_of_smoothVecs hv
  have hc := anyCap hDS hgap hP hcap Y ⟨v, hm⟩
  rw [actU_qdet hσ _ v hm, hc]
  rfl

theorem isPsiFor_compact {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : S7.IsMu lam μ) :
    IsPsiFor ε lam T (S7.PsiM T μ) := by
  refine ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
    fun g hg => S7.psiM_casimir T μ hμ hg, fun ν hν => ?_⟩
  haveI : CompactSpace (S7.UJ ε) := cmpt_compact (cmpt_eps_eq hpq)
  haveI := hν
  haveI : IsFiniteMeasure ν := inferInstance
  have hc : Continuous (fun g : S7.UJ ε => S7.PsiM T μ (S7.toM g)) :=
    (S7.psiM_continuousOn T μ hμ).comp_continuous (Units.continuous_val.comp continuous_subtype_val)
      (fun g => g.2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun g => hC g (Set.mem_univ _))

theorem infinitesimal_character_discrete_series_gap : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrX ε < h →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v := by
  intro n ε lam H _ _ σ hlam hDS h hh hthr
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (S7.PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • S7.PsiM T μ g :=
    fun Y g hg => S7.psiCapelli ε lam T μ hμ Y g hg
  rcases Nat.eq_zero_or_pos (S7.q0 ε) with h0 | hq
  ·
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := Nat.min_eq_zero_iff.1 h0
    exact infChar_of_model hDS (cf_stdGap_of_pq hpq hlam.1) (isPsiFor_compact hpq T μ hμ) hcap
  ·
    have hX : Formalism.MainNotions.GapDS.thrDS ε ≤ Formalism.MainNotions.GapDS.thrX ε ∧
        120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ Formalism.MainNotions.GapDS.thrX ε :=
      ⟨le_max_left _ _, le_max_right _ _⟩
    have hq1 : (1 : ℝ) ≤ (S7.q0 ε : ℝ) := by exact_mod_cast hq
    have e1 : (S7.q0 ε : ℝ) ≤ (S7.q0 ε : ℝ) ^ ((3 : ℝ) / 2) := by
      have := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
      simpa using this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
      have e2 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
        have : 8 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * (S7.q0 ε : ℝ) := by nlinarith
        have e3 : 120 * (n : ℝ) * (S7.q0 ε : ℝ) ≤ 120 * (n : ℝ) * ((S7.q0 ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
        linarith
      linarith [hX.2]
    have hstd : StdGap ε lam := ⟨hlam.1, h, hh, lt_of_le_of_lt hX.1 hthr⟩
    exact infChar_of_model hDS hstd (S7.isPsiFor_psiM ε lam h T μ hlam hμ hh hq h8).1 hcap

theorem gapped_infinitesimal_character : Formalism.MainNotions.GapDS.InfCharDSG := infinitesimal_character_discrete_series_gap

end Formalism.MainNotions.BesselDiscreteSeries
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsCC

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem coefCap_carrierInT_own (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h) :
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀) := by
  intro j0 Y g hg
  obtain ⟨j, rfl⟩ : ∃ j : Fin (nfE D), j = j0 := ⟨j0, rfl⟩
  obtain ⟨g, rfl⟩ : ∃ g' : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, g' = g := ⟨g, rfl⟩
  set w := tauE X e j with hw
  set τ := e (plE D j) with hτ
  have hpl : X.pl w = τ := by
    show X.pl (X.pl.symm (e (plE D j))) = _
    exact Equiv.apply_symm_apply _ _
  obtain ⟨hQP, hPQ, hH, -⟩ := isTransp_Qcs X C w
  rw [hpl] at hQP hPQ hH
  set P := Qcs C τ
  set Q := Qics C τ
  set σ := X.B.σ w
  set ε := X.B.I.ε w
  have hσ : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := (X.ds w).2.2.1
  have hbm : (b j : X.B.H w) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ := Formalism.MainNotions.BesselDiscreteSeries.mem_smD_of_smoothVecs (hb j)
  set T0 : X.Vloc u' w →L[ℂ] X.Vloc u w := (innerSL ℂ (ξ' j)).smulRight (ξ j)
  have hF : ∀ h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      hᴴ * (Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P) * h = Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P →
      fcT X C e u u' a b ξ ξ' cc j h =
        (inner ℂ (a j) (σ (P * h * Q) ((⟨b j, hbm⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : X.B.H w))) • (cc j • T0) := by
    intro h _
    rw [fcT_eq]
    unfold Formalism.MainNotions.S.Pv.BetaCut.coefM
    rw [smul_smul, mul_comm, ← smul_smul]
    congr 1
    ext y
    simp [T0, smul_smul, mul_comm]
    rfl
  have hg' : gᴴ * (Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P) * g = Pᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * P := by
    have : gᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hg
    rw [← hH] at this; exact this
  obtain ⟨hh, hgapw, hthr⟩ := hgap w
  have hcap := Formalism.MainNotions.BesselDiscreteSeries.gapped_infinitesimal_character X.B.I.n ε (X.B.lam w) (X.B.H w) σ (hHC w) (X.ds w) hh hgapw hthr
    (b j) (hb j) (Y : ℂ)
  rw [Formalism.MainNotions.BesselDiscreteSeries.actU_qdet hσ _ (b j) hbm] at hcap
  have hn : (X.B.I.n : ℂ) = ((Formalism.FourierDecayAlt.Q.mdim D.R.k D.R.rS 0 : ℕ) : ℂ) := by
    rw [X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R]
    unfold Formalism.FourierDecayAlt.Q.mdim
    simp
  show Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (Formalism.FourierDecayAlt.Q.uC D.R.k D.R.rS 0 (Y : ℂ))
    (fcT X C e u u' a b ξ ξ' cc j) g = _
  rw [← hH]
  refine (Formalism.L2.SG.Pf.CapCoef.capelliH_cf_rect (ε := ε) (σ := σ) hσ hQP hPQ (a j) (cc j • T0) ⟨b j, hbm⟩ _ hF _ hg').trans ?_
  have hu : Formalism.FourierDecayAlt.Q.uC D.R.k D.R.rS 0 (Y : ℂ) = (Y : ℂ) + ((X.B.I.n : ℂ) - 1) / 2 := by
    unfold Formalism.FourierDecayAlt.Q.uC; rw [hn]
  rw [hu, hcap, map_smul, inner_smul_right, ← smul_smul, ← hF g hg']
  congr 1

  rw [Formalism.MainNotions.BridgeLemma.capelliPoly_ofReal]
  congr 1
  show ∏ s, ((Y : ℝ) + X.B.lam w s) = ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)).P Y
  rw [Formalism.L2.SG.Pf.SzHypOf.gOf_place, Formalism.MainNotions.BridgeLemma.cfg_P]
  simp only [X.lam_eq w, hpl]
  exact Fintype.prod_equiv (finCongr X.n_eq) _ _ (fun i => rfl)

instance factCoefCapAll : Fact CoefCapAll :=
  ⟨by
    intro D X θ C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap
    exact coefCap_carrierInT_own X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap⟩

end Formalism.L2.SG.Pf.CarrierT
end
end
end
