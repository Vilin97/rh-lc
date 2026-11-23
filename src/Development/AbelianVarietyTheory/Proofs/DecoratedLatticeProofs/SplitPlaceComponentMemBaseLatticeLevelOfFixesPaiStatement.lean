module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralVectorsComponentIffIntegralFrameCoordStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDiv
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDivStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.PairKeep.keep | exact GlobalTheory.PairKeep.keep | (intros; apply GlobalTheory.PairKeep.keep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryKeepsBaseLatticeOfSplitComponents

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.SplitStab

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (hS : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) R (c : E) ∈ S)
    (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (y : Fin m → E ⊗[F] R) :
    y ∈ Formalism.UG.latS (F := F) R S Λ ↔ (∀ j, y j ∈ S) ∧
      ∀ j : Fin m, j.1 + 1 = m → ∃ s ∈ S, y j = Formalism.UG.inclE (F := F) R (t : E) * s := by
  constructor
  · intro hy
    unfold Formalism.UG.latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, hΛ] at hx
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨r, hr, -⟩ := hx j
        simp only [hr]; exact hS r
      · obtain ⟨r, hr, hd⟩ := hx j
        obtain ⟨c, rfl⟩ := hd hj
        refine ⟨_, hS c, ?_⟩
        simp only [hr]; push_cast; rw [map_mul]
    | zero => exact ⟨fun j => zero_mem _, fun j _ => ⟨0, zero_mem _, by simp⟩⟩
    | add a b _ _ ha hb =>
      refine ⟨fun j => add_mem (ha.1 j) (hb.1 j), fun j hj => ?_⟩
      obtain ⟨s1, hs1, e1⟩ := ha.2 j hj
      obtain ⟨s2, hs2, e2⟩ := hb.2 j hj
      exact ⟨s1 + s2, add_mem hs1 hs2, by simp [Pi.add_apply, e1, e2, mul_add]⟩
    | smul a b _ hb =>
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        exact mul_mem a.2 (hb.1 j)
      · obtain ⟨s, hs, e⟩ := hb.2 j hj
        refine ⟨(a : E ⊗[F] R) * s, mul_mem a.2 hs, ?_⟩
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, e]
        ring
  · rintro ⟨h1, h2⟩
    have key : ∀ (j : Fin m) (r : 𝓞 E), (j.1 + 1 = m → t ∣ r) → ∀ s ∈ S,
        Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) ∈ Formalism.UG.latS (F := F) R S Λ := by
      intro j r hr s hs
      have hx : (Pi.single j (r : E) : Fin m → E) ∈ Λ := by
        rw [hΛ]; intro i
        by_cases hij : i = j
        · subst hij; exact ⟨r, by simp, hr⟩
        · exact ⟨0, by simp [hij], fun _ => dvd_zero _⟩
      have : (Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) : Fin m → E ⊗[F] R) =
          (⟨s, hs⟩ : S) • (fun i => Formalism.UG.inclE (F := F) R ((Pi.single j (r : E) : Fin m → E) i)) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [Subring.smul_def]
        · simp [hij, Subring.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.1 + 1 = m
    · obtain ⟨s, hs, e⟩ := h2 j hj
      rw [e, mul_comm]; exact key j t (fun _ => dvd_refl _) s hs
    · simpa using key j 1 (fun h => absurd h hj) (y j) (h1 j)

end GlobalTheory.SplitStab

theorem GlobalTheory.SplitStab.stab_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  intro F E _ _ _ _ _ σ v k _ _ _ _ φ hS m t Λ hΛ q hq hq' M hM h h' hh hhh' hA hB
  have hSO : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (c : E) ∈
      Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
  have ht : (t : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, map_zero] at hq
    have h1 : ((q.1 : 𝒪[k]) : k) = 0 := (valuation k).zero_iff.mp hq.symm
    exact q.2.ne_zero (by simpa using h1)
  have hint : ∀ x : k, x ∈ 𝒪[k] ↔ valuation k x ≤ 1 := fun x => Valuation.mem_integer_iff (valuation k) x
  set σ' := Formalism.UG.sigR σ (v.adicCompletion F) with hσ'
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι

  have hchar : ∀ y : Fin m → E ⊗[F] v.adicCompletion F,
      y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ ↔
      (((∀ r, (fun j => φ (y j)) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (fun j => φ (y j)) r0 = φ (ι (t : E)) * s) ∧
        ∀ r, (fun j => φ (σ' (y j))) r ∈ 𝒪[k]) := by
    intro y
    rw [GlobalTheory.SplitStab.mem_latS_iff (F := F) (v.adicCompletion F) _ hSO m t Λ hΛ y]
    simp only [hS]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun r => (h1 r).1, fun r0 hr0 => ?_⟩, fun r => (h1 r).2⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      exact ⟨φ s, hs.1, by rw [e, map_mul]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun r => ⟨h1 r, h3 r⟩, fun r0 hr0 => ?_⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      have hu : ι (t : E) * ι ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      refine ⟨ι ((t : E)⁻¹) * y r0, ?_, ?_⟩
      · constructor
        · have hu' : φ (ι ((t : E)⁻¹)) * φ (ι (t : E)) = 1 := by rw [← map_mul, mul_comm, hu, map_one]
          rw [map_mul, show φ (y r0) = φ (ι (t : E)) * s from e, ← mul_assoc, hu', one_mul]
          exact hs
        · have hu' : φ (σ' (ι ((t : E)⁻¹))) * φ (σ' (ι (t : E))) = 1 := by
            rw [← map_mul, ← map_mul, mul_comm, hu, map_one, map_one]
          have hv : valuation k (φ (σ' (ι ((t : E)⁻¹)))) = 1 := by
            have := congrArg (valuation k) hu'
            rw [map_mul, hq', mul_one, map_one] at this
            exact this
          rw [map_mul, map_mul]
          exact mul_mem ((hint _).2 hv.le) (h3 r0)
      · rw [← mul_assoc, hu, one_mul]

  have hU : (M.val.map (φ.comp σ'))ᵀ * h = 1 := by
    have h0 : Formalism.UG.cT σ' (M : Matrix (Fin m) (Fin m) _) * 1 * (M : Matrix (Fin m) (Fin m) _) = 1 := hM
    rw [Matrix.mul_one] at h0
    have := congrArg (fun X => X.map φ) h0
    simp only [Formalism.UG.cT] at this
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← hh]
    simpa [Matrix.transpose_map] using this
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  have hσM : M.val.map (φ.comp σ') = h'ᵀ := by
    have : (M.val.map (φ.comp σ'))ᵀ = h' := by
      calc (M.val.map (φ.comp σ'))ᵀ = (M.val.map (φ.comp σ'))ᵀ * (h * h') := by rw [hhh', Matrix.mul_one]
        _ = h' := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← this, Matrix.transpose_transpose]
  intro y
  rw [hchar y, hchar]
  have e1 : (fun j => φ (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j)) = h *ᵥ (fun j => φ (y j)) := by
    funext j; rw [RingHom.map_mulVec, hh]; rfl
  have e2 : (fun j => φ (σ' (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j))) = h'ᵀ *ᵥ (fun j => φ (σ' (y j))) := by
    funext j
    have := RingHom.map_mulVec (φ.comp σ') (M : Matrix (Fin m) (Fin m) _) y j
    rw [← hσM]
    exact this
  rw [e1, e2]
  exact and_congr (hA _) (hB _)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryKeepsBaseLatticeOfSplitComponentsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.unitary_keeps_baseLattice_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  first | exact @GlobalTheory.SplitStab.stab_of_split_components | exact GlobalTheory.SplitStab.stab_of_split_components | (intros; apply GlobalTheory.SplitStab.stab_of_split_components <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMemBaseLatticeLevelOfFixesPai

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

open GlobalTheory.AdForm




theorem GlobalTheory.AdForm.std_comp_mem_levelVL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) b i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i →
    ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
    x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ Formalism.UG.levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v (A.K j hj b).lev.Lb := by
  intro B X I hI hP l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b i g hg x hx
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hL, hS3⟩ := hS2 j hj
  obtain ⟨hLat, hVal⟩ := hS3 i
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : X.piT u ∈ (e i).1.asIdeal := (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hsq : X.piT u ∉ (e i).1.asIdeal ^ 2 := hPr.piT_notMem_sq hX u (e i).2
  have hconj : B.fields.conjO (X.piT u) ∉ (e i).1.asIdeal := fun h => by
    obtain ⟨s, t, hst⟩ := hcop
    have : (1 : 𝓞 B.fields.E) ∈ (e i).1.asIdeal := by
      rw [← hst]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ h)
    exact (e i).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨φ, hφ1, hφ2, hφ3, hφ4⟩ := GlobalTheory.T.exists_splitPlace_component_ringHom_integral _ k (p i) (e i).1 (he i)
  obtain ⟨⟨q, hq⟩, hc⟩ := GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime _ k (p i) (e i).1 (he i) (X.piT u) (B.fields.conjO (X.piT u)) hmem hsq hconj
  have hlat := GlobalTheory.T.mem_integralVectors_component_iff_integral_frame_coords _ k (p i) _ _ (β j i) (L j) hL _ hLat
  have hv6 := GlobalTheory.T.functional_values_integral_vectors_of_integer_vectors _ k (p i) (e i).1 (he i) _ (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat
    (B.fields.conjO (X.piT u)) (fun z hz r hr => hVal z ((hL z).2 hz) r hr)
  have hn := rankN (I.rec7 l Z) j hj
  obtain ⟨hhh, hkeep, hkeep'⟩ := GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv k _ _ hn (β j i).b (β j i).b' (β j i).bb' (β j i).b'b (Q j i) hlat _
    (φ (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F) ((X.piT u : 𝓞 B.fields.E) : B.fields.E)))
    q ((congrArg (valuation k) (hφ2 _)).trans hq) hc hv6 g hg
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hj).1
  have hU := Formalism.UG.P.afsplit_bc_mem (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v x.1 x.2
  refine Subgroup.mem_inf.2 ⟨hU, ?_⟩
  have hU1 : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈
      Formalism.UG.UJ (Formalism.UG.sigR (sigD (I.rec7 l Z)) ((p i).v.adicCompletion (I.rec7 l Z).host.F)) 1 := by
    have h1 : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈
        Formalism.UG.UJ (Formalism.UG.sigR (sigD (I.rec7 l Z)) ((p i).v.adicCompletion (I.rec7 l Z).host.F))
          ((gramN (I.rec7 l Z) j hj).map (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F))) := hU
    have hJ : (gramN (I.rec7 l Z) j hj).map (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) ((p i).v.adicCompletion (I.rec7 l Z).host.F)) = 1 := by
      rw [hg1]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [hJ] at h1
  have hM : (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1).val.map φ =
      ((β j i).b * g.val * (β j i).b').reindex (finCongr hn) (finCongr hn) := by
    rw [← (β j i).gl_mat g]
    ext r s
    simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    change φ (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (x.1.1 r s)) = _
    rw [hx]
    simp only [finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    rw [hφ1]
  exact GlobalTheory.T.unitary_keeps_baseLattice_of_split_components _ _ (sigD (I.rec7 l Z)) (p i).v k φ hφ4 _ (X.piT u) (A.K j hj b).lev.Lb (fun y => (hA.reads j hj).lb b y) q ((congrArg (valuation k) (hφ2 _)).trans hq)
    ((congrArg (valuation k) (hφ3 _)).trans hc) _ hU1 _ _ hM hhh hkeep hkeep'
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMemBaseLatticeLevelOfFixesPaiStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.splitPlace_component_mem_baseLattice_level_of_fixes_pair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) b i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i →
    ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
    x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v) x.1 ∈ Formalism.UG.levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (p i).v (A.K j hj b).lev.Lb := by
  first | exact @GlobalTheory.AdForm.std_comp_mem_levelVL | exact GlobalTheory.AdForm.std_comp_mem_levelVL | (intros; apply GlobalTheory.AdForm.std_comp_mem_levelVL <;> assumption)
end
end
