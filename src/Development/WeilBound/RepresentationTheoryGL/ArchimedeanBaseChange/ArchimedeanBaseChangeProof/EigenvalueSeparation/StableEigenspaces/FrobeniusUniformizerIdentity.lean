module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralCompactLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTensA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.SizeBounds.SizetHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.StableHulls.IsStableHull

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterpolationLocalL2Bound

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
      (hm ψ hψ).aestronglyMeasurable
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvEqOfCentral

section

@[expose] public section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have : T2Space (GA E N) := by
    have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have : T1Space (GA E N) := T2Space.t1Space
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSp

section

@[expose] public section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.CenteigHolds

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.S2.Clozel

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem trace_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (V : Submodule ℂ (Sm E a))
    (τ : E →+* ℂ) (m : Multiset ℂ) (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end centeig

theorem centeig_holds : CentEig := by
  intro E _ _ _ N V m hm
  refine ⟨∑ τ : E →+* ℂ, (m τ).sum, fun φ hφ t g => ?_⟩
  refine GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ ?_ t g
  rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => centeig.trace_eq V τ (m τ) (hm τ) φ hφ

end PositivityTheory.Rg.BcB.E.E3

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.IsStableEigenspaceCap

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

theorem isStable_eigenspace_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (τ : E →+* ℂ)
    (u c : ℂ) : _root_.GlobalTheory.CuspRep.IsStable (Module.End.eigenspace (cap (a := N) τ u) c) := by
  intro o φ hφ
  rw [Module.End.mem_eigenspace_iff] at hφ ⊢
  rw [← Module.End.mul_apply, (GlobalTheory.SpehInfChar.cap_commute_act τ u o).eq, Module.End.mul_apply, hφ, map_smul]

theorem isStable_autSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} :
    _root_.GlobalTheory.CuspRep.IsStable (GlobalTheory.DiscClosure.autSub E N) := by
  intro o φ hφ
  exact PositivityTheory.Rg.Rs.PrAut.isAutForm_act PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL o hφ

end centeig

theorem hullaut_holds : HullAut := by
  intro E _ _ _ N S hS
  refine ⟨fun φ hφ => ?_, fun τ m hm => ⟨hm.1, fun u φ hφ => ?_⟩⟩
  · have hle : hull S ≤ GlobalTheory.DiscClosure.autSub E N := sInf_le ⟨fun ψ h => hS ψ h, centeig.isStable_autSub⟩
    exact hle hφ
  · have hle : hull S ≤ Module.End.eigenspace (cap (a := N) τ u) ((m.map (u + ·)).prod) :=
      sInf_le ⟨fun ψ h => Module.End.mem_eigenspace_iff.2 (hm.2 u ψ (Submodule.subset_span h)),
        centeig.isStable_eigenspace_cap τ u _⟩
    exact Module.End.mem_eigenspace_iff.1 (hle hφ)

end PositivityTheory.Rg.BcB.E.E3

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FrobeniusUniformizerIdentity

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.E.E3

theorem frobenius_uniformizer_identity (h : LocNonPosGlue) : PositivityTheory.Rg.BcB.E.E3 :=
  asm_holds fintype_holds (GlobalTheory.CompanionTheory.LocSlice.locSlGlue sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC GlobalTheory.CompanionTheory.InterpLoc.interpolation_local_L2_bound)
    (h sizet_holds) centeig_holds (GlobalTheory.CompanionTheory.CentRe.centReGlue_holds sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC) hullaut_holds
    GlobalTheory.CompanionTheory.HullExp.hullNonPos GlobalTheory.CompanionTheory.PairSpProof.pairSp

end PositivityTheory.Rg.BcB.E.E3
end
end
