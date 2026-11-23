module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatricesStatement
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
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompactStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNe

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem gramSkew_rat {D : D7} (W : HSp D) {ρ : ℕ} (y : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y) = rat ((-D.host.xi0) • (gramQ W y)ᵀ) := by
  have e : adj (rat y) ⬝ (gA W ⬝ rat y) = rat (gramQ W y) := by
    rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, e, rat_smul, map_neg]
  rfl

theorem gramQ_eq_of_gramSkew {D : D7} (W : HSp D) {ρ : ℕ} {x y : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y)) : gramQ W x = gramQ W y := by
  rw [gramSkew_rat, gramSkew_rat] at h
  have h' := rat_injective h
  have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D))
  exact Matrix.transpose_injective (smul_right_injective _ hξ h')

theorem exists_central_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  intro D ψ hψ V V₀ W ρ d x₀ x hne
  by_contra hcon
  push_neg at hcon
  have hall : ∀ c : skewA D ρ, ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) := by
    intro c
    have hn : ‖ψ (d.qS W c (rat x₀))‖ = 1 := hψ.1.2.1 _
    have hs : ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    calc ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) := by
          rw [hs, one_mul]
      _ = ψ (d.qS W c (rat x₀)) := by rw [mul_assoc, hcon c, mul_one]
  have h := (((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.2 ψ hψ).2.2 (rat x) (rat_mem x) (rat x₀) (rat_mem x₀)
  exact hne (gramQ_eq_of_gramSkew W (h.1 hall))

end GlobalTheory.Unf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  first | exact @GlobalTheory.Unf.exists_central_ne | exact GlobalTheory.Unf.exists_central_ne | (intros; apply GlobalTheory.Unf.exists_central_ne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Reindex

variable {D : D7}

theorem exists_rat_block {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hq : γ ∈ GQ V)
    (hn : γ ∈ flagN d) : ∃ (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E),
      blockX d γ = u.1.1 ∧ rat u₀ = u.1.1 := by
  obtain ⟨u, hu, h⟩ := GlobalTheory.JacClosed.flagN_le d hn
  have hb : blockX d γ = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  have hr : blockX d γ ∈ ratMx D ρ ρ :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))
  obtain ⟨u₀, hu₀⟩ := mem_ratMx.1 hr
  exact ⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩

theorem det_eq_one {ρ : ℕ} (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) (h : rat u₀ = u.1.1) :
    u₀.det = 1 := by
  have h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0 := fun i j hij => incA_injective (by
    rw [map_zero]
    have := congrFun (congrFun h i) j
    change incA D (u₀ i j) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i j).1 hij)
  have h1 : ∀ i : Fin ρ, u₀ i i = 1 := fun i => incA_injective (by
    rw [map_one]
    have := congrFun (congrFun h i) i
    change incA D (u₀ i i) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i i).2)
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]
  simp [h1]

theorem gramQ_mul (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u₀) = u₀ᴴ * gramQ W x * u₀ := by
  simp only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.Unf.Reindex


open GlobalTheory.Unf.Reindex in
theorem GlobalTheory.Unf.tsum_offBase_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  intro D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ
  obtain ⟨u, u₀, hb, hu₀⟩ := exists_rat_block d hq hn
  have hdet : IsUnit u₀.det := by rw [det_eq_one u u₀ hu₀]; exact isUnit_one
  have hdet' : IsUnit u₀ᴴ.det := by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one
  set G₀ := gramQ W x₀
  have hG : u₀ᴴ * G₀ * u₀ = G₀ := by
    apply rat_injective
    have := hx₀.2 u.1 u.2
    rw [rat_mul, rat_mul, rat_conjTranspose, hu₀]
    rw [Matrix.mul_assoc]; exact this
  have key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀ := by
    intro x
    rw [gramQ_mul]
    constructor
    · intro h
      have h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀ := h.trans hG.symm
      have h3 := congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2
      simp only [Matrix.mul_assoc] at h3
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet] using h3
    · intro h; rw [h, hG]
  have hinv : u₀ * u₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv' : u₀⁻¹ * u₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  let e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃
      {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} :=
    { toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩
      invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by
        have := (key (x.1 * u₀⁻¹)).2 h
        rwa [Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩
      left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])
      right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }
  have hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀},
      term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1 := by
    intro x
    refine (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_
    rw [rat_mul, hu₀, hb]
  rw [tsum_congr hterm]
  exact Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  first | exact @GlobalTheory.Unf.tsum_offBase_invariant | exact GlobalTheory.Unf.tsum_offBase_invariant | (intros; apply GlobalTheory.Unf.tsum_offBase_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContribute

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf



theorem GlobalTheory.Unf.cut_gram_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS vN x₀ Th hB hTh Ψ hΨ
  have lemR : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent D ψ V V₀ W ρ d χV χW om om' hW hW' vS x₀ hB
  have lemQ : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne D ψ hW.std V V₀ W ρ d x₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hH, hFD, h1⟩ := vN.unit

  have hBc : ∀ (c : skewA D ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∀ x,
      term ψ d W vS (om (d.nC c, 1) Φ) x = ψ (d.qS W c (rat x)) * term ψ d W vS Φ x := by
    intro c Φ hΦ x
    have h := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ).1 x 0 1 c
    rw [d.nB_zero, Subgroup.coe_one, map_one, mul_one, mul_one] at h
    rw [h]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, Matrix.mul_zero]
    rfl
  have hsplit : ∀ g h : GA D V, om (g * h, 1) Ψ = om (g, 1) (om (h, 1) Ψ) := by
    intro g h
    rw [show ((g * h, (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply]
  let F : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} → flagN d → ℂ :=
    fun i n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
  let a : skewA D ρ → Matrix (Fin W.rank) (Fin ρ) D.host.E → ℂ :=
    fun c x => star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x))
  have hE : ∀ i c (n : flagN d), F i (⟨d.nC c, d.nC_mem_NFlag c⟩ * n) = a c i.1 * F i n := by
    intro i c n
    simp only [F, a, Subgroup.coe_mul]
    rw [hTh.cen c n.1 n.2, hsplit, hBc c _ (hW.om_pres _ _ hΨ)]
    ring

  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS
  obtain ⟨-, hM⟩ := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  obtain ⟨-, hcl, hnorm, K, hK, hKc⟩ := hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)
  have hdisc : DiscreteTopology (NFlagQ V d.e) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V))
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h)))
  have hcl' : IsClosed (((GlobalTheory.MixPer.centre d).subgroupOf (flagN d) : Subgroup (flagN d)) : Set (flagN d)) := by
    rw [Subgroup.coe_subgroupOf]; exact hcl.preimage continuous_subtype_val
  have hcpt : ∃ K' : Set ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), IsCompact K' ∧
      ∀ m, ∃ γ ∈ (NFlagQ V d.e).subgroupOf ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), ∃ k ∈ K', m = γ * k := by
    let φ : GlobalTheory.MixPer.centre d → (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) := fun c =>
      ⟨⟨c.1, (hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)).1 c.2⟩, Subgroup.mem_subgroupOf.2 c.2⟩
    have hφ : Continuous φ := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
    refine ⟨φ '' K, hK.image hφ, fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨φ γ, ?_, φ k, ⟨k, hk, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hγ))
    · refine Subtype.ext (Subtype.ext ?_)
      change m.1.1 = γ.1 * k.1
      exact congrArg Subtype.val e
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    (hTh.cont.mul ((hT Ψ hΨ).2.2.2.1 i.1 |>.comp (continuous_subtype_val.prodMk continuous_const))).measurable
  have hbd : ∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B := by
    obtain ⟨K, hK, hKc⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D V ρ d.e (isIsoSub_e d)).1
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hTh.cont.continuousOn
    obtain ⟨C, A, hCA⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
    refine ⟨M.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal, fun n => ?_⟩
    have hTn : ‖Th n.1‖ₑ ≤ ENNReal.ofReal M := by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      rw [Subgroup.coe_mul, hTh.left γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 k.1 k.2, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM k hk)
    have hS := hCA 1 1 n.1 n.2
    rw [mul_one] at hS
    calc ∑' i, ‖F i n‖ₑ = ‖Th n.1‖ₑ * ∑' i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀},
          ‖term ψ d W vS (om (n.1, 1) Ψ) i.1‖ₑ := by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun i => enorm_mul _ _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
          mul_le_mul' hTn ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans hS)
      _ = _ := by rw [ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul]
  have hinv : ∀ γ ∈ NFlagQ V d.e, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n := by
    intro γ hγ n
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit, tsum_mul_left, tsum_mul_left,
      lemR γ.1 hγ' γ.2 _ (hW.om_pres _ _ hΨ)]
  have hcinv : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∀ γ ∈ NFlagQ V d.e, γ ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) → ∀ n,
      ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 (γ * n) =
        ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 n := by
    intro c γ hγ hγM n
    refine tsum_congr fun i => ?_
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hγM
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit]
    congr 1
    refine (hT _ (hW.om_pres _ _ hΨ)).2.1 γ.1 hγ' γ.2 i.1.1 i.1.1 ?_
    rw [blockX_of_fix d (mem_fixer.2 (hc' ▸ d.nC_jX c')), Matrix.mul_one]
  have heig : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∃ u ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∃ a : ℂ, a ≠ 1 ∧ ∀ i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, id i = c →
      ∀ m ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∀ n, F i (m * u * n) = a * F i (m * n) := by
    intro c
    obtain ⟨c', hc'⟩ := lemQ c.1 c.2
    refine ⟨⟨d.nC c', d.nC_mem_NFlag c'⟩, Subgroup.mem_subgroupOf.2 ⟨c', rfl⟩, a c' c.1, hc', ?_⟩
    intro i hi m hm n
    subst hi
    obtain ⟨c'', hc''⟩ := Subgroup.mem_subgroupOf.1 hm
    have : m = ⟨d.nC c'', d.nC_mem_NFlag c''⟩ := Subtype.ext hc''.symm
    subst this
    rw [mul_assoc, hE, hE, hE]
    simp only [id]
    ring
  exact GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν (NFlagQ V d.e) ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)) j4 hdisc hnorm hcl' hcpt
    vN.𝓝 hFD (by rw [h1]; exact ENNReal.one_ne_top) _ _ id F hmeas hbd hinv hcinv heig
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContributeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  first | exact @GlobalTheory.Unf.cut_gram_base | exact GlobalTheory.Unf.cut_gram_base | (intros; apply GlobalTheory.Unf.cut_gram_base <;> assumption)
end
end
