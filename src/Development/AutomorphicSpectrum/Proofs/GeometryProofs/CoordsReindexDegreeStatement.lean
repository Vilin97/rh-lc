module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalZeroOfMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import Mathlib.RingTheory.WittVector.IsPoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]


theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

end NefAddBlock

end GroundTheory.Heights₂.Heights
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCurvePoint

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]

theorem ker_red_le {W : Ideal (MRing J)} (hpW : (C (p : ℤ) : MRing J) ∈ W) :
    RingHom.ker (Bridge.GeoNum.red (ι := J) p) ≤ W := by
  classical
  rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
  exact hpW

theorem map_red_prime [DecidableEq K] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : MRing J) ∈ W) : NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) := by
  have hker := ker_red_le p hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2

theorem exists_curve_point {W : Ideal (MRing J)} (hW : IsMultiProjPrime W) (hpW : (C (p : ℤ) : MRing J) ∈ W)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : (Σ k, J k) → L) (c : ∀ k, J k),
      Algebra.trdeg (ZMod p) L = 1 ∧ (∀ k, w ⟨k, c k⟩ = 1) ∧ mCoordIdeal w = W := by
  classical
  obtain ⟨hQ, hQd⟩ := NefAddBlock.map_red p hW hpW 1 hdim
  have hcm := Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)
  set Q := W.map (Bridge.GeoNum.red p)
  have := hQ.isPrime
  obtain ⟨n, hn, hrn⟩ := FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ
  have hn1 : n = 1 := by
    rw [hQd] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  choose c hc using hQ.relevant
  let π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) :=
    (algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ g, π g = 0 ↔ g ∈ Q := fun g => by
    change algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) := fun x => π (X x)
  have hy₀ := hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]
  have hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0 := fun k h => hc k ((hπ _).1 h)
  have hW₀ : mCoordIdeal y₀ = W := by
    refine le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)
    · rw [← hcm]
      exact (hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))
    · exact (hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))
  have hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q := fun x =>
    IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x,
      isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩
  refine ⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c,
    by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩
  rw [← hW₀, mCoordIdeal_ratioPt y₀ c hyc]
  exact (mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm

theorem dim_le {L : Type} [Field L] [Algebra (ZMod p) L] (hL : Algebra.trdeg (ZMod p) L ≤ 1) (w : (Σ k, J k) → L) :
    (C (p : ℤ) : MRing J) ∈ mCoordIdeal w ∧ ∃ m : ℕ, m ≤ 1 + Fintype.card K ∧
      ringKrullDim (NumbersDVR.MRing J (ZMod p) ⧸ (mCoordIdeal w).map (Bridge.GeoNum.red p)) = m := by
  classical
  let Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L := aeval fun x => C (w x) * X x.1
  have hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f x hf => simp only [map_mul, hf, map_X]; simp [mConeMap, Φ]
  have hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p) := by
    ext g
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hΦ]
    rfl
  have hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ := by
    rw [hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]
  refine ⟨?_, ?_⟩
  · rw [hcm]
    refine Bridge.GeoNum.ker_le_comap p _ ?_
    rw [Bridge.GeoNum.ker_red]
    exact Ideal.mem_span_singleton_self _
  · rw [hm]
    have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime _
    obtain ⟨m, h1, h2⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p)
      (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)
    refine ⟨m, ?_, h1⟩
    have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)
    rw [h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at h3
    have h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal) := h3.trans (by gcongr)
    exact_mod_cast h4

end LevelTowerAlt
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresBlockEmbedding

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial in
theorem LevelTowerAlt.nef_fibres_block_embedding : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro _ Ω Ω' _ _ _ i K K' _ _ J J' _ _ y y' bk bx a a' hbk hy hy' ha ha' hnef W hW hle hchar hdim
  have hp : (charOf W).Prime := PB.prime_charOf_of_ne_zero hW.1 hchar
  have hpW := Inter.C_charOf_mem W
  generalize charOf W = p at hp hpW
  have : Fact p.Prime := ⟨hp⟩
  let v : (Σ k, J k) → Σ k, J' k := fun x => ⟨bk x.1, bx x.1 x.2⟩
  have hv : IsBlockMap bk v := by
    refine ⟨hbk, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, x⟩ ⟨k₁, x₁⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl := hbk h1
      obtain rfl := (bx k).injective (eq_of_heq h2)
      rfl
    · rintro ⟨_, x⟩ ⟨k, rfl⟩
      exact ⟨⟨k, (bx k).symm x⟩, by simp [v]⟩
  obtain ⟨L, _, _, w, c, hL, hc, hw⟩ := LevelTowerAlt.exists_curve_point p hW hpW hdim
  have hle' : mCoordIdeal (fun x : Σ k, J k => y' ⟨bk x.1, bx x.1 x.2⟩) ≤ mCoordIdeal w := by
    simp only [hy]
    rw [hw, CoordinateConeArithVar.mCoordIdeal_comp i y]
    exact hle
  obtain ⟨k₀, L₁, _, _, σ, _, _, w₀, w', h1, h2, h3, h4⟩ := LevelTowerAlt.exists_lift_blk y' bk bx hbk hy' w c hc hle'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have : CharP k₀ p := σ.charP σ.injective p
  have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap k₀ L₁).injective p
  let _ : Algebra (ZMod p) k₀ := ZMod.algebra k₀ p
  let _ : Algebra (ZMod p) L₁ := ZMod.algebra L₁ p
  have : IsScalarTower (ZMod p) k₀ L₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hL₁ : Algebra.trdeg (ZMod p) L₁ ≤ 1 := by
    rw [← trdeg_add_eq (ZMod p) k₀, trdeg_eq_zero (R := k₀), add_zero, ← hL]
    exact trdeg_le_of_injective ⟨σ, fun r => RingHom.congr_fun
      (Subsingleton.elim (σ.comp (algebraMap (ZMod p) k₀)) (algebraMap (ZMod p) L)) r⟩ σ.injective
  obtain ⟨hpW', m, hm, hmd⟩ := LevelTowerAlt.dim_le p hL₁ w'
  choose c' hc' using h3
  have hW' : IsMultiProjPrime (mCoordIdeal w') := ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal w',
    CoordinateConeArithVar.relevant w' c' hc'⟩
  have himg : AI.I4.imageZ v (mCoordIdeal w') = W := by
    rw [← Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv, ← hw, ← funext h1,
      CoordinateConeArithVar.mCoordIdeal_comp σ w₀, ← CoordinateConeArithVar.mCoordIdeal_comp (algebraMap k₀ L₁) w₀]
    exact congrArg _ (funext h2)
  have hQ' := LevelTowerAlt.map_red_prime p hW' hpW'
  have hcm' := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW')
  have hcm := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW)
  set Q' := (mCoordIdeal w').map (Bridge.GeoNum.red p) with hQ'_def
  set Q := W.map (Bridge.GeoNum.red p) with hQ_def
  have hiv : imageVar (ZMod p) v Q' = Q := by
    ext f
    obtain ⟨g, rfl⟩ := Bridge.GeoNum.red_surjective p f
    change rename v (Bridge.GeoNum.red p g) ∈ Q' ↔ g ∈ Q.comap (Bridge.GeoNum.red p)
    rw [hcm, ← himg, Bridge.GeoNum.red, ← map_rename]
    change rename v g ∈ Q'.comap (Bridge.GeoNum.red p) ↔ _
    rw [hcm']
    rfl
  have hQd : ringKrullDim (MRingOver (ZMod p) J ⧸ Q) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q), hcm]
    exact hdim
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') =
      ((1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← Targets.ProjContract.ringKrullDim_imageVar hv, hiv]
    exact hQd
  have hge := FieldNumbers.ContractRelDimLe.proof (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ'
  have hrel : FieldNumbers.relDim Q' = ((((m : ℤ) - Fintype.card K' : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    unfold FieldNumbers.relDim
    rw [hmd]
    rfl
  have hm' : m = 1 + Fintype.card K' := by
    rw [hcd, hrel] at hge
    have h5 : ((1 : ℕ) : ℤ) ≤ (m : ℤ) - Fintype.card K' :=
      WithTop.coe_le_coe.1 (WithBot.coe_le_coe.1 hge)
    omega
  subst hm'
  have hQ'd := (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q' 1).2 hmd
  have hdim' : ringKrullDim (MRing J' ⧸ mCoordIdeal w') = ((1 + Fintype.card K' : ℕ) : WithBot ℕ∞) := by
    rw [← hcm', ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q')]
    exact hmd
  have h6 := hnef _ hW' h4 (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero (by simpa using hpW')) hdim'
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW' hpW' hdim'] at h6
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW hpW hdim]
  have := hQ'.isPrime
  have h7 := (GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ' 1
    hQ'd hcd fun _ => a).2
  have h8 := FieldNumbers.FunctionFieldFinite.proof FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q'
    hQ' (hcd.trans hQ'd.symm)
  have h9 : FieldNumbers.pullDeg (Targets.ProjContract.emb hv) a = a' := by
    funext k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      rw [ha]
      exact hbk.extend_apply _ _ k
    · rw [ha' k' hk]
      exact Function.extend_apply' _ _ _ hk
  have h10 := FieldNumbers.RenameIntNum.full (ZMod p) K K J (fun k => J' (Targets.ProjContract.emb hv k))
    (Equiv.refl K) (Targets.ProjContract.blockEquiv hv)
    (fun x => hbk ((congrArg Sigma.fst (Targets.ProjContract.blockIncl_blockEquiv hv x))))
    (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') 1 fun _ => a
  have h11 : NumbersDVR.intNum (ZMod p) Q (fun _ : Fin 1 => a) =
      NumbersDVR.intNum (ZMod p) (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') (fun _ : Fin 1 => a) := by
    rw [← hiv, Targets.ProjContract.imageVar_eq hv]
    exact h10
  rw [h9, ← h11] at h7
  change 0 ≤ NumbersDVR.intNum (ZMod p) Q' (fun _ : Fin 1 => a') at h6
  rw [h7] at h6
  exact nonneg_of_mul_nonneg_right h6 (by exact_mod_cast Nat.pos_of_ne_zero h8)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @LevelTowerAlt.nef_fibres_block_embedding | exact LevelTowerAlt.nef_fibres_block_embedding
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.coords_reindex_degree : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | exact GlobalTheory.CompanionTheory.Relay.coords_reindex_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.coords_reindex_degree <;> assumption)
end
end
