module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardFormApproximationOfDecay
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecay
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSeventh

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnCusp
variable {D : D7}


open GlobalTheory.Size in
theorem isCuspFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hU' : ∀ w, IsAutFun N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨(hx.aut w).toIsAutFun, hx.cusp w⟩
    | zero => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1 (hy w).1 (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_smul (hx w).1 c, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  suffices H : IsAutFun N.V ((PiTensorProduct.lift U) v) ∧ IsCuspFun N.V ((PiTensorProduct.lift U) v) from H.2
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.RowLift.isAutFun_smul (hU' f).1 r, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

end GlobalTheory.DnCusp

namespace GlobalTheory.DnCusp

end GlobalTheory.DnCusp

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedFormDownwardGrowthBound

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownGrowth
open GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.DownApprox
open scoped ENNReal

theorem downward_growth_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi
  classical
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨Ae, fun K Fm v hF Φ hΦ ε hε => ?_⟩
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : ∀ k ∈ K, GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm k (v k)) := fun k hk => by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 (Fm k) (hF k hk) (v k)
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  have hB : ∀ k ∈ K, ∃ B : ℝ, ∀ g, ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ B :=
    fun k hk => (hFv k hk).decay Ae
  choose! B hB using hB
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)
  have hker : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ g h,
        ‖thetaKO (G.dn i).ω g h f‖ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
          GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨C, hC0, hC⟩ := (H (neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU'
    refine ⟨C * 2 ^ Ae, by positivity, fun f hf g h => ?_⟩
    have hb := (hC _ _ ((G.dn i).ω.toSgn true) hω μ 𝓓 hμ f hf).2
    have hinv : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, thetaKO (G.dn i).ω (γ * g) h f = thetaKO (G.dn i).ω g h f := fun γ hγ g => by
      have e1 : (((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) : GA D (neg (G.P (i + 1)).V) × GA D (G.P i).V) =
          ((ofSgn true (G.P (i + 1)).V).symm γ, 1) * ((ofSgn true (G.P (i + 1)).V).symm g, h) := by simp
      show ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) f 0 =
        ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm g, h) f 0
      rw [e1, map_mul, Module.End.mul_apply]
      exact hω.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω.om_pres _ _ hf.1)
    have hgr : ∀ g, ‖thetaKO (G.dn i).ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        GlobalTheory.Grow.height (G.P i).V h ^ Ae) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ Ae := fun g => by
      have := hb ((ofSgn true (G.P (i + 1)).V).symm g) h
      refine this.trans_eq ?_
      show C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        (GlobalTheory.Grow.height (G.P (i + 1)).V g * GlobalTheory.Grow.height (G.P i).V h) ^ Ae = _
      ring
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO (G.dn i).ω g h f) hinv hgr g).trans_eq ?_
    ring
  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ k ∈ K, ∀ h,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm k (v k) g ∂(G.mP (i + 1)).ν‖ ≤
          Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal *
            GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨Kc, hK0, hK⟩ := hker U' hU'
    refine ⟨Kc, hK0, fun f hf k hk h => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul (hFv k hk).continuous
    have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm k (v k) g‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h3 : ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max (B k) 0 :=
        (hB k hk g).trans (le_max_left _ _)
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm k (v k) g‖
          ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm k (v k) g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae * max (B k) 0 := by
          gcongr
        _ = _ := by ring
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  obtain ⟨Kc, hK0, hMb⟩ := hbound U hU
  have hvol : 0 ≤ ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal := ENNReal.toReal_nonneg
  have hBs : 0 ≤ ∑ k ∈ K, max (B k) 0 := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hM0 : 0 ≤ Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 := by positivity
  obtain ⟨r, -, hr0', hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr0'
  set M := Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 with hMdef
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (r / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g₀, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  let f' : ℕ → (WO (G.P (i + 1)).V (G.P i).V → ℂ) := fun j => if hj : j < n then f ⟨j, hj⟩ else 0
  let p' : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) := fun j => if hj : j < n then p ⟨j, hj⟩ else 0
  refine ⟨Finset.range n, f', p', fun j hj => ?_, ?_⟩
  · have hj' := Finset.mem_range.1 hj
    simp only [f', dif_pos hj']
    exact (isVacF_negFr _ _ _).1 (hf _)
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h
      (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l k hk h
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' k hk h).1
  have hΨU := sub_mem hΦU hgU
  have e : ∀ k ∈ K, ∀ h, (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm k (v k) g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm k (v k) g
          ∂(G.mP (i + 1)).ν := by
    intro k hk h
    rw [← integral_finsetSum _ fun l _ => hint l k hk h,
      ← integral_sub (hMb Φ hΦU k hk h).1 (integrable_finsetSum _ fun l _ => hint l k hk h)]
    refine integral_congr_ae (.of_forall fun g => ?_)

    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  have hsw : ∀ h, ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∑ k ∈ K, ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g ∂(G.mP (i + 1)).ν := by
    intro h
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [f', p', dif_pos l.isLt, Fin.eta]
  set s := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d
    (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hle : GlobalTheory.Size.growthSize (G.P i).V Ae (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ *
      (Fm k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * (Fm k (v k)) g ∂(G.mP (i + 1)).ν) ≤
      ENNReal.ofReal (M * s) := by
    refine (GlobalTheory.Size.growthSize_le_iff (mul_nonneg hM0 hs0)).2 fun h => ?_
    rw [hsw h, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k hk => e k hk h]
    refine (norm_sum_le _ _).trans ?_
    rw [hMdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ((hMb _ hΨU k hk h).2).trans_eq ?_
    ring
  refine hle.trans_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrε)
  have hM1 : 0 < M + 1 := by linarith
  have h1 : (M + 1) * s < r := by
    have := mul_lt_mul_of_pos_left hs hM1
    rwa [mul_div_cancel₀ _ hM1.ne'] at this
  nlinarith
end GlobalTheory.DownGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_form_downward_growth_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DownGrowth.downward_growth_approximation | exact _root_.GlobalTheory.DownGrowth.downward_growth_approximation | (intros; apply _root_.GlobalTheory.DownGrowth.downward_growth_approximation <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardThetaLiftIsCuspidalOfIntegrable

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnCusp
variable {D : D7}
end GlobalTheory.DnCusp
namespace GlobalTheory.DnCusp
theorem downward_theta_lift_isCuspidal_of_integrable (s1 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint
  obtain ⟨N₁, h1⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  obtain ⟨N₂, h2⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ
  have hdn := (hL D hS G₀ Pl0 T A Ks R G hB hG).dn i hi
  have haut := _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hB hG i hi Φ hΦ φ hφ hint
  set L : GA D (G.P i).V → ℂ := fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν with hLdef
  set N := max N₁ N₂
  have key : ∀ n : ℕ, ∃ ψ : GA D (G.P i).V → ℂ, (IsAutFun (G.P i).V ψ ∧ IsCuspFun (G.P i).V ψ) ∧
      GlobalTheory.Size.growthSize (G.P i).V N (ψ - L) ≤ ((n : ENNReal) + 1)⁻¹ := by
    intro n
    set ε : ENNReal := ((n : ENNReal) + 1)⁻¹ / 2 with hε
    have hε0 : 0 < ε := ENNReal.div_pos (ENNReal.inv_ne_zero.2 (by simp)) (by simp)
    obtain ⟨K, F, v, hF, hK⟩ := h2 Φ hΦ ε hε0
    obtain ⟨J, f, p, hf, hJ⟩ := h1 K F v hF Φ hΦ ε hε0
    have hF' : ∀ j ∈ J, ∀ k ∈ K, ∃ F' ∈ (G.P i).Cusp R.θ, ∀ h,
        (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) h := by
      intro j hj k hk
      obtain ⟨F', hF'm, hF'e⟩ := hdn (f j) (hf j hj) (F k) (hF k hk)
      exact ⟨F', hF'm, fun h => (hF'e (p j) (v k) h).2⟩
    refine ⟨fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν, ?_, ?_⟩
    · have hterm : ∀ j ∈ J, ∀ k ∈ K, IsAutFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) ∧
          IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) := by
        intro j hj k hk
        obtain ⟨F', hF'm, hF'e⟩ := hF' j hj k hk
        have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) = F' ((G.dn i).It (p j) (v k)) := funext hF'e
        rw [e]
        exact ⟨GlobalTheory.RowLift.isAutFun_of_mem_cusp _ _ hF'm _, isCuspFun_of_mem_cusp _ _ hF'm _⟩
      have h0 : IsCuspFun (G.P i).V (0 : GA D (G.P i).V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
      have hsum : ∀ (s : Finset ℕ) (u : ℕ → GA D (G.P i).V → ℂ), (∀ a ∈ s, IsAutFun (G.P i).V (u a) ∧ IsCuspFun (G.P i).V (u a)) →
          IsAutFun (G.P i).V (fun h => ∑ a ∈ s, u a h) ∧ IsCuspFun (G.P i).V (fun h => ∑ a ∈ s, u a h) := by
        intro s u hu
        have e : (fun h => ∑ a ∈ s, u a h) = ∑ a ∈ s, u a := by funext h; simp [Finset.sum_apply]
        rw [e]
        clear e
        induction s using Finset.induction_on with
        | empty => simpa using ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          have hA := hu a (Finset.mem_insert_self a s)
          have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
          exact ⟨GlobalTheory.RowLift.isAutFun_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1 hB.1 hA.2 hB.2⟩
      exact hsum J _ fun j hj => hsum K _ fun k hk => hterm j hj k hk
    · set M : GA D (G.P i).V → ℂ := fun h => ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      set Ψ : GA D (G.P i).V → ℂ := fun h => ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν
      have e : Ψ - L = -((L - M) + (M - Ψ)) := by abel
      have e2 : GlobalTheory.Size.growthSize (G.P i).V N (Ψ - L) = GlobalTheory.Size.growthSize (G.P i).V N ((L - M) + (M - Ψ)) := by
        rw [e]; unfold GlobalTheory.Size.growthSize; congr 1; funext g; rw [Pi.neg_apply, norm_neg]
      rw [e2]
      refine (GlobalTheory.Size.growthSize_add_le).trans ?_
      have a1 : GlobalTheory.Size.growthSize (G.P i).V N (L - M) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_right N₁ N₂)).trans hK.le)
      have a2 : GlobalTheory.Size.growthSize (G.P i).V N (M - Ψ) ≤ ε :=
        ((GlobalTheory.Size.growthSize_anti (le_max_left N₁ N₂)).trans hJ.le)
      refine (add_le_add a1 a2).trans (le_of_eq ?_)
      rw [hε, ENNReal.add_halves]
  choose ψ hψ hψb using key
  have ht : Filter.Tendsto (fun n => GlobalTheory.Size.growthSize (G.P i).V N (ψ n - L)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) Filter.atTop (nhds 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => bot_le) hψb
  exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto D (G.P i).V N ψ L
    (fun n => ⟨(hψ n).1.cont, (hψ n).1.left, (hψ n).2⟩) haut.cont haut.left ht
theorem downward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) :=
  _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal_of_integrable _root_.GlobalTheory.T.twisted_form_downward_growth_bound _root_.GlobalTheory.T.twisted_form_downward_approximation
end GlobalTheory.DnCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsCuspFun (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal | exact _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal | (intros; apply _root_.GlobalTheory.DnCusp.downward_theta_lift_isCuspidal <;> assumption)
end
end
end
