module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApproxStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspAverageKFiniteDecomposition
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspLiftFiniteSumApproximation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnFormApprox

variable {D : D7}

theorem autSm_cusp_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFunSm θ N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hz : IsAutFunSm θ N.V (0 : GA D N.V → ℂ) := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ N.V
  have hU' : ∀ w, IsAutFunSm θ N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨hx.aut w, hx.cusp w⟩
    | zero => exact fun w => ⟨hz, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1.toIsAutFun (hy w).1.toIsAutFun (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hx w).1, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hU' f).1, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem autSm_cusp_sum {V : HSp D} {θ : InfFam D} (K : Finset ℕ) (u : ℕ → GA D V → ℂ)
    (hu : ∀ k ∈ K, IsAutFunSm θ V (u k) ∧ IsCuspFun V (u k)) :
    IsAutFunSm θ V (∑ k ∈ K, u k) ∧ IsCuspFun V (∑ k ∈ K, u k) := by
  induction K using Finset.induction_on with
  | empty =>
    have h0 : IsCuspFun V (0 : GA D V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
    rw [Finset.sum_empty]
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, h0⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hA := hu a (Finset.mem_insert_self a s)
    have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1.toIsAutFun hB.1.toIsAutFun hA.2 hB.2⟩

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DecayIntegralBoundedBySobolevGrowth

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownConv
theorem decayIntegral_le_sobolevGrowth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi U hU M
  obtain ⟨hν, h𝓕⟩ := MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  obtain ⟨d, C₀, hC⟩ := hP.cuspDecaySobolev D R.θ hB.inf (G.P (i + 1)).V U hU 0 M
  have hfin : (G.mP (i + 1)).ν (G.mP (i + 1)).fd < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν h𝓕
  refine ⟨d, C₀ * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toNNReal, fun ψ ha hk hs hg hc => ?_⟩
  refine (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt_le _ _ M ψ).trans ?_
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin.ne, mul_right_comm]
  exact mul_le_mul' (hC ψ ha hk hs hg hc) le_rfl
end GlobalTheory.DownConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.decay_integral_bounded_by_sobolev_growth : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ := by
  first | exact @_root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth | exact _root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth | (intros; apply _root_.GlobalTheory.DownConv.decayIntegral_le_sobolevGrowth <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LiftedGrowthBoundedByDecayIntegral

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownLiftGrowth
theorem growthSize_lift_le_decayIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  intro _ D _ G₀ _ _ Pl0 T Af Ks _ _ _ R G hB hG i hi
  obtain ⟨N, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.sgn true (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨N, fun Φ hΦ => ?_⟩
  have hω := (hG.arrows.dn i hi).weil
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real R.ψ hB.inf hU
  have hb := (hC _ _ _ hω μ 𝓕 hμ Φ hl).2
  set K := C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 ENNReal.toReal_nonneg
  have e : ∀ g h, thetaKO (G.dn i).ω g h Φ =
      thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm g) h Φ := fun g h => by
    show (G.dn i).ω (g, h) Φ 0 = (G.dn i).ω (GlobalTheory.Grid.ofSgn true _ ((GlobalTheory.Grid.ofSgn true _).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g,
      thetaKO (G.dn i).ω (γ * g) h Φ = thetaKO (G.dn i).ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hk : ∀ g h, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
      K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N := by
    intro g h
    have h1 : ∀ g, ‖thetaKO (G.dn i).ω g h Φ‖ ≤
        (K * GlobalTheory.Grow.height (G.P i).V h ^ N) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ N := fun g => by
      rw [e]
      have h2 := hb ((GlobalTheory.Grid.ofSgn true _).symm g) h
      have hh : GlobalTheory.Grow.height (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true _).symm g) =
          GlobalTheory.Grow.height (G.P (i + 1)).V g := rfl
      rw [hh] at h2
      exact h2.trans_eq (by rw [hK, mul_pow]; ring)
    exact (GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) h1 g).trans_eq (by ring)
  refine ⟨(K * 2 ^ N).toNNReal, fun f => iSup_le fun h => ?_⟩
  have hg := pow_pos (GlobalTheory.Grow.height_pos (G.P i).V h) N
  rw [ENNReal.ofReal_div_of_pos hg, ofReal_norm_eq_enorm]
  refine ENNReal.div_le_of_le_mul ((enorm_integral_le_lintegral_enorm _).trans ?_)
  rw [mul_right_comm, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt]
  refine (lintegral_mono fun g => ?_).trans_eq
    (lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))
  have hq := (pow_pos (GlobalTheory.Grow.quotHeight_pos (G.P (i + 1)).V g) N).le
  rw [← ofReal_norm_eq_enorm]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (K * 2 ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]
  calc ‖thetaKO (G.dn i).ω g h Φ‖ * ‖f g‖
      ≤ (K * 2 ^ N * GlobalTheory.Grow.height (G.P i).V h ^ N * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ N) * ‖f g‖ :=
        mul_le_mul_of_nonneg_right (hk g h) (norm_nonneg _)
    _ = _ := by ring
end GlobalTheory.DownLiftGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  first | exact @_root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | exact _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral | (intros; apply _root_.GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayIntegral <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SobolevApproximationByCuspForms

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ENNReal
namespace GlobalTheory.SobolevCuspApprox
theorem sobolev_approximation_by_cuspForms : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB _ i _ φ hφ U hU hlev d δ hδ
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨hAut, hc, -⟩ := id hφ
  have hφg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V φ :=
    ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hAut hc, hc⟩
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h)] at hr1
    exact lt_irrefl _ hr1
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D R.θ hθ (G.P (i + 1)) φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList
    (Finset.nodup_toList _) d r hr
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D R.θ hθ hP (G.P (i + 1)) φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  let F' : ℕ → (G.P (i + 1)).Maps := fun k => if h : k < n then F ⟨k, h⟩ else 0
  let v' : ℕ → Formalism.IndefR.Links.SmT (G.P (i + 1)).M := fun k => if h : k < n then v ⟨k, h⟩ else 0
  have hval : ∀ j : Fin n, F' j (v' j) = F j (v j) := fun j => by simp [F', v', j.2]
  have hsumeq : ∑ k ∈ Finset.range n, F' k (v' k) = ∑ j, F j (v j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => F' k (v' k))]
    exact Finset.sum_congr rfl fun j _ => hval j
  refine ⟨Finset.range n, F', v', fun k hk => ?_, fun k hk u hu hu' g => ?_, ?_⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', hk'] using hF ⟨k, hk'⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', v', hk'] using hFlev ⟨k, hk'⟩ u hu hu' g
  · rw [hsumeq]
    have hsg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (∑ j, F j (v j)) :=
      Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
        (GlobalTheory.CuspApproxAll.good_zero R.θ (G.P (i + 1)).V) fun j _ =>
          GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ (G.P (i + 1)) (hF j) (v j)
    have hg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (φ - ∑ j, F j (v j)) := by
      have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
      rwa [neg_one_smul, ← sub_eq_add_neg] at this
    exact ⟨fun e' => GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1 e', lt_of_le_of_lt hgrow hr2⟩
end GlobalTheory.SobolevCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.cuspForm_sobolev_density : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  first | exact @_root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | exact _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | (intros; apply _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardFormApproximationOfDecay

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnFormApprox
variable {D : D7}
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem decay_integral_approximation (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ (M : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ M δ hδ
  obtain ⟨U, hU, hk⟩ := hφ.1.level
  obtain ⟨d, C, hC⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi U hU M
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hlev, hfin, hd⟩ := s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ U hU hk d (δ / C')
    (ENNReal.div_pos hδ.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  have hs := autSm_cusp_sum K (fun k => F k (v k)) fun k hk => autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)
  have hψ : IsAutFunSm R.θ (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) ∧ IsCuspFun (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (∑ k ∈ K, F k (v k))]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hφ.1 (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1),
      GlobalTheory.MultMem.isCuspFun_add hφ.1.toIsAutFun (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1).toIsAutFun hφ.2.1
        (GlobalTheory.MultMem.isCuspFun_smul _ hs.2)⟩
  have hlevψ : ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, (φ - ∑ k ∈ K, F k (v k)) (g * u) = (φ - ∑ k ∈ K, F k (v k)) g := by
    intro u hu hu' g
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [hk u hu hu' g]
    congr 1
    exact Finset.sum_congr rfl fun k hkK => hlev k hkK u hu hu' g
  calc GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k))
      ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        hC _ hψ.1.toIsAutFun hlevψ hψ.1.smooth hfin hψ.2
    _ ≤ C' * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (δ / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = δ := ENNReal.mul_div_cancel hC0 hCt
theorem downward_form_approximation_of_decay (s1 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f) (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ
  obtain ⟨N, hN⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  refine ⟨N, fun Φ hΦ ε hε => ?_⟩
  obtain ⟨C, hC⟩ := hN Φ hΦ
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hd⟩ := _root_.GlobalTheory.DnFormApprox.decay_integral_approximation s2 s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ N (ε / C')
    (ENNReal.div_pos hε.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  have hint : ∀ u : GA D (G.P (i + 1)).V → ℂ, IsAutFunSm R.θ (G.P (i + 1)).V u → IsCuspFun (G.P (i + 1)).V u → ∀ h,
      IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * u g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := fun u hu hc h =>
    GlobalTheory.DownConv.integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hu hc h
  have e : (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) -
      ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (F k (v k)) g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν := by
    funext h
    have hk : ∀ k ∈ K, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * (F k (v k)) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν :=
      fun k hk => hint _ (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).1 (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).2 h
    rw [← integral_finsetSum _ hk, ← integral_sub (hint φ hφ.1 hφ.2.1 h) (integrable_finsetSum _ hk)]
    congr 1
    funext g
    simp [Pi.sub_apply, Finset.sum_apply, mul_sub, Finset.mul_sum]
  rw [e]
  calc GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν)
      ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) := hC _
    _ ≤ C' * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (ε / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = ε := ENNReal.mul_div_cancel hC0 hCt
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem downward_form_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε :=
  _root_.GlobalTheory.DnFormApprox.downward_form_approximation_of_decay _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral _root_.GlobalTheory.T.decay_integral_bounded_by_sobolev_growth _root_.GlobalTheory.T.cuspForm_sobolev_density
end GlobalTheory.DnFormApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_form_downward_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DnFormApprox.downward_form_approximation | exact _root_.GlobalTheory.DnFormApprox.downward_form_approximation | (intros; apply _root_.GlobalTheory.DnFormApprox.downward_form_approximation <;> assumption)
end
end
end
