module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxThetaLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftApproxFockSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApprox

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThLiftCusp

theorem isCuspFun_of_approx {D : D7} (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (N : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ ψ : GA D V → ℂ, Continuous ψ ∧ (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧
      ∀ g, ‖ψ g - f g‖ ≤ ε * GlobalTheory.Grow.height V g ^ N) : IsCuspFun V f := by
  choose ψ hψ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine GlobalTheory.CuspLimit.isCuspFun_of_tendsto D V N ψ f (fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩) hf hl ?_
  have hb : ∀ n : ℕ, GlobalTheory.Size.growthSize V N (ψ n - f) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (GlobalTheory.Size.growthSize_le_iff Nat.one_div_pos_of_nat.le).2 fun g => by simpa using (hψ n).2.2.2 g
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  simpa using (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)

end GlobalTheory.ThLiftCusp

namespace GlobalTheory.ThLiftCusp

theorem norm_lift_sub_le {X H : Type} [MeasurableSpace X] (μ : Measure X) (K K' : H → X → ℂ) (φ φ' : X → ℂ)
    (u : H → ℝ) (w : X → ℝ) (C e δ : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e) (hu : ∀ h, 0 ≤ u h)
    (hK : ∀ h x, ‖K h x‖ ≤ C * u h * w x) (hKK : ∀ h x, ‖K' h x - K h x‖ ≤ e * u h * w x)
    (h1 : Integrable (fun x => w x * ‖φ x‖) μ) (h2 : Integrable (fun x => w x * ‖φ' x - φ x‖) μ)
    (hδ : ∫ x, w x * ‖φ' x - φ x‖ ∂μ ≤ δ)
    (hA : ∀ h, Integrable (fun x => K' h x * φ' x) μ) (hB : ∀ h, Integrable (fun x => K h x * φ x) μ) (h : H) :
    ‖∫ x, K' h x * φ' x ∂μ - ∫ x, K h x * φ x ∂μ‖ ≤ u h * (e * ∫ x, w x * ‖φ x‖ ∂μ + (e + C) * δ) := by
  rw [← integral_sub (hA h) (hB h)]
  have hpt : ∀ x, ‖K' h x * φ' x - K h x * φ x‖ ≤
      u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖)) := fun x => by
    have e1 : K' h x * φ' x - K h x * φ x =
        (K' h x - K h x) * φ x + (K' h x - K h x) * (φ' x - φ x) + K h x * (φ' x - φ x) := by ring
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ x))
    have a2 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ' x - φ x))
    have a3 := mul_le_mul_of_nonneg_right (hK h x) (norm_nonneg (φ' x - φ x))
    nlinarith
  have hint : Integrable (fun x => u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖))) μ :=
    ((h1.const_mul e).add (h2.const_mul (e + C))).const_mul (u h)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (h1.const_mul e) (h2.const_mul (e + C)), integral_const_mul,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hu h)

end GlobalTheory.ThLiftCusp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.IndefR.Mult GlobalTheory.Grid

namespace GlobalTheory.FinLift

variable {D : D7}

theorem autCusp_of_mem_cusp (N : Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hΦ
  replace hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨(GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f)).toIsAutFun, GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

theorem autCusp_sum (V : HSp D) {ι : Type} (s : Finset ι) (φ : ι → GA D V → ℂ) (h : ∀ i ∈ s, IsAutFun V (φ i) ∧ IsCuspFun V (φ i)) :
    IsAutFun V (∑ i ∈ s, φ i) ∧ IsCuspFun V (∑ i ∈ s, φ i) :=
  Finset.sum_induction φ (fun ψ => IsAutFun V ψ ∧ IsCuspFun V ψ)
    (fun a b ha hb => ⟨GlobalTheory.RowLift.isAutFun_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1 hb.1 ha.2 hb.2⟩)
    ⟨GlobalTheory.RowLift.isAutFun_zero V, fun r C hC μ 𝓕 hμ h𝓕 g => by simp⟩ h

end GlobalTheory.FinLift

namespace GlobalTheory.FinLift

variable {D : D7}

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    {ι : Type} (s : Finset ι) (x : ι → WO S T → ℂ) : thetaKO om g h (∑ i ∈ s, x i) = ∑ i ∈ s, thetaKO om g h (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, Finset.sum_apply]

theorem lift_finSum {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {n : ℕ}
    (K : Fin n → P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M)
    (hK : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsMult θ m (K l) It) (ps : Fin n → P) {n' : ℕ} (Fs : Fin n' → A.Maps)
    (vs : Fin n' → SmT A.M) (hF : ∀ k, Fs k ∈ A.Cusp θ) :
    (∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν) ∧
    IsAutFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) ∧
    IsCuspFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) := by
  choose F' h using fun l k => hK l (Fs k) (hF k)
  have hF' := fun l k => (h l k).1
  have hI := fun l k => (h l k).2
  have hsplit : ∀ h g, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g = ∑ l, ∑ k, K l (ps l) h g * Fs k (vs k) g :=
    fun h g => by rw [Finset.sum_mul_sum]
  have hint : ∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν := fun h => by
    simp_rw [hsplit]
    exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1
  have heq : (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) =
      ∑ l, ∑ k, F' l k (It (ps l) (vs k)) := by
    funext h
    simp_rw [hsplit]
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    exact Finset.sum_congr rfl fun k _ => (hI l k (ps l) (vs k) h).2
  rw [heq]
  exact ⟨hint, autCusp_sum B.V _ _ fun l _ => by
    simpa only [Finset.sum_apply] using autCusp_sum B.V _ _ fun k _ => autCusp_of_mem_cusp B θ (hF' l k) _⟩

end GlobalTheory.FinLift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFiniteLevelLiftOfTwist

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FinLift
theorem exists_finite_level_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  intro LC _ D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj n fs ps hfs n' Fs vs hFs
  have hC := LC D hS G₀ Pl0 T A Ks R G hRB hG
  simp only [thetaKO_sum]
  exact lift_finSum (fun l p h g => thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) p))
    (fun p v => (G.th t i j).It p v) (fun l => hC.th t i j hi hj (fs l) (hfs l)) ps Fs vs hFs
end GlobalTheory.FinLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_finite_level_lift_of_twist : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.FinLift.exists_finite_level_lift | exact _root_.GlobalTheory.FinLift.exists_finite_level_lift | (intros; apply _root_.GlobalTheory.FinLift.exists_finite_level_lift <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftLeQuotientHeight

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaArrowGrowth
theorem thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨K, n, hK, hb⟩ := GlobalTheory.ChainOnto.ThetaSwap.thetaKO_le_quotHeight hRB.inf hω hΦ
  refine ⟨n, n, K, hK, fun h g => ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact hb h g
end GlobalTheory.ThetaArrowGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @_root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | exact _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | (intros; apply _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
theorem GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint
  have haut := _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint
  obtain ⟨a1, b1, C, hC0, hK1⟩ := _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  obtain ⟨a2, b2, happ2⟩ := _root_.GlobalTheory.T.twist_thetaLift_approx_fockSpace hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  set a := max a1 a2
  set b := max b1 b2
  have hqB : ∀ h, ∀ c, c ≤ a → GlobalTheory.Grow.quotHeight (G.V i j).V h ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a :=
    fun h c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ h) hc
  have hqA : ∀ g, ∀ c, c ≤ b → GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b :=
    fun g c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ g) hc
  have hK : ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤
      C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := fun h g =>
    (hK1 h g).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hqB h a1 (le_max_left _ _)) hC0)
      (hqA g b1 (le_max_left _ _)) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hC0 (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))
  have happ : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ))
      (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g,
        ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤
          ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
    intro ε hε
    obtain ⟨n, fs, ps, hfs, hb⟩ := happ2 ε hε
    exact ⟨n, fs, ps, hfs, fun h g => (hb h g).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hqB h a2 (le_max_right _ _)) hε.le) (hqA g b2 (le_max_right _ _))
      (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hε.le (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))⟩
  obtain ⟨hI1, hform⟩ := _root_.GlobalTheory.T.twist_cuspForm_approx_thetaLift hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj φ hφ b
  refine GlobalTheory.ThLiftCusp.isCuspFun_of_approx _ _ haut.cont haut.left a fun η hη => ?_
  set I1 := ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖ ∂(G.meas t i (j + 1)).ν
    with hI1def
  have hI1nn : 0 ≤ I1 := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun g =>
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _) (norm_nonneg _))
  have hden : 0 < I1 + 1 + C := by linarith
  set e := min 1 (η / (I1 + 1 + C)) with hedef
  have he : 0 < e := lt_min one_pos (div_pos hη hden)
  obtain ⟨n, fs, ps, hfs, hKK⟩ := happ e he
  obtain ⟨n', Fs, vs, hFs, hI2, hδ⟩ := hform e he
  obtain ⟨hint', haut', hcusp'⟩ := _root_.GlobalTheory.T.exists_finite_level_lift_of_twist hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj n fs ps hfs n' Fs vs hFs
  refine ⟨_, haut'.cont, haut'.left, hcusp', fun h => ?_⟩
  have key := GlobalTheory.ThLiftCusp.norm_lift_sub_le ((G.meas t i (j + 1)).ν.restrict (G.meas t i (j + 1)).fd)
    (fun h g => thetaKO (G.th t i j).ω h g Φ)
    (fun h g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)))
    φ (fun g => ∑ k, Fs k (vs k) g) (fun h => GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a)
    (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b) C e e hC0 he.le
    (fun h => pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _) hK hKK hI1 hI2 hδ hint' hint h
  refine key.trans ?_
  have hq : GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a :=
    pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos _ h).le (GlobalTheory.Grow.quotHeight_le_height _ h) a
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e ≤ η / (I1 + 1 + C) := min_le_right _ _
  have hb : e * I1 + (e + C) * e ≤ η := by
    have : e * (I1 + 1 + C) ≤ η := (le_div_iff₀ hden).1 he2
    nlinarith
  have h0 : 0 ≤ e * I1 + (e + C) * e := by positivity
  calc GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * (e * I1 + (e + C) * e)
      ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a * η :=
        mul_le_mul hq hb h0 (pow_nonneg ((GlobalTheory.Grow.quotHeight_pos _ h).le.trans (GlobalTheory.Grow.quotHeight_le_height _ h)) _)
    _ = η * GlobalTheory.Grow.height (G.V i j).V h ^ a := mul_comm _ _
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | exact _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | (intros; apply _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal <;> assumption)
end
end
end
