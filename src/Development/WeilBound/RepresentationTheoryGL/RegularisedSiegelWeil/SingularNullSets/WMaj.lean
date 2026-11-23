module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuityStatement
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajB
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajC

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LWMaj

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.ThetaDens.WeilCompact

variable {D : D7}

def supK {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Set (GA D S × GA D T))
    (f : WO S T → ℂ) : ℝ≥0∞ :=
  ⨆ x ∈ K, ⨆ w, ‖om x f w‖ₑ

section Sup

variable {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Set (GA D S × GA D T))

theorem supK_add (f f' : WO S T → ℂ) : supK om K (f + f') ≤ supK om K f + supK om K f' := by
  unfold supK
  refine iSup₂_le fun x hx => iSup_le fun w => ?_
  rw [map_add (f := _), Pi.add_apply]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup₂_of_le (f := fun x _ => ⨆ w, ‖om x f w‖ₑ) x hx (le_iSup (fun w => ‖om x f w‖ₑ) w)
  · exact le_iSup₂_of_le (f := fun x _ => ⨆ w, ‖om x f' w‖ₑ) x hx (le_iSup (fun w => ‖om x f' w‖ₑ) w)

theorem supK_smul (c : ℂ) (f : WO S T → ℂ) : supK om K (c • f) = ‖c‖ₑ * supK om K f := by
  simp only [supK, map_smul, Pi.smul_apply, smul_eq_mul, enorm_mul, ENNReal.mul_iSup]

end Sup

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem supK_ne_top (hψ : IsStdChar D ψ (-1)) (hom : IsWeilDatumO ψ S T χS χT om) {K : Set (GA D S × GA D T)}
    (hK : IsCompact K) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) : supK om K F ≠ ⊤ := by
  obtain ⟨-, -, -, -, -, K₀, hK₀, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 F p.2 :=
    GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hom F hF
  obtain ⟨M, hM⟩ := (hK.prod hK₀).exists_bound_of_continuousOn hcont.continuousOn
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M)) ?_
  refine iSup₂_le fun x hx => iSup_le fun w => ?_
  obtain ⟨γ, hγ, h⟩ := hc w
  rw [← ofReal_norm, ← theta_norm_periodic hψ (hom.om_pres x F hF) γ hγ w]
  exact ENNReal.ofReal_le_ofReal (hM (x, γ + w) (Set.mk_mem_prod hx h))

section Sob

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (K : Set (GA D S × GA D T))
include hψ hθ

theorem sobK_add_le {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') (d : ℕ) :
    wordSum (heisDer ψ θ) (supK om K) d (f + f') ≤
      wordSum (heisDer ψ θ) (supK om K) d f + wordSum (heisDer ψ θ) (supK om K) d f' := by
  refine wordSum_le_add fun l => le_of_eq_of_le (congrArg _ ?_) (supK_add om K _ _)
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

omit hψ hθ in
theorem sobK_smul (d : ℕ) (c : ℂ) (f : WO S T → ℂ) :
    wordSum (heisDer ψ θ) (supK om K) d (c • f) = ‖c‖ₑ * wordSum (heisDer ψ θ) (supK om K) d f :=
  wordSum_eq_mul fun l => by
    rw [← supK_smul]
    exact congrArg _ (wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl)

theorem sobK_sum_le {ι : Type} (s : Finset ι) {g : ι → WO S T → ℂ} (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) (d : ℕ) :
    wordSum (heisDer ψ θ) (supK om K) d (∑ i ∈ s, g i) ≤ ∑ i ∈ s, wordSum (heisDer ψ θ) (supK om K) d (g i) := by
  refine Finset.le_sum_of_subadditive_on_pred (wordSum (heisDer ψ θ) (supK om K) d) (IsThetaFunO ψ S T) ?_
    (fun _ _ a b => sobK_add_le hψ hθ K a b d) (fun _ _ => theta_add) g hg
  have := sobK_smul (ψ := ψ) (θ := θ) (om := om) K d 0 (0 : WO S T → ℂ)
  rw [zero_smul, enorm_zero, zero_mul] at this
  exact this.le

theorem sobK_dRho_le {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (d : ℕ) :
    wordSum (heisDer ψ θ) (supK om K) d (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * wordSum (heisDer ψ θ) (supK om K) (d + 1) f := by
  have ht : ∀ (c : ℂ) a, IsThetaFunO ψ S T (c • heisDer ψ θ a f) := fun c a =>
    theta_smul c (theta_dRho hθ hψ a.1 _ hf)
  have hb : ∀ (c : ℝ) a, wordSum (heisDer ψ θ) (supK om K) d ((c : ℂ) • heisDer ψ θ a f) ≤
      ENNReal.ofReal |c| * wordSum (heisDer ψ θ) (supK om K) (d + 1) f := fun c a => by
    rw [sobK_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact wordSum_letter_le d a f
  rw [dRho_eq_sum_heisDer hψ hθ hf, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (sobK_sum_le hψ hθ K _ (fun i _ => theta_finsetSum _ fun j _ => theta_add (ht _ _) (ht _ _)) d).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (sobK_sum_le hψ hθ K _ (fun j _ => theta_add (ht _ _) (ht _ _)) d).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_mul]
  exact (sobK_add_le hψ hθ K (ht _ _) (ht _ _) d).trans (add_le_add (hb _ _) (hb _ _))

end Sob

theorem word_om_sup_le (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g →
        (⨆ w, ‖wordAct (heisDer ψ θ) l (om x g) w‖ₑ) ≤ C * wordSum (heisDer ψ θ) (supK om K) k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x hx g _ => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, wordSum_zero, ENNReal.coe_one, one_mul]
    exact le_iSup₂_of_le (f := fun x _ => ⨆ w, ‖om x g w‖ₑ) x hx le_rfl
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * wordSum (heisDer ψ θ) (supK om K) k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * wordSum (heisDer ψ θ) (supK om K) (k + 1) g) := by
          gcongr
          exact sobK_dRho_le hom.std hθ K hg a.1 _ k
      _ ≤ C * (B * wordSum (heisDer ψ θ) (supK om K) (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * wordSum (heisDer ψ θ) (supK om K) (k + 1) g := by push_cast; ring

theorem unifSob {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (C : Set (GA D S)) (hC : IsCompact C) (N : ℕ) :
    ∃ B : ℝ≥0, ∀ g ∈ C, GlobalTheory.Unf.supSob ψ θ N (om (g, 1) f) ≤ B := by
  set K : Set (GA D S × GA D T) := C ×ˢ {1} with hKdef
  have hK : IsCompact K := hC.prod isCompact_singleton
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  choose Cw hCw using word_om_sup_le hom hθ (K := K) _ hB
  have hfin : ∀ k, wordSum (heisDer ψ θ) (supK om K) k f ≠ ⊤ := fun k =>
    wordSum_ne_top_iff.2 fun l _ => supK_ne_top hψ hom hK (theta_word hψ hθ l hf)
  set B' : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool,
    (Cw k : ℝ≥0∞) * wordSum (heisDer ψ θ) (supK om K) k f with hB'
  have hB'fin : B' ≠ ⊤ := ENNReal.sum_ne_top.2 fun k _ => ENNReal.sum_ne_top.2 fun _ _ =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin k)
  refine ⟨B'.toNNReal, fun g hg => ?_⟩
  rw [ENNReal.coe_toNNReal hB'fin]
  show wordSum (heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) N (om (g, 1) f) ≤ B'
  unfold wordSum
  refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun a _ => ?_
  exact hCw k _ List.length_ofFn (g, 1) (Set.mk_mem_prod hg rfl) f hf

end PositivityTheory.Rg.Rsw.L.LWMaj

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajD

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LWMaj

variable {D : D7}

theorem unifLevel {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (C : Set (GA D S)) (hC : IsCompact C) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ g ∈ C, om (g, 1) f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  obtain ⟨U, hUo, hU⟩ := hf.level

  let a : GA D S → WO S T →+ WO S T := fun g =>
    { toFun := fun u => actO S T g⁻¹ 1 u
      map_zero' := by simp [actO]
      map_add' := fun u v => by simp [actO, Matrix.mul_add, Matrix.add_mul] }
  let U' : AddSubgroup (WO S T) := ⨅ g ∈ C, U.comap (a g)
  have hcont : Continuous fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2 := by
    simp only [actO, inv_inv]
    exact (continuous_const.matrix_mul continuous_snd).matrix_mul ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst)
  have hmem : ∀ u, u ∈ U' ↔ ∀ g ∈ C, actO S T g⁻¹ 1 u ∈ U := fun u => by
    rw [AddSubgroup.mem_iInf]
    exact forall_congr' fun g => by rw [AddSubgroup.mem_iInf]; rfl
  have hopen : IsOpen (U' : Set (WO S T)) := by
    have hn : C ×ˢ ({0} : Set (WO S T)) ⊆ (fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2) ⁻¹' U := by
      rintro ⟨g, u⟩ ⟨-, hu⟩
      simp only [Set.mem_singleton_iff] at hu
      subst hu
      simp [actO, U.zero_mem]
    obtain ⟨s, v, -, hv, hCs, h0v, hsv⟩ :=
      generalized_tube_lemma hC isCompact_singleton (hUo.preimage hcont) hn
    refine AddSubgroup.isOpen_of_mem_nhds U' (g := 0) ?_
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun u hu => ?_
    refine (hmem u).2 fun g hg => ?_
    have h := hsv (Set.mk_mem_prod (hCs hg) hu)
    rw [Set.mem_preimage] at h
    exact h
  refine ⟨U', hopen, fun g hg => ⟨hom.om_pres _ _ hf, fun u hu h0 => ?_⟩⟩
  have hu' : actO S T g⁻¹ 1 u ∈ U := by
    exact (hmem u).1 hu g hg
  have h0' : (actO S T g⁻¹ 1 u).map (infPart D) = 0 := by
    simp only [actO, Matrix.map_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  have h1 := hom.om_heis g 1 (actO S T g⁻¹ 1 u) f hf
  rw [hU _ hu' h0'] at h1
  have h2 : actO S T g 1 (actO S T g⁻¹ 1 u) = u := by
    simp only [actO, inv_inv, GlobalTheory.MixModel.mt_one, Matrix.one_mul, Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv,
      Matrix.mul_one]
  rw [h2] at h1
  exact h1.symm

end PositivityTheory.Rg.Rsw.L.LWMaj

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WMaj

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open GlobalTheory.Core.Rk.SW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L

theorem wMaj : WMaj := by
  intro D n V ψ hψ χ hχ hr θ hθ μ hμ' ω hω Φ
  obtain ⟨𝓕, hμ⟩ := hμ'
  refine ⟨GlobalTheory.T.weil_representation_continuity D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ, fun C hC => ?_⟩
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    rwa [κ.apply_symm_apply g] at h
  have hC' : IsCompact (κ.symm '' C) := hC.image (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  obtain ⟨U, hU, hlev⟩ := LWMaj.unifLevel hW hf _ hC'
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.Unf.mixS_support_inBox D ψ₀ hstd (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
    (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) U hU
  have hsupp : ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x, u x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    rintro u ⟨g, hg, rfl⟩ x hx
    rw [key] at hx
    exact hbox _ (hlev _ ⟨g, hg, rfl⟩) x 0 hx
  have hdec : ∀ N : ℕ, ∃ B : ℝ, ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x,
      ‖u x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ B := by
    intro N
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.Unf.mixS_decay D ψ₀ hstd θ hθ (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
      (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) N
    obtain ⟨B, hB⟩ := LWMaj.unifSob hstd hθ hW hf _ hC' N
    have hne : (C₂ : ℝ≥0∞) * (B : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
    refine ⟨((C₂ : ℝ≥0∞) * (B : ℝ≥0∞)).toReal, ?_⟩
    rintro u ⟨g, hg, rfl⟩ x
    have h := hC₂ (omh (κ.symm g, 1) f) (hW.om_pres _ _ hf) x 0
    change ‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ₑ * _ ≤ _ at h
    have h2 : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ₀ θ N (omh (κ.symm g, 1) f) ≤ C₂ * B :=
      mul_le_mul' le_rfl (hB _ ⟨g, hg, rfl⟩)
    rw [key]
    have h3 : ENNReal.ofReal (‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N) ≤
        (C₂ : ℝ≥0∞) * B := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      exact h.trans h2
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h3
  obtain ⟨M, hM, hle⟩ := LWMaj.adMaj θ hθ K hK _ hsupp hdec
  exact ⟨M, hM, fun g hg x => hle _ ⟨g, hg, rfl⟩ x⟩

end PositivityTheory.Rg.Rsw.L

end
end
end
