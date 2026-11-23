module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslatesScalarFormsSumIffStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousChartLevelCharactersAdelicTupleStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]

      rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllDataStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data : ∀ D : D7, GlobalTheory.SeeSaw.RamIff D := by
  first | exact @GlobalTheory.SeeSaw.ramIff_all | exact GlobalTheory.SeeSaw.ramIff_all | (intros; apply GlobalTheory.SeeSaw.ramIff_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuous

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RamCont

variable {D : D7}

theorem infM_mul' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem infM_fin' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    infM θ V hn k τ = 1 := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem continuous_infM' (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V hn g τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.continuous_infM θ hθ V τ

theorem pf_mul (V : HSp D) (g h : GA D V) :
    GlobalTheory.AdForm.RdLaw.pf V (g * h) = GlobalTheory.AdForm.RdLaw.pf V g * GlobalTheory.AdForm.RdLaw.pf V h := by
  apply Subtype.ext
  show GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V (g * h)) =
    GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V g) * GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V h)
  rw [map_mul, map_mul]

theorem pf_inv (V : HSp D) (g : GA D V) : GlobalTheory.AdForm.RdLaw.pf V g⁻¹ = (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pf_mul, inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]

theorem pf_inv_mul_mem (V : HSp D) (g : GA D V) : (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ * g ∈ GinfC V := by
  rw [GlobalTheory.CentreTarget.mem_GinfC, ← pf_inv, GlobalTheory.CentreTarget.mt_mul, Matrix.map_mul, GlobalTheory.AdForm.RdLaw.mt_pf,
    GlobalTheory.AdForm.RdLaw.PM_map, GlobalTheory.AdForm.RdLaw.finPart_eps, RingHom.map_sub, RingHom.map_one,
    GlobalTheory.AdForm.RdLaw.finPart_eps, sub_self, zero_smul, add_zero, one_smul, ← Matrix.map_mul,
    ← GlobalTheory.CentreTarget.mt_mul, inv_mul_cancel]
  show (matHom V 1).1.map _ = 1
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem infM_mul_pf (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k d : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V d)⁻¹ * d)) τ = infM θ V hn k τ * infM θ V hn d τ := by
  rw [infM_mul' θ V hn k, infM_mul' θ V hn _ d, infM_fin' θ V hn _ (inv_mem (GlobalTheory.AdForm.RdLaw.pf_fin V d)), one_mul]

end GlobalTheory.AdForm.RamCont

namespace GlobalTheory.AdForm.RamCont

theorem rd_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  classical
  intro B X I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ b y
  obtain ⟨hreps, -, -⟩ := GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hPins l Z u a Ch A hA j hj b
  have hchi := GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hI hPins l Z u a Ch A hA j hj b
  obtain ⟨hval, hrd⟩ := GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X j).gram
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨γ, hγ, c, k, hk, κ, hκ, e0⟩ := hreps.dec g0
  obtain ⟨P, -, hP⟩ := hval c.1
  let V := (I.rec7 l Z).sp.X j
  let hn := rankN (I.rec7 l Z) j hj
  have hpc : Continuous fun g : GA (I.rec7 l Z) V => GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) :=
    (GlobalTheory.AdForm.RdLaw.continuous_pf V).comp (continuous_const_mul g0⁻¹)
  let p : GA (I.rec7 l Z) V → GfC V := fun g => ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), GlobalTheory.AdForm.RdLaw.pf_fin V _⟩
  have hp : Continuous p := hpc.subtype_mk _
  let O : Set (GA (I.rec7 l Z) V) := {g | GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b}
  have hO : IsOpen O := by
    have h1 := hreps.opn.preimage hp
    have e : O = p ⁻¹' (((A.U j b).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := by
      ext g
      show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b ↔ p g ∈ (A.U j b).subgroupOf (GfC V)
      rw [Subgroup.mem_subgroupOf]
    rw [e]; exact h1
  have hg0 : g0 ∈ O := by
    show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g0) ∈ A.U j b
    rw [inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]; exact one_mem _
  let G : GA (I.rec7 l Z) V → ℂ := fun g =>
    if h : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b then ((A.chi j b ⟨_, h⟩ : ℂˣ) : ℂ) else 0
  have hG : ContinuousAt G g0 := by
    have hc : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (fun x : O => G x.1) = fun x : O => ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * x.1), x.2⟩ : ℂˣ) : ℂ) := by
        funext x
        exact dif_pos x.2
      show Continuous fun x : O => G x.1
      rw [e]
      exact hchi.comp ((hpc.comp continuous_subtype_val).subtype_mk _)
    exact hc.continuousAt (hO.mem_nhds hg0)
  let M : GA (I.rec7 l Z) V → (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ :=
    fun g τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ
  have hMu : ∀ g τ, IsUnit (M g τ).det := fun g τ => by
    simp only [M]
    erw [det_mul, det_mul]
    exact ((GlobalTheory.AdForm.RdVal.infM_unit θ V hn k τ).mul (GlobalTheory.AdForm.RdVal.infM_unit θ V hn _ τ)).mul (y.2 τ)
  have hM : ∀ τ, Continuous fun g =>
      (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ := by
    intro τ
    have h1 : Continuous fun g : GA (I.rec7 l Z) V => infM θ V hn (g0⁻¹ * g) τ :=
      (continuous_infM' θ hθ V hn τ).comp (continuous_const_mul g0⁻¹)
    show Continuous fun g : GA (I.rec7 l Z) V => (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * ((show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ)
    exact continuous_const.matrix_mul ((continuous_const.matrix_mul h1).matrix_mul continuous_const)
  let Φ : GA (I.rec7 l Z) V → ℂ := fun g =>
    (∏ τ, ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ).det ^
      shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ) *
    MvPolynomial.eval (fun q : (I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N j) × Fin ((I.rec7 l Z).R.N j) =>
      ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) q.1 * M g q.1) q.2.1 q.2.2) P
  have hΦ : Continuous Φ := by
    refine Continuous.mul (continuous_finsetProd _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · rw [Pi.one_apply, one_mul]; exact (hMu g τ).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine ContinuousAt.congr (f := fun g => ((A.chi j b ⟨κ, hκ⟩ : ℂˣ) : ℂ) * G g * Φ g)
    ((continuousAt_const.mul hG).mul hΦ.continuousAt) ?_
  filter_upwards [hO.mem_nhds hg0] with g hg
  have hU : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b := hg
  have hδi : (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g) ∈ GinfC V := pf_inv_mul_mem V _
  have hδf : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := GlobalTheory.AdForm.RdLaw.pf_fin V _
  have hκf : κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := mul_mem (hreps.le hκ) hδf
  have eg : g = γ * (A.h j b c * (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) *
      (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) := by
    have hc := Formalism.IndefR.Eqv.Act.comm_inf_fin hδi hκf
    calc g = g0 * (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by group
      _ = γ * (A.h j b c * k) * ((κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) *
          ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by rw [e0]; group
      _ = γ * (A.h j b c * k) * (((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)) *
          (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))) := by rw [hc]
      _ = _ := by group
  let y' : (I.chain l u a).Y j := ⟨M g, hMu g⟩
  have htr : IsTr (G := fun _ => 1) (infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_mul_pf θ V hn k (g0⁻¹ * g) τ]
    rfl
  have key := hrd b y γ hγ c _ (mul_mem hk hδi) ⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ y' htr
  rw [show A.rd θ j hj b φ y g = _ from (congrArg (A.rd θ j hj b φ y) eg).trans key]
  have e1 : (⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ : A.U j b) =
      ⟨κ, hκ⟩ * ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ := rfl
  have e2 : G g = ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ : ℂˣ) : ℂ) := dif_pos hU
  have e3 : Φ g = φ c.1 y' := congrFun hP ⟨M g, hMu g⟩
  rw [e1, map_mul, Units.val_mul, e2, e3, mul_assoc]

end GlobalTheory.AdForm.RamCont
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuousStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  first | exact @GlobalTheory.AdForm.RamCont.rd_continuous | exact GlobalTheory.AdForm.RamCont.rd_continuous | (intros; apply GlobalTheory.AdForm.RamCont.rd_continuous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_mul_level {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (γ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hγ : γ ∈ GQ ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (γ * x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ * (γ0 * (A.h j b c * k0) * κ0) * κ.1 = (γ * γ0) * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd (γ * γ0) (Subgroup.mul_mem _ hγ hγ0) c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

theorem ram_iff_scalar_ram : TwRam' := by
  intro B X I hOk hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd j hj φ hφ
  have hlaw := rd_mul_level I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ
  have hcont : ∀ b y, IsContAut _ (A.rd θ j hj b φ y) := fun b y =>
    ⟨fun γ hγ g => by simpa using hlaw b y g γ hγ 1, GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ b y⟩
  refine ⟨hcont, ?_⟩
  obtain ⟨e, he⟩ := hStd.1
  have : Finite ι := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ι
  have hlev := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hStd (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj
  have hfix : ∀ b y i (x : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), x • Q j i = Q j i →
      rTrans ((β j i).gl x) (A.rd θ j hj b φ y) = A.rd θ j hj b φ y := by
    intro b y i x hx
    obtain ⟨hm, h1⟩ := (hlev b).1 i x hx
    funext g
    have := hlaw b y g 1 (Subgroup.one_mem _) ⟨_, hm⟩
    simpa [rTrans, h1] using this
  choose gS hgS using fun (i : ι) (s : 𝓀[k]ˣ) =>
    MulAction.exists_smul_eq (GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (Q j i) (s • Q j i)
  have hram : ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y) ↔
      ∑ᶠ s, rTrans ((β j i).gl (gS i s)) (A.rd θ j hj b φ y) = 0 := by
    intro b y i
    rw [GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data (I.rec7 l Z) k (p i) (Fin _) _ (β j i) (Q j i) (gS i) (hgS i)]
    exact ⟨fun h => h.2.2, fun h => ⟨hcont b y, fun x hx => hfix b y i x hx, h⟩⟩
  have hdia := fun i => GlobalTheory.T.diamondTranslates_scalarForms_sum_iff I hOk hP l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ i (e i) (he i) (gS i) (hgS i)
  simp only [hram]
  unfold RamT
  constructor
  · rintro ⟨-, hR⟩ b y i
    exact (hdia i).2 (fun c => hR (e i) c) b y
  · intro h
    refine ⟨hφ, fun v c => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective v
    exact (hdia i).1 (fun b y => h b y i) c

end GlobalTheory.AdForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamifiedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
end
end
