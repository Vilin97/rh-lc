module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriodsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomRelationOfPin

section

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo


end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnFormStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  first | exact @GlobalTheory.Core.Mi.colDict_rd_eq_colForm | exact GlobalTheory.Core.Mi.colDict_rd_eq_colForm | (intros; apply GlobalTheory.Core.Mi.colDict_rd_eq_colForm <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpCEqSum

section

@[expose] public section



section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.MiTop.CenIsom
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}

theorem ipC_colDictL_eq_sum_inner_shP (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)
theorem ipC_colDictL_rtr_eq (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u P P').trans (Eq.trans ?_ (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'
end GlobalTheory.MiTop.CenIsom
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamified

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

open GlobalTheory.Core.Mi.CenAct in
theorem GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB u d z hP
  have hδ : ∀ k : Hfin W.S.X u, (d.B.toH d.a).2 * k = k * (d.B.toH d.a).2 := toH_snd_comm d.B hP.cen
  have hta : d.B.toH d.a = (1, (d.B.toH d.a).2) := Prod.ext (toH_fst d.B hP.fin) rfl
  generalize (d.B.toH d.a).2 = δ at hδ hta
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  let col : D.what₂.Mu u →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    e.symm.toLinearMap ∘ₗ (Submodule.inclusion hram) ∘ₗ (D.eMu u).toLinearMap
  have hcol : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (col φ) =
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  let mv : Cu W.S.X u W.S.Y.hK →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    (Formalism.L2.SG.ColDict.rtr W.S.X δ).restrict (fun T hT => rtr_mem_Cu W.S.Y.hK hδ hT)
  have hmv : ∀ T, (mv T).1 = Formalism.L2.SG.ColDict.rtr W.S.X δ T.1 := fun T => rfl
  have hmem : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) ∈ (D.mem u).A.Mram := fun φ =>
    GlobalTheory.MiTop.CenIsom.ram_rtr (W.S.tr u) W.S.Y.hK (W.S.lev u) (W.S.into u) (W.S.bij u) δ hδ (col φ) (mv (col φ)) (hmv _) (by rw [hcol]; exact (D.eMu u φ).2)
  let g0 : D.what₂.Mu u →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
    Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK ∘ₗ mv ∘ₗ col
  let fL : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := (D.eMu u).symm.toLinearMap ∘ₗ g0.codRestrict _ hmem
  have hfL : ∀ φ, ((D.eMu u (fL φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) := fun φ => by
    have h1 : D.eMu u (fL φ) = ⟨Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)), hmem φ⟩ :=
      (D.eMu u).apply_symm_apply _
    rw [h1]
  clear_value fL g0 mv col e
  have hinner : ∀ x y, ⟪fL x, fL y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by
    refine ((D.eMu_isom u (fL x) (fL y)).trans ?_).trans (D.eMu_isom u x y).symm
    refine (congrArg₂ ((D.fm u).ipC 0) (hfL x) (hfL y)).trans ?_
    refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_rtr_eq W.S hB.fin u δ hδ (col x) (col y) (mv (col x)) (mv (col y)) (hmv _) (hmv _)).trans ?_
    exact congrArg₂ ((D.fm u).ipC 0) (hcol x) (hcol y)
  let Li := fL.isometryOfInner hinner
  haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
  haveI : FiniteDimensional ℂ (D.mem u).A.Mram := Submodule.finiteDimensional_of_le hram
  haveI : FiniteDimensional ℂ (D.what₂.Mu u) := LinearEquiv.finiteDimensional (D.eMu u).symm
  have hsurj : Function.Surjective Li := (LinearMap.injective_iff_surjective (f := Li.toLinearMap)).1 Li.injective
  refine ⟨LinearIsometryEquiv.ofSurjective Li hsurj, ?_⟩
  intro φ C C₀ hC hC₀ ξ
  have e1 : C = mv (col φ) := (W.S.bij u).1 (hC.trans (hfL φ))
  have e2 : C₀ = col φ := (W.S.bij u).1 (hC₀.trans (hcol φ).symm)
  rw [e1, e2]
  funext g
  simp only [SBes.colForm, rTrans]
  rw [hmv]
  have h4 : d.B.toH (g * d.a⁻¹) * (1, δ) = d.B.toH g :=
    (congrArg (fun y => d.B.toH (g * d.a⁻¹) * y) hta.symm).trans
      ((toH_mul d.B _ _).symm.trans (congrArg d.B.toH (inv_mul_cancel_right g d.a)))
  exact (congrArg ((col φ).1 ξ) h4).symm
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamifiedStatement

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

theorem _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  first | exact @_root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | exact _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin | (intros; apply _root_.GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotRelTwo

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk
noncomputable section
namespace GlobalTheory.MiTop.BotTwo
variable {D : D7}
end GlobalTheory.MiTop.BotTwo

open GlobalTheory.MiTop.BotTwo in
theorem GlobalTheory.MiTop.botRel_of_pin_of_mem_center : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u), d.Pin z → _root_.GlobalTheory.MiTop.BottomRelation W z d := by
  intro _ hCR D L hT Gi Gl Kc Yd cX ex W hB z hzf hzc u d hP
  obtain ⟨-, hθ, hψ, hMatch, hχ, -⟩ := _root_.GlobalTheory.MiTop.botHyp_match_alt W hB
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.T.exists_isometry_colForm_eq_rTrans_of_pin W hB u d z hP
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D W.S.X W.Q.instEq u W.Q.Rl.ψ d.B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK W.Q.Rl.θ d.a₀
    hθ hB.idE hP.adapted hP.h0 (hB.hyp.2.1 u)
  have hRS := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D W.S.X W.Q.instEq W.Q.Rl.θ hθ hB.idE
  obtain ⟨c, hc⟩ := GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y hψ (hB.fin.inHH u)
  have hMt := hMatch z hzf hzc
  have hf1 : (iotaX W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS))).1 = 1 := (hRS.1 _).1 hMt.1
  have hcont : ∀ (C : Cu W.S.X u W.S.Y.hK) ξ', IsContAut (D.sp.X 0) (d.B.colForm C.1 ξ') := fun C =>
    (GlobalTheory.Core.Mi.PhCol.ph_colForm D W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0) d.B W.S.Y.hK C).1
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  have hcol : ∀ φ : D.what₂.Mu u, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK
      (e.symm (Submodule.inclusion hram (D.eMu u φ))) = (D.eMu u φ).1 := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  have L1 : ∀ (φ : D.what₂.Mu u) (C : Cu W.S.X u W.S.Y.hK), _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ y v,
      d.per φ T y v = _root_.GlobalTheory.MiTop.realCharacter W d.k * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) := by
    intro φ C hC T hT y v
    have hC₀ : _root_.GlobalTheory.MiTop.IsColumnForm W u (e.symm (Submodule.inclusion hram (D.eMu u φ))) φ := hcol φ
    have e1 : (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y =
        fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹) := by
      rw [← hcol φ]
      funext g
      rw [hξ _ y g, hR φ C _ hC hC₀ (ξ y)]
      simp only [rTrans]
      congr 1
      rw [mul_assoc, mul_inv_rev, (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hP.cen) d.a₀⁻¹)]
    have e2 : rTrans (embA d.B.d d.B.o (d.a₀ * d.a)) (rTrans d.b (T v)) =
        _root_.GlobalTheory.MiTop.realCharacter W d.k • rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v) := by
      funext g
      simp only [rTrans, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc g, hP.eq]
      refine Eq.trans (congrArg (T v) ?_) (lev_multT hT v hP.lev
        (g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) : GA D (D.sp.Y 0)))
      change g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)) =
        g * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) * d.k
      rw [mul_assoc g, mul_assoc ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))]
    have ea : rTrans (d.a₀ * d.a) (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹)) = d.B.colForm C.1 (ξ y) := by
      funext g; simp only [rTrans, mul_inv_cancel_right]
    have hsh := GlobalTheory.Core.Mi.per_rTrans D W.Q.Rl.ψ D.R.rS d.B.lev (fun g => d.B.colForm C.1 (ξ y) (g * (d.a₀ * d.a)⁻¹))
      (rTrans d.b (T v)) (d.a₀ * d.a) hψ (contAut_rTrans _ (hcont C (ξ y))) (contAut_rTrans _ (contAut_multT hT v))
    rw [ea] at hsh
    unfold _root_.GlobalTheory.MiTop.BottomData.per
    rw [e1, ← hsh, ← per_smul_f]
    exact congrArg _ e2
  refine ⟨R, ?_⟩
  intro φ φ' T hT T' hT' α α' hrel v C C' b b' hC hC' hb hb'
  have hrelξ : ∀ y v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 (ξ y))
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro y v
    have h0 := hrel y v
    rw [L1 φ C hC T hT, L1 φ' C' hC' T' hT'] at h0
    refine (mul_eq_zero.1 ?_).resolve_left (hχ _ hP.lev)
    rw [← h0]; ring
  have hrelAll : ∀ ξ' v, α * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T v)) +
      α' * d.B.lev.per W.Q.Rl.ψ (d.B.colForm C'.1 ξ')
        (rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T' v)) = 0 := by
    intro ξ' v
    have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hlin : ∀ C₁ : Cu W.S.X u W.S.Y.hK, d.B.colForm C₁.1 ξ' = ∑ i ∈ cf.support, cf i • d.B.colForm C₁.1 (ξ i) := by
      intro C₁
      rw [← hcf]
      funext g

      simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    rw [hlin C, hlin C',
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT v)) _ cf.support cf
        (fun i => d.B.colForm C.1 (ξ i)) (fun i _ => hcont C (ξ i)),
      GlobalTheory.SeeSaw.perSum_all D W.Q.Rl.ψ hψ D.R.rS d.B.lev _ (contAut_rTrans _ (contAut_multT hT' v)) _ cf.support cf
        (fun i => d.B.colForm C'.1 (ξ i)) (fun i _ => hcont C' (ξ i)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hrelξ i v
    linear_combination cf i * this
  have hσ : ∀ y : W.S.X.B.I.Ginf, ∃ σ : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] SmT (W.Q.Rl.MY 0), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ x,
      T (σ x) = rTrans ((iotaX W.S.X W.Q.instEq).symm (y, 1)) (T x) := by
    intro y
    obtain ⟨σ, hσ⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D W.Q.Rl.θ (D.sp.Y 0) _ (W.Q.Rl.MY 0) hθ
      ((iotaX W.S.X W.Q.instEq).symm (y, 1))
      ((hRS.2.1 _).2 (congrArg Prod.snd ((iotaX W.S.X W.Q.instEq).apply_symm_apply (y, 1))))
    exact ⟨σ, fun T hT x => hσ (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) T hT x⟩
  choose σ hσ using hσ
  have hpt : ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ v (y : W.S.X.B.I.Ginf),
      (fun g => evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T v)
        (iotaX W.S.X W.Q.instEq g * (y, W.S.X.xu u))) =
      rTrans ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS))) (T (σ y v)) := by
    intro T hT v y
    funext g
    rw [hσ y T hT v]
    simp only [evS, rTrans]
    exact congrArg (T v) (shift_swap (iotaX W.S.X W.Q.instEq).toMulEquiv g _ y (W.S.X.xu u) hf1)
  obtain ⟨φL, hφL, rfl⟩ := hb
  obtain ⟨φL', hφL', rfl⟩ := hb'
  rw [hc C _ φL (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T hT v).1 hφL,
    hc C' _ φL' (GlobalTheory.Core.Mi.rowFun_evS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) _ hθ hMt T' hT' v).1 hφL']
  refine comb_integral _ c α α' _ _ fun y => ?_
  refine Eq.trans ?_ (hrelAll (W.S.X.Wu u y) (σ y v))
  exact congrArg₂ (fun p q => α * p + α' * q) (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T hT v y))
    (congrArg (d.B.lev.per W.Q.Rl.ψ _) (hpt T' hT' v y))
end
end
end
end
