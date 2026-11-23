module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListAction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open Filter Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.LineAdd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tens_add_smul (f s : SInf F κ) (t : ℝ) (r : (κ → AF F) → ℂ) :
    tens (evI F) ⇑(f + t • s) r = tens (evI F) ⇑f r + (t : ℂ) • tens (evI F) ⇑s r := by
  funext x
  simp only [tens, SchwartzMap.add_apply, SchwartzMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

theorem hasDerivAt_of_curve {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f g : SInf F κ} {c : ℝ → SInf F κ}
    {r : (κ → AF F) → ℂ} (hc : ∀ t, T t (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) (hc0 : c 0 = f)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g)) :
    ∀ x, HasDerivAt (fun t => T t (tens (evI F) ⇑f r) x) (tens (evI F) ⇑g r x) 0 := by
  intro x
  have ev : ∀ y : κ → mixedEmbedding.mixedSpace F, Continuous fun s : SInf F κ => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have e : (fun t => T t (tens (evI F) ⇑f r) x) = fun t => tens (evI F) ⇑(c t) r x := by
    funext t; rw [hc t]
  rw [e, hasDerivAt_iff_tendsto_slope]
  refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, tens]
  rw [slope_def_module, hc0]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul, smul_eq_mul]
  ring

end

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem om_prod_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (a b : UA σ Y.J) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om (a * b, 1) Φ = om (a, 1) (om (b, 1) Φ) := by
  have e : ((a * b, (1 : UA σ Wd.J)) : UA σ Y.J × UA σ Wd.J) = (a, 1) * (b, 1) := by
    simp [Prod.mk_mul_mk]
  rw [e, map_mul, Module.End.mul_apply]

theorem om_one_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om ((1 : UA σ Y.J), (1 : UA σ Wd.J)) Φ = Φ := by
  rw [show ((1 : UA σ Y.J), (1 : UA σ Wd.J)) = (1 : UA σ Y.J × UA σ Wd.J) from rfl, map_one, Module.End.one_apply]

end GlobalTheory.LineAdd
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JointlyContinuousArchimedeanWeilAction

section

@[expose] public section

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
noncomputable section
namespace GlobalTheory.ArchJointCont
theorem tendsto_schrodinger_action_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh
  have hs := IsUWeilPair.isUSplitting hW
  let δ : ℝ → UA σ Y.J × UA σ Wd.J := fun t => (γ (Multiplicative.ofAdd t), 1)
  have hδc : Continuous δ := (hγ.1.comp continuous_ofAdd).prodMk continuous_const
  have hδ0 : δ 0 = 1 := by
    show (γ (Multiplicative.ofAdd 0), 1) = 1
    rw [ofAdd_zero, map_one]; rfl
  have hδm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)
    rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
  have ex := fun f => _root_.GlobalTheory.ArchLinePair.exists_orbit_pair_archimedean_line hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _)
    (fun t u _ => by simp [δ, mat]) f
  choose c g hc0 hslope hact using ex
  have hrr : ∀ x z, At (evI F) z → r (x + z) = r x := (hR 0).1
  have hinj := GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩
  have hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r :=
    fun t f => hact f t r (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r := by
    intro a f; funext x; simp [tens, mul_assoc]
  let A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := fun f => c f t
      map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add (f := _), hA, hA, tadd])
      map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }
  have hAf : ∀ t f, A t f = c f t := fun _ _ => rfl
  have hmul : ∀ s t f, c f (s + t) = c (c f t) s := fun s t f => hinj _ _ (by
    rw [← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])
  have hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f) := by
    intro f
    have h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)
    rw [zero_smul] at h1
    have h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f) := by
      have h1' := h1.add_const f
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]
    have h3 : ContinuousAt (fun s => c f s) 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]; exact h2
    have h4 := h3.tendsto
    rwa [hc0] at h4
  have hcont : ∀ f, Continuous fun s => c f s := by
    intro f
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0) := by
      have h5 := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at h5
    refine ((hcont0 (c f t₀)).comp ht).congr fun s => ?_
    show c (c f t₀) (s - t₀) = c f s
    rw [← hmul, sub_add_cancel]
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hAcont : ∀ t, Continuous (A t) := by
    intro t
    refine continuous_of_weak (A t) fun T => ?_
    obtain ⟨l, hl, hlf⟩ := exists_adm F T
    obtain ⟨T', hT'⟩ := hs.adm (δ t) l hl g₀ hg₀
    refine T'.continuous.congr fun f => ?_
    have e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀ := hact f t r₀ (hR₀ f)
    have e2 := hT' f
    rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
    exact e2.symm
  let 𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun i => ⟨A i, hAcont i⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hq := schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ 𝓕) := hq.banach_steinhaus fun q x => by
    have hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t) :=
      (hq.continuous_seminorm q).comp (hcont x)
    have := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have hk' : ∀ t, k t = c (h t) t := fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))
  have h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    intro U hU
    have hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈
        uniformity (SInf F (Fin n × Fin d)) := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨U, hU, fun p hp => hp⟩
    have ev := hE _ hU'
    have hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0) := by simpa using hh.sub_const h₀
    have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    refine Filter.mem_map.2 ?_
    filter_upwards [hz.eventually ev, ev3] with t ht ht'
    have := ht ⟨t, ht'⟩
    simpa [𝓕] using this
  have h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀)) := h1.add (hcont0 h₀)
  rw [zero_add] at h2
  refine h2.congr fun t => ?_
  rw [hk' t, map_sub]
  show c (h t) t - c h₀ t + c h₀ t = c (h t) t
  exact sub_add_cancel _ _
end GlobalTheory.ArchJointCont
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField

theorem _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  first | exact @_root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | exact _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | (intros; apply _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeAdditiveInLines

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open Filter Topology
noncomputable section
open scoped Classical
namespace GlobalTheory.LineAdd
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
theorem line_sum_curve_eq_prod (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hψ : IsStd ψ) (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om)
    {ι : Type} (γs : ι → (Multiplicative ℝ →* UA σ Y.J)) (hγs : ∀ i, γs i ∈ Lines σ Y)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr00 : r 0 ≠ 0) (hr : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) f r)
    (f : SInf F (Fin n × Fin d)) (g : ι → SInf F (Fin n × Fin d))
    (hg : ∀ i, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧ c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (g i))) :
    ∀ l : List ι, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om ((l.map fun i => γs i (Multiplicative.ofAdd t)).prod, 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧
      c 0 = f ∧ Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (l.map g).sum) := by
  have hr0 : ∃ x, r x ≠ 0 := ⟨0, hr00⟩
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 hr0
  have img : ∀ i (h : SInf F (Fin n × Fin d)) (t : ℝ), ∃ k : SInf F (Fin n × Fin d),
      om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑h r) = tens (evI F) ⇑k r := by
    intro i h t
    obtain ⟨c, -, hc, -⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW (γs i) (hγs i) h r (hr h)
    exact ⟨c t, hc t⟩
  intro l
  induction l with
  | nil =>
    refine ⟨fun _ => f, fun t => ?_, rfl, ?_⟩
    · simp only [List.map_nil, List.prod_nil]
      exact om_one_one om _
    · simp only [sub_self, smul_zero, List.map_nil, List.sum_nil]
      exact tendsto_const_nhds
  | cons i l' ih =>
    obtain ⟨c', hc', hc'0, hlim'⟩ := ih
    obtain ⟨ci, hci, hci0, hlimi⟩ := hg i
    set S' := (l'.map g).sum with hS'
    let s : ℝ → SInf F (Fin n × Fin d) := fun t => if t = 0 then S' else t⁻¹ • (c' t - f)
    choose k hk using fun t => img i (s t) t
    have hs : Tendsto s (𝓝 0) (𝓝 S') := by
      rw [← nhdsNE_sup_pure (0 : ℝ)]
      refine Tendsto.sup ?_ ?_
      · refine hlim'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [s, if_neg (show t ≠ 0 from ht)]
      · simp only [tendsto_pure_left, s, if_pos rfl]
        exact fun _ => mem_of_mem_nhds
    have hk' : Tendsto k (𝓝 0) (𝓝 S') :=
      _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action hP M ψ χX χW om hψ hG hW (γs i) (hγs i) r hr00 hr s k S' hk hs
    have hcs : ∀ t, c' t = f + t • s t := by
      intro t
      by_cases ht : t = 0
      · subst ht; simp [hc'0]
      · simp only [s, if_neg ht, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]
    refine ⟨fun t => ci t + t • k t, fun t => ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [om_prod_one, hc' t, hcs t, tens_add_smul, map_add (f := _), map_smul, hci t, hk t, tens_add_smul]
    · simp [hci0]
    · simp only [List.map_cons, List.sum_cons]
      refine (hlimi.add (hk'.mono_left nhdsWithin_le_nhds)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ ht', one_smul]
end GlobalTheory.LineAdd
open GlobalTheory.LineAdd GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.LineAdd.deriv_prod_lines_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om a b a' b' hpair ι l γs hγs γ _ hprod f _ f₁ fs hD hDs
  obtain ⟨r, hr00, hr⟩ := GlobalTheory.ThK.exists_rest_inf F (Fin n × Fin d)
  have hψ := hpair.base.std
  have hG := hpair.good
  have hW := hpair.weil
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 ⟨0, hr00⟩
  choose cs gs hcs hlims using fun i => _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M B.ψ χX χW om hψ hG hW (γs i) (hγs i) f r (hr f)
  have hcs0 : ∀ i, cs i 0 = f := by
    intro i
    refine canc _ _ ?_
    rw [← hcs i 0]
    simp only [ofAdd_zero, map_one]
    exact om_one_one om _
  have hlims' : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (cs i t - f)) (𝓝[≠] 0) (𝓝 (gs i)) := by
    intro i; simpa [hcs0 i] using hlims i
  have hfs : ∀ i, fs i = gs i := by
    intro i
    refine canc _ _ (funext fun x => ?_)
    exact (hDs i r (hr f) x).unique (hasDerivAt_of_curve (hcs i) (hcs0 i) (hlims' i) x)
  obtain ⟨c, hc, hc0, hlim⟩ := _root_.GlobalTheory.LineAdd.line_sum_curve_eq_prod hP M B.ψ χX χW om hψ hG hW γs hγs r hr00 hr f gs
    (fun i => ⟨cs i, hcs i, hcs0 i, hlims' i⟩) l
  have hc' : ∀ t, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r := by
    intro t; rw [hprod]; exact hc t
  have e1 : f₁ = (l.map gs).sum := by
    refine canc _ _ (funext fun x => ?_)
    exact (hD r (hr f) x).unique (hasDerivAt_of_curve hc' hc0 hlim x)
  rw [e1]
  congr 1
  exact List.map_congr_left fun i _ => (hfs i).symm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.line_derivative_additive_in_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  first | exact @_root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | exact _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | (intros; apply _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum <;> assumption)
end
end
end
