module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfOrthogonalRealTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeMultiplicityMapValueEq
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodEqZeroOfVanishingOnKFiniteValues

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.KFinPer

open Formalism.MainNotions.S
open scoped Classical

variable {D : D7}

theorem isMultMap_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hPu := M.fr_unit τ
  have hG := M.fr_gram τ
  choose ℓ hℓ hℓT using fun g : GA D V => hT.cont τ v g
  have hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ := fun u hu =>
    Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG u).2 hu)
  obtain ⟨L, C, hL, hC⟩ := GlobalTheory.SobUnif.unif_model hσ ℓ
    (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hPu hG (hℓ g))
    (fun u hu => by
      obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut (Function.update v τ ⟨u, hsm u hu⟩))
        (hT.cusp (Function.update v τ ⟨u, hsm u hu⟩))
      exact ⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g⟩)
  refine ⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g => ?_⟩
  · intro l hl Y hY
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hPu)) hG
      (hL l0 hl0 X hX)
  · have hw := (GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG (w : M.H τ)).1
      (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)
    have h1 := hC g (w : M.H τ) hw
    rw [hℓT g w] at h1
    refine h1.trans_eq ?_
    congr 1
    rw [GlobalTheory.SmoothGlob.sobNorm, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
    exact congrArg norm (GlobalTheory.SobUnif.foldr_conj_eq (M.σ τ) hPu l (w : M.H τ)).symm

theorem mult_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M}
    (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact isMultMap_bound hP θ hθ M J χ T hT τ v
  | zero => exact ⟨[], 0, by simp, fun w g => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g) (hb₂ w g)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g) (norm_nonneg _)

theorem per_eq_zero_of_kF : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  intro hP hHC D θ hθ V S M J χ y hy X _ ν e u he hu h0 a
  have : BorelSpace (GA D V) := ⟨rfl⟩
  set T' : MMap M := PiTensorProduct.lift.symm y with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ y).1 hy
  have hTt : ∀ w : M.Vec, y (PiTensorProduct.tprod ℂ w) = T' w := by
    intro w
    have : y = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply y).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hval : ∀ b, Continuous (y b) ∧ ∃ B : ℝ, ∀ g, ‖y b g‖ ≤ B := by
    intro b
    obtain ⟨h1, h2, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ y hy b
    exact ⟨h1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ h1 h2⟩
  have hint : ∀ b, Integrable (fun x => y b (e x) * u x) ν := by
    intro b
    obtain ⟨hc, B, hB⟩ := hval b
    have hm : AEStronglyMeasurable (fun x => y b (e x)) ν :=
      (hc.measurable.comp he).aestronglyMeasurable
    first
      | exact hu.bdd_mul hm ⟨B, fun x => hB (e x)⟩
      | exact hu.bdd_mul hm (Filter.Eventually.of_forall fun x => hB (e x))
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun b => ∫ x, y b (e x) * u x ∂ν
      map_add' := fun b c => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint b) (hint c)
      map_smul' := fun c b => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hsep : GlobalTheory.Core.Mi.SepCont M Λ := by
    intro τ v
    obtain ⟨L, Cu, hL, hb⟩ := mult_bound hP θ hθ M J χ hT'm τ v
    let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
      intro w
      have := congrArg (fun m => m w) hℓ
      simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ⟨L, Cu * ∫ x, ‖u x‖ ∂ν, hL, fun w hw => ?_⟩, hℓw⟩
    have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    rw [hℓw ⟨w, hw'⟩]
    change ‖∫ x, y (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩)) (e x) * u x ∂ν‖ ≤ _
    rw [hTt]
    set s := (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum
    have hpt : ∀ x, ‖T' (Function.update v τ ⟨w, hw'⟩) (e x) * u x‖ ≤ Cu * s * ‖u x‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb ⟨w, hw'⟩ (e x)) (norm_nonneg _)
    calc _ ≤ ∫ x, Cu * s * ‖u x‖ ∂ν :=
          norm_integral_le_of_norm_le (hu.norm.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Cu * s * ∫ x, ‖u x‖ ∂ν := integral_const_mul _ _
      _ = _ := by ring
  have hΛ : Λ = 0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D V S M Λ hsep fun v hv =>
    h0 _ (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  exact congrArg (fun L : SmT M →ₗ[ℂ] ℂ => L a) hΛ

end GlobalTheory.SepPer.KFinPer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodEqZeroOfVanishingOnKFiniteValuesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  first | exact @GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | exact GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | (intros; apply GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PeriodNePf

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}


open Classical in
theorem real_translate (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} :
    ∀ a ∈ GinfC V, ∀ v : SmT M, ∃ v' : SmT M, ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine GlobalTheory.Core.Rk.TopOnto.real_induction hθ _ (fun v => ⟨v, fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, f1⟩ := hb v
    obtain ⟨v₂, f2⟩ := ha v₁
    exact ⟨v₂, fun T hT h => by rw [f2 T hT, f1 T hT, mul_assoc]⟩
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), GlobalTheory.Core.Rk.TopOnto.rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), fun T hT h => ?_⟩
      rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
        GlobalTheory.Core.Rk.TopOnto.multT_rel v (Function.update v τ w) (h * atTau θ V τ g) h 1 (fun m hm => by
          rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', f1⟩ := ha
      obtain ⟨b', f2⟩ := hb
      exact ⟨a' + b', fun T hT h => by rw [map_add, map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]⟩

end General

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

variable {D : D7}

theorem exists_kf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hHC : GlobalTheory.Published.HarishChandraModules)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0)))
    {t : SmT M₀ →ₗ[ℂ] (GA D (Yc D 0) → ℂ)} (ht : t ∈ Rows L W.θ M₀)
    {y : SmT MP →ₗ[ℂ] (GA D (G.V (.core 0)) → ℂ)} (hy : y ∈ CoreForms G W.θ 0 MP) (v : SmT MP) (w' : SmT M₀)
    (h0 : per0 G M (y v) (t w') ≠ 0) (w : SmT M₀) (hw : w ≠ 0) :
    ∃ a ∈ KF MP, per0 G M (y a) (t w) ≠ 0 := by
  have hθ := W.θ_is
  obtain ⟨hμ, hfd⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vY : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hμ, hfd⟩
  have hyv : ∀ a, RapidDec (G.V (.core 0)) (y a) := fun a =>
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ MP W.θ hθ _ _ y hy a).2.2
  have htw : RapidDec (Yc D 0) (t w) :=
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ M₀ W.θ hθ _ _ t ht w).2.2
  have hF : GlobalTheory.Unf.IsContAut (Yc D 0) (fun g => y v (stabilizerEmbedding G.sp.dec0 g)) :=
    ⟨fun γ hγ g => by
      simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      exact (hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ) _,
      (hyv v).2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _)⟩
  have hB : ∃ C, ∀ g, ‖y v (stabilizerEmbedding G.sp.dec0 g)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hyv v).2.2 0
    exact ⟨C, fun g => by simpa using hC (stabilizerEmbedding G.sp.dec0 g)⟩
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ GinfC (Yc D 0),
      ∫ g in vY.𝓕, y v (stabilizerEmbedding G.sp.dec0 g) * t w (g * h) ∂vY.μ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h0 (GlobalTheory.T.integral_eq_zero_of_orthogonal_real_translates hCR GlobalTheory.Mem.VolFin.finVol D W.θ hθ (Yc D 0) _ M₀ _ _ t ht vY _ hF hB w hw hn w')
  have e1 := GlobalTheory.QPl.LastOrb.setIntegral_mul_right vY
    (fun g => y v (stabilizerEmbedding G.sp.dec0 (g * h⁻¹)) * t w g) (fun γ hγ g => by
      simp only [mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      rw [(hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ), htw.1 γ hγ g]) h
  simp only [mul_inv_cancel_right] at e1
  have hinf : stabilizerEmbedding G.sp.dec0 h⁻¹ ∈ GinfC (G.V (.core 0)) := GlobalTheory.RealType.Emb_mem_inf G.sp.dec0 (inv_mem hh)
  obtain ⟨v', hv'⟩ := real_translate hθ (M := MP) (J := (lev G (.core 0) : Set _)) (χ := 1) _ hinf v
  have hp : per0 G M (y v') (t w) ≠ 0 := by
    unfold per0
    simp only [hv' y hy]
    rw [e1] at hne
    simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul] at hne
    exact hne
  by_contra hn
  push_neg at hn
  have key := GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values hCR hHC D W.θ hθ (G.V (.core 0)) _ MP _ _ y hy (GA D (Yc D 0)) (vY.μ.restrict vY.𝓕)
    (stabilizerEmbedding G.sp.dec0) (t w) (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _).measurable
    (htw.integrableOn_fundamentalDomain hμ hfd) (fun a ha => hn a ha) v'
  exact hp key

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

end GlobalTheory.PeriodNePf

end
end
end
