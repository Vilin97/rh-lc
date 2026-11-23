module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.WeilBound.ThetaLifts.Reductions.MetaDef
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TraceBlocks
public import Development.WeilBound.ThetaLifts.Reductions.SymplOfMem
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieG

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieI

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MeasureTheory

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem box_SB {g g' : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (hg' : g' ∈ SB (κ → Af F)) :
    boxFun g g' ∈ SB (κ ⊕ κ → Af F) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  refine ⟨(hg.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (by fun_prop)).mul
    (hg'.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hg.2.prod hg'.2).image
    (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := Af F)).symm.continuous) fun x hx => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩

variable (F κ) in
theorem exists_box : ∃ (f : SInf F κ) (B : SInf F (κ ⊕ κ)) (r : (κ → mixedEmbedding.mixedSpace F) → ℝ),
    (∀ x, B x = f (x ∘ Sum.inl) * f (x ∘ Sum.inr)) ∧ (∀ x, f x = r x) ∧ Continuous r ∧ HasCompactSupport r ∧ r 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h3 : HasCompactSupport fun x : κ ⊕ κ → mixedEmbedding.mixedSpace F =>
      ((b (x ∘ Sum.inl) : ℝ) : ℂ) * ((b (x ∘ Sum.inr) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro ((h1.prod h1).image
      (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := mixedEmbedding.mixedSpace F)).symm.continuous)
      fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩
  exact ⟨h1.toSchwartzMap h2, h3.toSchwartzMap ((h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inl i))).mul
    (h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inr i)))), b, fun _ => rfl, fun _ => rfl, b.continuous,
    b.hasCompactSupport, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)⟩

variable (F κ) in
theorem exists_form (ψ : AddChar (AF F) ℂ) : ∃ l ∈ (adeleClass F).adm (κ ⊕ κ),
    (∀ x y : κ → AF F, ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧
      ∃ (B : SInf F (κ ⊕ κ)), ∃ G ∈ SB (κ ⊕ κ → Af F), l (pureA F B G) ≠ 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  borelize (κ → Af F)
  let X := κ → mixedEmbedding.mixedSpace F
  borelize X
  let μ : Measure X := Measure.addHaar
  let ν : Measure (κ → Af F) := Measure.addHaar
  haveI : MeasurableAdd X := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → Af F) := ContinuousAdd.measurableAdd
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  let k : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] (X × (κ → Af F) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun p => Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {φ | Integrable (k φ) (μ.prod ν)}
      zero_mem' := integrable_zero _ _ _
      add_mem' := fun ha hb => ha.add hb
      smul_mem' := fun c _ h => h.smul c }
  let l0 : N →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ p, k φ p ∂(μ.prod ν)
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c _ }
  obtain ⟨l, hl⟩ := l0.exists_extend
  have hl' : ∀ φ ∈ N, l φ = ∫ p, k φ p ∂(μ.prod ν) := fun φ h => LinearMap.congr_fun hl ⟨φ, h⟩
  let dg : X →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.elim id id i)
  have hdg : AntilipschitzWith 1 dg := AddMonoidHomClass.antilipschitz_of_bound dg fun x => by
    rw [NNReal.coe_one, one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (dg x) (Sum.inl i)
  let Rs : SInf F (κ ⊕ κ) →L[ℂ] 𝓢(X, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ dg.hasTemperateGrowth hdg
  have hk : ∀ (B : SInf F (κ ⊕ κ)) (G : (κ ⊕ κ → Af F) → ℂ),
      k (pureA F B G) = fun p => Rs B p.1 * G (Sum.elim p.2 p.2) := fun B G => by
    funext p
    refine congrArg₂ (· * ·) (congrArg B (funext fun i => ?_)) (congrArg G (funext fun i => ?_))
    · rcases i with i | i <;> exact RingEquiv.apply_symm_apply _ _
    · rcases i with i | i <;> rfl
  have hc : Continuous fun b : κ → Af F => (Sum.elim b b : κ ⊕ κ → Af F) :=
    continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i
  have hG : ∀ G ∈ SB (κ ⊕ κ → Af F), Integrable (fun b : κ → Af F => G (Sum.elim b b)) ν := fun G hG =>
    (hG.1.continuous.comp hc).integrable_of_hasCompactSupport (hG.2.comp_isClosedEmbedding
      (Function.LeftInverse.isClosedEmbedding (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (fun _ => rfl) (by fun_prop) hc))
  have hp : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F), pureA F B G ∈ N := fun B G h => by
    show Integrable (k _) _
    rw [hk]
    exact (Rs B).integrable.mul_prod (hG G h)
  have hv : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F),
      l (pureA F B G) = (∫ a, Rs B a ∂μ) * ∫ b, G (Sum.elim b b) ∂ν := fun B G h => by
    rw [hl' _ (hp B G h), hk]
    exact integral_prod_mul (Rs B) fun b => G (Sum.elim b b)
  refine ⟨l, fun G h => ⟨(∫ b, G (Sum.elim b b) ∂ν) • (SchwartzMap.integralCLM ℂ μ ∘L Rs), fun B => ?_⟩,
    fun x y φ hφ => ?_, ?_⟩
  · rw [hv B G h, mul_comm]
    rfl
  · have hN : φ ∈ N := (Submodule.span_le.2 (by rintro _ ⟨B, G, h, rfl⟩; exact hp B G h) : schA F (κ ⊕ κ) ≤ N) hφ
    let c : X × (κ → Af F) := (fun i => evI F (x i), fun i => (x i).2)
    have e : k (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = fun p => k φ (c + p) := by
      funext p
      have e1 : SeminormBoundRestriction.pt (c + p).1 (c + p).2 = SeminormBoundRestriction.pt p.1 p.2 + x := funext fun i =>
        Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _).trans ((add_comm _ _).trans
          (congrArg (_ + ·) (RingEquiv.symm_apply_apply _ _)))) (add_comm _ _)
      show schr _ _ _ (Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)) =
        φ (Sum.elim (SeminormBoundRestriction.pt (c + p).1 (c + p).2) (SeminormBoundRestriction.pt (c + p).1 (c + p).2))
      rw [e1, schr, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
      simp only [dotProduct_neg, add_neg_cancel, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      funext i
      rcases i with i | i <;> rfl
    rw [hl' _ hN, hl' _ (by
      show Integrable (k _) _
      rw [e]
      exact (show Integrable (k φ) (μ.prod ν) from hN).comp_add_left c), e]
    exact integral_add_left_eq_self (k φ) c
  · obtain ⟨f, B, r, hB, hf, hr, hr', hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    have hg' : (fun x => ((‖g x‖ : ℝ) : ℂ)) ∈ SB (κ → Af F) :=
      ⟨hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ), hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
    refine ⟨B, _, box_SB hg' hg', ?_⟩
    rw [hv _ _ (box_SB hg' hg')]
    refine mul_ne_zero ?_ ?_
    · have : ∀ a, Rs B a = ((r a * r a : ℝ) : ℂ) := fun a => by
        rw [ofReal_mul, ← hf]
        exact hB _
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hr.mul hr).integral_pos_of_hasCompactSupport_nonneg_nonzero hr'.mul_left (fun _ => mul_self_nonneg _)
        (x := 0) (by simp [hr0])).ne'
    · have : ∀ b, boxFun (fun x => ((‖g x‖ : ℝ) : ℂ)) (fun x => ((‖g x‖ : ℝ) : ℂ)) (Sum.elim b b) =
          ((‖g b‖ * ‖g b‖ : ℝ) : ℂ) := fun b => (ofReal_mul _ _).symm
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hg.1.continuous.norm.mul hg.1.continuous.norm).integral_pos_of_hasCompactSupport_nonneg_nonzero
        hg.2.norm.mul_left (fun _ => mul_self_nonneg _) (x := y) (by simp [hy])).ne'

end PositivityTheory.RL.Up

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.Reductions.LieScalar2

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex

namespace PositivityTheory.ThKR

open PositivityTheory.RL PositivityTheory.RL.Up

theorem lieSecond2 (hM : LocalLift) : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.LieSecond := by
  set_option backward.isDefEq.respectTransparency false in
    intro hD0 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om χ m hcm hψ hfr hΦ hW hm γ hγ Y hY T
    obtain ⟨hom, dd, omd, hdd, ⟨-, homd, hS⟩, hres⟩ := hW
    obtain ⟨D, hD⟩ := hD0 F E σ α β κ ψ JA JB d hψ
    obtain ⟨Dd, hDd⟩ := hD0 F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
    have iD : IsD d D := fun u hu f => (hD u hu f).2
    have iDd : IsD dd Dd := fun u hu f => (hDd u hu f).2
    obtain ⟨c, hc⟩ := main2 hM hcm hψ τ (fun w => (b • JB.map (piInf (τ w))).map star)
      (fun w => (frame_K (hfr.2.2 w)).1) (fun w => (frame_K (hfr.2.2 w)).2) (fun w => iff_K (frame_K (hfr.2.2 w)).2) hom iD
    have eK : ∀ w, (b • (dbl JB).map (piInf (τ w))).map star = Matrix.fromBlocks ((b • JB.map (piInf (τ w))).map star) 0 0
        (-(b • JB.map (piInf (τ w))).map star) := fun w => by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
    have uK : ∀ w, IsUnit ((b • (dbl JB).map (piInf (τ w))).map star).det := fun w => by
      rw [eK, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
      exact (frame_K (hfr.2.2 w)).2.mul ((isUnit_one.neg.pow _).mul (frame_K (hfr.2.2 w)).2)
    obtain ⟨c', hc'⟩ := main2 hM hcm hψ τ (fun w => (b • (dbl JB).map (piInf (τ w))).map star)
      (fun w => by
        simp only [eK, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_zero,
          (frame_K (hfr.2.2 w)).1]) uK (fun w => iff_K (uK w)) homd iDd
    obtain ⟨Z, tr, hZ, hdet, hre, u, v, hu, hv, huv, hq⟩ := fock_data hcm hfr hΦ (fun u hu f => (hD u hu f).1) hY
    have split : ∀ x : Matrix α (β ⊕ β) (AE F E), At (evI F) x → ∃ x₁ x₂, At (evI F) x₁ ∧ At (evI F) x₂ ∧
        x = Matrix.fromCols x₁ x₂ := fun x hx =>
      ⟨x.toCols₁, x.toCols₂, fun s hs => congrArg Matrix.toCols₁ (hx s hs), fun s hs => congrArg Matrix.toCols₂ (hx s hs),
        (Matrix.fromCols_toCols x).symm⟩
    have z0 : At (evI F) (0 : Matrix α β (AE F E)) := fun _ _ => smul_zero _
    have step2 : ∑ w, c w * (Y w).trace = ∑ w, c' w * (Y w).trace := by
      obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ (γ' := 1) ⟨continuous_const, fun t s _ => by
        change s • ((1 : Matrix β β (AE F E)) - 1) = 0
        simp⟩
      obtain ⟨f, B, r, hB, hf, -, -, hr0⟩ := exists_box F κ
      obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
      let x := SeminormBoundRestriction.pt (0 : κ → mixedEmbedding.mixedSpace F) y
      have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 0) (fun t w => by
        rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks, NormedSpace.exp_zero]
        simp) _ (fun j => Matrix.fromCols (u j) 0) (fun j => Matrix.fromCols (v j) 0) (fun j => at_cols (hu j) z0)
        (fun j => at_cols (hv j) z0) (fun x hx w => by
          obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
          simp only [sB_dbl hdd, sB_zero d, sub_zero, Matrix.fromBlocks_transpose, Matrix.fromCols_map,
            Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, huv x₁ h₁]
          ext i j
          rcases j with j | j <;> simp [Matrix.sum_apply]) B _ (box_SB hg hg) _ (SeminormBoundRestriction.eval_adm (Sum.elim x x))
      have h2 := (hc γ hγ Z hZ _ u v hu hv huv f g hg _ (SeminormBoundRestriction.eval_adm x)).mul_const (pureA F f g x)
      have eB : ∀ (B : SInf F (κ ⊕ κ)), pureA F B (boxFun g g) (Sum.elim x x) = B 0 := fun B => by
        have : Sum.elim x x = SeminormBoundRestriction.pt 0 (Sum.elim y y) := funext fun i => by rcases i with i | i <;> rfl
        rw [this, SeminormBoundRestriction.pureA_pt]
        show _ * (g y * g y) = _
        rw [hy, mul_one, mul_one]
      have ef : ∀ f : SInf F κ, pureA F f g x = f 0 := fun f => by rw [SeminormBoundRestriction.pureA_pt, hy, mul_one]
      have e3 : pureA F B (boxFun g g) = boxFun (pureA F f g) (pureA F f g) := by
        funext p
        simp only [pureA, boxFun, hB]
        exact mul_mul_mul_comm _ _ _ _
      have h3 := h1.unique (h2.congr_of_eventuallyEq (.of_forall fun t => by
        show omd _ _ _ = _
        rw [e3, hres (γ (Multiplicative.ofAdd t)) _ (hδ' _) _ (pure_mem f hg) _ (pure_mem f hg)]
        rfl))
      have f0 : f 0 = 1 := by rw [hf, hr0, ofReal_one]
      have bb : ∀ p q : Matrix α β (AE F E), At (evI F) p → At (evI F) q →
          Dd (Matrix.fromCols p 0) (Dd (Matrix.fromCols q 0) B) 0 = D p (D q f) 0 := fun p q hp hq =>
        (box_D hdd iD iDd hp (box_D hdd iD iDd hq hB) 0).trans (by
          show D p (D q f) 0 * f 0 = _
          rw [f0, mul_one])
      have B0 : B 0 = 1 := (hB 0).trans (by
        show f 0 * f 0 = 1
        rw [f0, mul_one])
      simp only [LinearMap.proj_apply, eB, ef, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply,
        bb _ _ (hu _) (hv _), bb _ _ (hv _) (hu _), f0, B0, mul_one, smul_eq_mul, add_right_inj, trace_blocks,
        Matrix.trace_zero, add_zero, tr] at h3
      exact h3.symm
    have step1 : ∑ w, c' w * (Y w).trace = ∑ w, (m w : ℂ) / 2 * (Y w).trace := by
      obtain ⟨δ, hδ, hδ'⟩ := exists_dbl hγ hγ
      obtain ⟨l, hl, hinv, B, G, hG, hne⟩ := exists_form F κ ψ
      obtain ⟨T0, hT0⟩ := hl G hG
      have kill : ∀ y, At (evI F) y → ∀ B', T0 (Dd (Matrix.fromCols y y) B') = 0 := fun y hy B' => by
        have h1 := (hDd _ (at_cols hy hy) B').1 G hG l hl
        have e : ∀ t : ℝ, l (dd.rho ψ (realAd F t • Matrix.fromCols y y) (pureA F B' G)) = l (pureA F B' G) := fun t => by
          rw [show realAd F t • Matrix.fromCols y y = Matrix.fromCols (realAd F t • y) (realAd F t • y) by
            ext i j
            rcases j with j | j <;> rfl, Darboux.rho, hdd, hinv _ _ _ (pure_mem B' hG)]
        simp only [e] at h1
        rw [← hT0]
        exact h1.unique (hasDerivAt_const _ _)
      let hf : AF F := realAd F (1 / 2)
      have hh : ∀ j, At (evI F) (hf • u j) := fun j s hs => by rw [smul_comm, hu j s hs, smul_zero]
      have ng : ∀ {p : Matrix α β (AE F E)}, At (evI F) p → At (evI F) (-p) := fun hp s hs => by
        rw [smul_neg, hp s hs, neg_zero]
      have h1 := hc' δ hδ (fun w => Matrix.fromBlocks (Z w) 0 0 (Z w)) (fun t w => by
        rw [hδ', Matrix.fromBlocks_map, hZ, Matrix.fromBlocks_smul, smul_zero, exp_blocks]
        simp) _
        (Sum.elim (fun j => Matrix.fromCols (hf • u j) (hf • u j)) fun j => Matrix.fromCols (hf • u j) (-(hf • u j)))
        (Sum.elim (fun j => Matrix.fromCols (v j) (-v j)) fun j => Matrix.fromCols (v j) (v j))
        (by rintro (j | j); exacts [at_cols (hh j) (hh j), at_cols (hh j) (ng (hh j))])
        (by rintro (j | j); exacts [at_cols (hv j) (ng (hv j)), at_cols (hv j) (hv j)]) (fun x hx w => by
          obtain ⟨x₁, x₂, h₁, h₂, rfl⟩ := split x hx
          simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sB_dbl hdd, sB_neg d, Matrix.fromBlocks_transpose,
            Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_zero, Matrix.mul_zero, add_zero, zero_add,
            huv x₁ h₁, huv x₂ h₂, ← Finset.sum_add_distrib]
          ext i k
          rcases k with k | k <;>
          · simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.sum_apply, Matrix.add_apply,
              Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, hf, Fock.piInf_realAd hcm.1, real_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            push_cast
            ring) B G hG l hl
      have h2 : ∀ t : ℝ, l (omd (δ (Multiplicative.ofAdd t)) (pureA F B G)) =
          cexp (t * ∑ w, (m w : ℂ) * (Y w).trace) * l (pureA F B G) := fun t => by
        have n1 : ∀ w, ‖cexp (t * (Y w).trace)‖ = 1 := fun w => by simp [norm_exp, hre]
        have ad := at_det (hγ.2 (Multiplicative.ofAdd t))
        rw [hS l hl (fun z φ hφ => by
          rw [show z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z by
            simp [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols], Darboux.rho, hdd, hinv _ _ _ hφ])
          (δ (Multiplicative.ofAdd t)) (γ (Multiplicative.ofAdd t)).1 (by
            rw [hδ']
            simp [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
            rfl) _ (pure_mem B hG),
          show Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (γ (Multiplicative.ofAdd t)).1) = 1
            from Units.ext (norm_eq_one hcm τ ad fun w => (congrArg norm (hdet t w)).trans (n1 w)),
          hm _ ad]
        simp only [map_one, NNReal.coe_one, Real.one_rpow, ofReal_one, mul_one]
        congr 1
        rw [Finset.mul_sum, Complex.exp_sum]
        apply Finset.prod_congr rfl
        intro w hw
        change (piInf (τ w) (Matrix.det (γ (Multiplicative.ofAdd t)).1.1) /
          ‖piInf (τ w) (Matrix.det (γ (Multiplicative.ofAdd t)).1.1)‖) ^ m w = _
        have he : piInf (τ w) (Matrix.det (γ (Multiplicative.ofAdd t)).1.1) =
            cexp (t * (Y w).trace) := hdet t w
        rw [he, n1, ofReal_one, div_one, ← Complex.exp_int_mul]
        congr 1
        push_cast
        ring
      change HasDerivAt (fun t => l (omd (δ (Multiplicative.ofAdd t)) (pureA F B G))) _ 0 at h1
      rw [show (fun t => l (omd (δ (Multiplicative.ofAdd t)) (pureA F B G))) =
        (fun t : ℝ => cexp (t * ∑ w, (m w : ℂ) * (Y w).trace) * l (pureA F B G)) from funext h2] at h1
      have h3 := h1.unique ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const
        (∑ w, (m w : ℂ) * (Y w).trace)).cexp).mul_const (l (pureA F B G)))
      have t1 : ∀ j, T0 (Dd (Matrix.fromCols (v j) (-v j)) (Dd (Matrix.fromCols (hf • u j) (hf • u j)) B)) =
          2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B := fun j => by
        rw [iDd.comm (at_cols (hv j) (ng (hv j))) (at_cols (hh j) (hh j)), map_add (f := _), kill _ (hh j), map_smul, sB_dbl hdd,
          sB_neg d, zero_add, smul_eq_mul]
        congr 3
        ring
      have t2 : ∀ j, T0 (Dd (Matrix.fromCols (hf • u j) (-(hf • u j))) (Dd (Matrix.fromCols (v j) (v j)) B)) =
          -(2 * π * I * (2 * sB σ JA JB (v j) (hf • u j) : ℝ) * T0 B) := fun j => by
        rw [iDd.comm (at_cols (hh j) (ng (hh j))) (at_cols (hv j) (hv j)), map_add (f := _), kill _ (hv j), map_smul, sB_dbl hdd,
          sB_neg d, zero_add, smul_eq_mul, sB_anti d]
        push_cast
        ring
      rw [hT0] at hne

      simp only [hT0, map_add (f := _), map_smul, map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, kill _ (hh _),
      kill _ (hv _), t1, t2, zero_add, add_zero, Finset.sum_neg_distrib, add_neg_cancel, smul_zero, smul_eq_mul,
      trace_blocks, tr, id, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ofReal_one, mul_zero] at h3
      have h4 := mul_right_cancel₀ hne h3
      simp only [mul_add, Finset.sum_add_distrib] at h4
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, ← h4]
      ring
    have := hc γ hγ Z hZ _ u v hu hv huv (Φ T)
    simp only [tr, hq, step2, step1] at this
    rw [sumPl_add]
    exact this

end PositivityTheory.ThKR

end
end
end
