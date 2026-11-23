module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.TopPow

open ReciprocityTheory.L2DbarEstimates (cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, GlobalTheory.CxForm.DensPow.dens_pow, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {L : LB X.X}

theorem dens_loc_c1W_pow (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    (y : CxPts X.str σ) (hy : y ∈ c.e.source) :
    (dens ((atlas X σ).loc (fld (atlas X σ) (c1W ψ ^ X.dim)) c (c.e y))).re = c.chernDens ψ y := by
  have e := (atlas X σ).loc_crd (fld (atlas X σ) (c1W ψ ^ X.dim)) (⟨(c, y), hy⟩ : (atlas X σ).Pt)
  erw [e]
  have hs := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  erw [fld, Pi.pow_apply, c1W, dens_ofValues_ddc_pow X.dim _ _ hs]
  rfl

theorem part_c1W_pow : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  intro F _ σ X L ψ hψ ε
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_c1W_pow ψ hψ c _ hy]

end GlobalTheory.ChernCalc.TopPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartFirstChernFormOfWeightPowEqChernPartStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  first | exact @GlobalTheory.ChernCalc.TopPow.part_c1W_pow | exact GlobalTheory.ChernCalc.TopPow.part_c1W_pow | (intros; apply GlobalTheory.ChernCalc.TopPow.part_c1W_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumber

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have eval_add (G₁ G₂ : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂) =
        evalF (atlas X σ) (fun a => c1W (ψ a)) G₁ + evalF (atlas X σ) (fun a => c1W (ψ a)) G₂ := by
    funext x
    simp [evalF, fld]
  have eval_smul (t : ℝ) (G : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G) =
        (t : ℂ) • evalF (atlas X σ) (fun a => c1W (ψ a)) G := by
    funext x
    simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, eval_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, eval_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := by
    classical
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : κ → ℤ, φ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = 0 := by
      intro n
      have hm : GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim ∈ Submodule.span ℝ
          (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := Submodule.subset_span ⟨n, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hQ : GlobalTheory.PowLinSpan.polOf φ X.dim = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset _
        (fun _ => (Finset.range (X.dim + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (GlobalTheory.PowLinSpan.degreeOf_polOf_le φ X.dim x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [GlobalTheory.PowLinSpan.eval_polOf]
        have he : (∑ x, C (v x) * MvPolynomial.X x : MvPolynomial κ ℝ) = GlobalTheory.ArInt.lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [GlobalTheory.ArInt.lin, Int.cast_natCast, hk]
        rw [he]
        exact hkill (fun i => (k i : ℤ))
    exact hφF (GlobalTheory.PowLinSpan.homog_kill φ X.dim hQ P hP)
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := GlobalTheory.T.exists_smoothWeight_integral_combination F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]

      simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add (f := _), hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumberStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly <;> assumption)
end
end
