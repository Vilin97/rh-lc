module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRealPolyEqOfDbarCohomologous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGraded

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGradedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  first | exact @GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF | exact GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF | (intros; apply GlobalTheory.ChernCalc.chernFld_ldPart_eq_esymm_grF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRealPolyEqOfDbarCohomologousStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  first | exact @GlobalTheory.ChernCalc.integral_evalF_of_dbarCoh | exact GlobalTheory.ChernCalc.integral_evalF_of_dbarCoh | (intros; apply GlobalTheory.ChernCalc.integral_evalF_of_dbarCoh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairGramLowerTriangularFactor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem ratVal_zero_var {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem isGramPair_ldPart (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H) (τ : ι) :
    IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  have hA : ∀ y : CxPts X.str σ, (E.nonempty (under y)).choose ∈ E.S (under y) :=
    fun y => (E.nonempty (under y)).choose_spec
  have hsm := fun y => GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH y _ (hA y) τ
  have hT : ∀ (A B : Mat m X.Fn) (w : CxPts X.str σ), A ∈ E.S (under w) → B ∈ E.S (under w) →
      HolUnitAt (atlas X σ) (fun z => ((B * A⁻¹) τ).map (ratVal · z)) w ∧
      ∀ i j : Fin (m τ), i < j → ((B * A⁻¹) τ).map (ratVal · w) i j = 0 := by
    intro A B w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) τ
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) ((B * A⁻¹) τ) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero_var w
  refine ⟨fun y => ⟨(hsm y).1, ?_⟩, fun y => ?_⟩
  · refine ⟨(GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (hH.posDef y _ (hA y) τ)).2.2.2, fun c hc => ?_⟩
    filter_upwards [(hsm y).2 c hc] with v hv
    exact (GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).1
  · have h1 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ (hA y)
    filter_upwards [h1, h1.eventually_nhds] with z hz hz'
    have h2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ (hA z)
    obtain ⟨hol, tri⟩ := hT _ _ z hz (hA z)
    refine ⟨_, _, fun w => Matrix.diagonal fun i =>
      (((E.nonempty (under z)).choose * (E.nonempty (under y)).choose⁻¹) τ).map (ratVal · w) i i,
      hol, hol, ⟨?_, fun c hc a b => ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, ← Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)]
      exact hol.1
    · by_cases hab : a = b
      · subst hab
        filter_upwards [hol.2 c hc a a] with v hv
        simpa only [Matrix.diagonal_apply_eq] using hv
      · exact Eventually.of_forall fun v => by
          simp only [Matrix.diagonal_apply_ne _ hab]
          exact differentiableAt_const _
    · filter_upwards [hz', h2] with w hwA hwB
      obtain ⟨holw, triw⟩ := hT _ _ w hwA hwB
      have e := hH.trans w _ hwA _ hwB τ
      change gramAt E H τ z w = _ * gramAt E H τ y w * _ at e
      refine ⟨e, ?_⟩
      rw [e]
      exact (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (hH.posDef w _ hwA τ) triw holw.1).1

end GlobalTheory.ChernCalc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairGramLowerTriangularFactorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  first | exact @GlobalTheory.ChernCalc.isGramPair_ldPart | exact GlobalTheory.ChernCalc.isGramPair_ldPart | (intros; apply GlobalTheory.ChernCalc.isGramPair_ldPart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlag

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem evalF_rename_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : Type}
    (u : α → A.Pt → Ev n) (v : β → A.Pt → Ev n) (R : MvPolynomial α ℝ) (Q : MvPolynomial β ℝ) :
    evalF A (Sum.elim u v) (rename Sum.inl R * rename Sum.inr Q) = evalF A u R * evalF A v Q := by
  funext x
  simp only [evalF, LineForm.fld, Pi.mul_apply, Polynomial.map_mul, MvPolynomial.map_rename, map_mul, aeval_rename]
  rfl

theorem evalF_chernRoots {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (m : ι → ℕ)
    (c : ι × ℕ → A.Pt → Ev n) (g : Root m → A.Pt → Ev n)
    (h : ∀ τ j p, c (τ, j) p = aeval (fun i => g ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j))
    (R : MvPolynomial (ι × ℕ) ℝ) : evalF A c R = evalF A g (chernRoots m R) := by
  funext p
  simp only [evalF, LineForm.fld]
  congr 1
  rw [aeval_map_algebraMap, aeval_map_algebraMap, chernRoots, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext x
  rw [h x.1 x.2 p, aeval_rename, aeval_esymm_eq_multiset_esymm, aeval_esymm_eq_multiset_esymm]
  rfl

theorem integral_chernF_mul_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  intro F _ σ X ι _ m E H hH R Q
  let ld : ι × ℕ → (atlas X σ).Pt → Ev X.dim := fun x => chernFld (atlas X σ) (fun y z => ldPart (gramAt E H x.1 y z)) x.2
  have hc : ∀ i, DbarCoh (atlas X σ) (Sum.elim (chernF E H) (grF E H) i) (Sum.elim ld (grF E H) i) := by
    rintro (⟨τ, j⟩ | x)
    · exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor F σ X ι m E H hH τ) j
    · exact GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ X ι m E H hH x
  have key := GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous (CxPts X.str σ) X.dim (atlas X σ) _ _ _ hc (rename Sum.inl R * rename Sum.inr Q)
  rw [evalF_rename_mul, evalF_rename_mul] at key
  rw [key, evalF_chernRoots (atlas X σ) m ld (grF E H) (fun τ j p => GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded F σ X ι m E H hH τ j p) R]
  simp only [evalF, LineForm.fld, map_mul]
  rfl

end GlobalTheory.ChernCalc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlagStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  first | exact @GlobalTheory.ChernCalc.integral_chernF_mul_grF | exact GlobalTheory.ChernCalc.integral_chernF_mul_grF | (intros; apply GlobalTheory.ChernCalc.integral_chernF_mul_grF <;> assumption)
end
end
