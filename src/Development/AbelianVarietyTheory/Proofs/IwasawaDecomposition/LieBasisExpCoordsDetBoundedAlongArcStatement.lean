module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSumStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Filter Topology

theorem tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim

theorem det_bounded_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPiStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  first | exact @GlobalTheory.det_bounded_eTwoPi | exact GlobalTheory.det_bounded_eTwoPi | (intros; apply GlobalTheory.det_bounded_eTwoPi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArc

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcLieFrame

theorem exists_const_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha
  have hG := GlobalTheory.SemiRigid.globalFns
  obtain ⟨g', e, v, -, hev, hb, hu, -⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c V V.subtype Y ℂ
    (σ.comp V.subtype) a χ W
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.ExpTan.anVec_bijective hG E H Dw l Xo c σ V V.subtype Y a χ W g ty Fu Ha
  choose z hz using fun i => (h1 (e i) (hev i).1).exists
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf
    obtain ⟨ν, hν⟩ := GlobalTheory.ConstLie.exists_gtComb cf e
    obtain ⟨ν₀, hν₀⟩ := GlobalTheory.ConstLie.exists_gtComb (0 : Fin g' → ℂ) e
    have a1 := (h4 g' cf e z ν hz).1 hν
    have a0 := (h4 g' 0 e z ν₀ hz).1 hν₀
    rw [hcf] at a1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at a0
    obtain rfl : ν = ν₀ := (h2 0).unique a1 a0
    have ht := h3 _ _ a1
    have := (hu ν ht).unique hν hν₀
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range z) := by
    intro z₀ _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨ν, hν, -⟩ := h2 z₀
    obtain ⟨cf, hcf, -⟩ := hu ν (h3 _ _ hν)
    exact ⟨cf, (h1 ν (h3 _ _ hν)).unique ((h4 g' cf e z ν hz).1 hcf) hν⟩
  have hg : g' = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    simpa using this.symm
  subst hg
  refine ⟨e, v, z, fun k => ⟨(hev k).2, hz k⟩, hb, ?_⟩
  have hu' : IsUnit (Matrix.of z) := (Matrix.linearIndependent_rows_iff_isUnit).1 (by simpa using hli)
  exact (Matrix.isUnit_iff_isUnit_det _).1 hu' |>.ne_zero

end GlobalTheory.ArcLieFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArcStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  first | exact @GlobalTheory.ArcLieFrame.exists_const_frame | exact GlobalTheory.ArcLieFrame.exists_const_frame | (intros; apply GlobalTheory.ArcLieFrame.exists_const_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArc

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chartLie_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U), ∃ v' : Fin M.n → (epsR (PowerSeries ℂ) ⟶ W.t.G), (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ i) ∧ IsLieBasis v' := by
  intro E _ _ _ H Dw l Xo c σ V Y a χ W M hM
  have cast : ∀ (p q : Sp (PowerSeries ℂ) ⟶ Y.X) (_ : p = q) (n : SABMap W.t Y.t p),
      ∃ n' : SABMap W.t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ (spMap (ev χ M.U hM) ≫ M.hU.fromSpec) (GlobalTheory.FlagMod.spMap_ev χ M.hU hM).symm W.m
  obtain ⟨v', hv', hb, -⟩ := M.lie (PowerSeries ℂ) (ev χ M.U hM) W.t m'
  refine ⟨v', fun j => ?_, hb⟩
  rw [← hm', hv' j]
  have e : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev χ M.U hM) = dualMap (ev χ M.U hM) := by
    ext x <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, dualMap]
  rw [e]

theorem exists_lieComb_matrix : ∀ (R : Type) [CommRing R] [Nontrivial R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n n' : ℕ) (v : Fin n → (epsR R ⟶ G)) (v' : Fin n' → (epsR R ⟶ G)), IsLieBasis v → IsLieBasis v' → ∃ h : n' = n, ∃ A : Matrix (Fin n) (Fin n) R, IsUnit A.det ∧ ∀ i, IsLieComb (A i) v (v' (Fin.cast h.symm i)) := by
  intro R _ _ G _ _ O _ act n n' v v' hv hv'
  let b := GlobalTheory.Serre.Lie.basis act hv
  let b' := GlobalTheory.Serre.Lie.basis act hv'
  have h : n' = n := by simpa using Fintype.card_congr (b'.indexEquiv b)
  subst h
  refine ⟨rfl, (b.toMatrix b').transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose]
    refine IsUnit.of_mul_eq_one (b'.toMatrix b).det ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · have hv_eq : v = fun k => (b k).hom := funext fun k => (GlobalTheory.Serre.Lie.hom_basis (a := act) hv k).symm
    rw [Fin.cast_eq_self, ← GlobalTheory.Serre.Lie.hom_basis (a := act) hv' i, hv_eq, GlobalTheory.Serre.Lie.isLieComb_iff]
    congr 1
    conv_lhs => rw [← b.sum_repr (b' i)]
    rfl

theorem lieCoord_det_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M h1 h2 h3 h4 h5 h6
  obtain ⟨e, v, z, hev, hv, hz⟩ := GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc E H Dw l Xo c σ V Y a χ W g ty Fu Ha
  obtain ⟨v', hv'1, hv'2⟩ := exists_chartLie_along E H Dw l Xo c σ V Y a χ W M h6
  obtain ⟨hn, A, hA, hAc⟩ := exists_lieComb_matrix (PowerSeries ℂ) W.t.G (𝓞 E) W.t.act g M.n v v' hv hv'2
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum E H Dw l Xo c σ V Y a χ W g ty Fu Ha M h6 e v z hn (fun i => v' (Fin.cast hn.symm i)) A
    h1 h2 h3 h4 h5 hev hv hz (fun i => hv'1 _) hAc
  by_cases hex : ∃ w : ℂ, T₀ < w.im ∧ ∀ i k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)
  swap
  · refine ⟨T₀, 1, one_pos, ?_⟩
    intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
    exact (hex ⟨w, hw, fun i k => (hT₀ w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf i).1 k⟩).elim
  obtain ⟨w₀, -, hs⟩ := hex
  obtain ⟨T', C, hC, hb⟩ := GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi g A w₀ hA hs
  have hd : 0 < ‖(Matrix.of z).det‖ := norm_pos_iff.2 hz
  refine ⟨max T₀ T', C * (‖(Matrix.of z).det‖ + ‖(Matrix.of z).det‖⁻¹), by positivity, ?_⟩
  intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
  have hM : (Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j) =
      (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m) * Matrix.of z := by
    ext i j
    rw [Matrix.of_apply, ((hT₀ w (lt_of_le_of_lt (le_max_left _ _) hw) yF e1 e2 hz' x φ hk hg u Wv hf hdf i).2 j),
      Matrix.mul_apply]
    rfl
  rw [hM, Matrix.det_mul, norm_mul]
  obtain ⟨b1, b2⟩ := hb w (lt_of_le_of_lt (le_max_right _ _) hw)
  set d := ‖(Matrix.of z).det‖
  set t := ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖
  constructor
  · rw [mul_inv, ← div_eq_mul_inv]
    calc C⁻¹ / (d + d⁻¹) ≤ C⁻¹ * d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ d * (d + d⁻¹) := by rw [mul_add, mul_inv_cancel₀ hd.ne']; nlinarith
          nlinarith [inv_pos.2 hC]
      _ ≤ t * d := mul_le_mul_of_nonneg_right b1 hd.le
  · calc t * d ≤ C * d := mul_le_mul_of_nonneg_right b2 hd.le
      _ ≤ C * (d + d⁻¹) := by nlinarith [inv_pos.2 hd]

end GlobalTheory.ArcNormal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArcStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.lieBasis_expCoords_det_bounded_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.lieCoord_det_bounded | exact GlobalTheory.ArcNormal.lieCoord_det_bounded | (intros; apply GlobalTheory.ArcNormal.lieCoord_det_bounded <;> assumption)
end
end
