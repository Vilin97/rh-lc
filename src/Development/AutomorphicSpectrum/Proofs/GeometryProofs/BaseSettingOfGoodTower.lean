module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTiedStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBoundStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreementStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StokesLimitIffPosOfResK
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModelsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimate
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImage

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SheetDecomposition.PF


theorem _root_.GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  intro II hII K _ ρ _ K' _ ρ' _ κ v P' d r G Jf L L' N hv hP' hP hJ hL hLL' hN
  have hA : IsArithVar P' (d + r + 1) := by rwa [Nat.add_right_comm] at hP'
  have hs : ∀ j, IsSmoothHerm (Fin.append L' N j) := fun j => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      exact GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hv (hLL' j) (hL j)
    · rw [Fin.append_right]
      exact hN j
  have h := GlobalTheory.T.projection_formula_of_arith_system ⟨II, hII⟩ II hII.1 K ρ K' ρ' κ v P' (d + 1) r G Jf
    (Fin.snoc (α := fun _ => HermLine ρ) L (cst ρ)) (Fin.snoc (α := fun _ => HermLine ρ') L' (cst ρ')) N hv hP' hP hJ
    (LevelTowerAlt.snoc_cst_smooth L hL)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.snoc_last]
        refine ⟨?_, fun z => rfl⟩
        show (0 : K' → ℤ) = pullDeg κ 0
        funext k
        by_cases hk : ∃ a, κ a = k
        · obtain ⟨a, rfl⟩ := hk
          exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
        · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm
      · simpa using hLL' j)
    hN
  rw [LevelTowerAlt.ii_cst_int hII.1 hP L hL, ← position_eq, ii_cast hII.1 _ hA _ (LevelTowerAlt.snoc_cst_smooth _ hs), LevelTowerAlt.ii_cst_int hII.1 hA _ hs,
    mul_neg, neg_inj] at h
  exact h
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImageStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | exact GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | (intros; apply GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionTower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem testPoly_eq_slX : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  intro hAg hPr hCmp hGiv hPts E _ _ _ _ H D Xo l c Y _ T o II hGl hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or hB hBB hqp hbg hsm hGood hgen hS
  have hIn : PB.Inputs := hGiv.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty (CMType H) := GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.cm_nonempty H
  have hUnif := GlobalTheory.T.good_tower_real_agreement hGiv E H D Xo l c Y T o II hGl hEx hII hp hq
  have hProp : T.Proportional :=
    GlobalTheory.T.real_tower_proportional hPr hIn II hII (CMType H) (D.p + D.q) T (Top.realOf o.toTowerOrigin) hUnif
  have hJpos : 0 < Top.testDeg (CMType H) (D.p + D.q) T.j :=
    (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) T.j T.j_pos T.j_lt).2.1
  have hLim : ArLimExists X.H X.S B :=
    (GlobalTheory.T.height_comparison_between_models hGiv hPts K J II (CMType H) Ω W Dc X.H X.M X.M X.S X.S B hII X.S_tied X.S_tied).1
  have hMass := (GlobalTheory.T.measure_limit_statement_holds II (CMType H) K J Ω W Dc O Lt X B hII.1 hLim).2
  have hSm := GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II (CMType H) Ω W Dc X.H X.M X.S B X.S_tied
  obtain ⟨K₃, _, ι₃, _, κ, v, P₃, e, r, cf, Mt, Nt, δ, hb, hY, himg, hδ, hdeg, hNs, hpull, hT, hGeo⟩ :=
    GlobalTheory.T.good_origin_intersection_relay hAg hPr hCmp hGiv hPts E H D Xo l c Y T o II hGl hEx hII hp hq B B₁ a K J Ω W Dc O Lt X Or hB hBB hqp hbg hsm hGood hgen hS
  have hXar : IsArithVar (imageZ v P₃) (Dc.n + 1) := by rw [himg]; exact Dc.arith
  obtain ⟨G⟩ := GlobalTheory.CompanionTheory.Ar.PB.Known.genFibreExists K J K₃ ι₃ κ v P₃ _ hb hY
  obtain ⟨Jf, hJf, -⟩ := (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers G.Φ (FibreBlock κ) (fibreIdx ι₃ κ)).1
  have hPF := GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩
  set fibN : Fin r → ℝ := fun m => (Jf (fibreIdeal κ G) e (fun i => fibreDeg κ (Nt 1 m i).a) : ℝ) with hfibN
  set fib : ℝ := ∑ m, cf m * fibN m with hfib
  have hEq1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m)) =
      fib * arLimFun X.H X.S B t := by
    filter_upwards [hSm, hpull] with t ht hp'
    rw [hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := hPF II hII.1 K J K₃ ι₃ κ v P₃ (Dc.n + 1) e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt t m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs t m)
    have hd : (fun i => fibreDeg κ (Nt t m i).a) = fun i => fibreDeg κ (Nt 1 m i).a := by
      funext i; rw [hdeg t m i]
    rw [h, himg, hd]
    simp only [arLimFun, hfibN]
    ring
  have hEq2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      fib * geomDeg (mCoordIdeal Dc.y) (muReg X.H X.S B t) Dc.n := by
    filter_upwards [hSm, hpull, hGeo] with t ht hp' hg
    rw [← hg, hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image II hII K J K₃ ι₃ κ v P₃ Dc.n e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt 1 m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs 1 m)
    rw [h, himg]
    simp only [geomDeg, hfibN]
    ring
  obtain ⟨L, hL⟩ := hLim
  have hA : arLim X.H X.S B = L := hL.limUnder_eq
  have h1 : δ * T.PPc II B a (Top.testPoly T.j) = fib * L :=
    tendsto_nhds_unique hT ((hL.const_mul fib).congr' (hEq1.mono fun t h => h.symm))
  have h2 : δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * degMu X.H :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hEq2) (hMass.const_mul fib)
  have h3 : (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := hProp.2.1 B a _
  rw [h3] at h2
  have hvol : 0 < T.vol a := hProp.1 a
  have hvJ : 0 < T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := mul_pos hvol hJpos
  have hpos : 0 < fib * degMu X.H := by rw [← h2]; exact mul_pos hδ hvJ
  have hd0 : 0 ≤ degMu X.H := GlobalTheory.CompanionTheory.StokesCompare.degMu_nonneg X
  have hdpos : 0 < degMu X.H := by
    refine lt_of_le_of_ne hd0 fun h => ?_
    rw [← h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hdpos, ⟨L, hL⟩, ?_⟩
  have hj : Dc.j = D.p := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · obtain ⟨τ⟩ := (inferInstance : Nonempty (CMType H))
      have := congrFun (hbg.symm.trans h) τ
      simp at this
  have hNn : Dc.N = D.p + D.q := Or.N_eq
  have hdim : ((Dc.n + 1 : ℕ) : ℝ) = (Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1 := by
    have hjT : T.j = D.p := o.j_eq
    have : Dc.n = Top.dimX (CMType H) (D.p + D.q) T.j := by
      simp only [ComponentData.n, Top.dimX, hj, hNn, hjT]
      ring
    rw [this]
    push_cast
    ring
  have hne : ((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) ≠ 0 := by positivity
  have hsl : slX X B = L / (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * degMu X.H) := by
    rw [slX, hA, hdim]
  rw [hsl]
  apply mul_left_cancel₀ hδ.ne'
  rw [h1]
  have hdn := hdpos.ne'
  field_simp
  linear_combination (-L) * h2

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionTowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.good_origin_intersection_tower : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX | exact GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.testPoly_eq_slX <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFinalEstimateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

theorem _root_.GlobalTheory.T.intersection_final_estimate : PB.Inputs → Prov.An → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Flat.GagaSections → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → ∀ [DecidableEq (CMType H)] (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt), X.H = Hd → (∀ z ∈ Dc.Xo, X.Cd.cuspWeight z = U z) → CuspBundlePos X → ∀ B : ℕ, 4 * Dc.f + 2 ≤ B → ArLimExists X.H X.S B → Top.StokesAt X B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | exact GlobalTheory.CompanionTheory.Relay.intersection_final_estimate | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_final_estimate <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularizationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  first | exact @GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | exact GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | (intros; apply GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopBase

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem base_setting_of_good_origin : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  intro Ch Cu hNine hWeil hAgr hProp hCmp hGiven hPts E _ _ _ _ H D Xo l c Y _ T o II hGlob hExtra hFull hp hq hqp
    hbad B hB a
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have := hne
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr hne
  have hN2 : 2 ≤ D.p + D.q := by omega
  have hsq : 4 ≤ (D.p + D.q) ^ 2 := by nlinarith
  have hB16 : 16 * Fintype.card (CMType H) ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by omega
  have hB4 : 4 * Fintype.card (CMType H) + 2 ≤ B := by omega
  have hgen : genPt (o.Or B a).𝔐.ξ₀ = genPt (o.Fx a).ξf :=
    genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset ℕ, ∀ r, r ∈ S₁ ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad :=
    ⟨(Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ∉ T.bad), by
      intro r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩⟩
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp => ((o.bad_iff p).1 hp).1
  have hS₁P : ∀ p ∈ S₁, p.Prime := fun p hp => ((hS₁ p).1 hp).1
  have hdisj : Disjoint S₁ T.bad := Finset.disjoint_left.2 fun p hp hp' => ((hS₁ p).1 hp).2.2 hp'
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ T.bad := fun p hp hd =>
    (o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have horigin :=
    GlobalTheory.T.full_intersection_generic_bound hGiven hWeil E H D Xo l c Y II hFull hGlob hp hq _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ T.bad S₁
      false hbadP hS₁P hdisj hdisc
  obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, hgen', hS, hj, hbg, -, hHT⟩ := horigin
  simp only [Bool.false_eq_true, ite_false] at hj hbg
  have hsm : Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨h, -, -⟩
    · exact h
    · exact absurd (congrFun (hbg.symm.trans h) hne.some) Sum.inl_ne_inr
  have hGood : Or.Good :=
    ⟨fun p hp => hHT p (Finset.mem_union_left _ hp),
      fun p hp => hHT p (Finset.mem_union_right _ (by rw [← hS]; exact hp))⟩
  have hSc : ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad := by
    intro r; rw [hS]; exact hS₁ r
  have hN : Dc.N = D.p + D.q := Or.N_eq
  have hAdm : admitted Xo l c Y Or B := by
    refine ⟨hGlob, hGood, o.bad_iff, ?_, ?_, hSc, ?_⟩
    · show T.bad.card ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2
      rw [hN]; exact hbad
    · exact hB4
    · show Dc.N - Dc.j ≤ Dc.j
      rw [hN, hj]; omega
  obtain ⟨U, M, S, S', hcw, hU0, hUt, hSt, hS't, hconj⟩ :=
    GlobalTheory.T.cusp_weight_regularisations_tied hGiven E H D Xo l c Y II K J Ω W Dc Hd T.bad Or
  obtain ⟨hpos, hht, hmean⟩ := hNine E H D Xo l c Y II K J Ω W Dc Hd T.bad Or B U M S' hFull hAdm hcw hS't
  obtain ⟨X, hXH, hXU, hXrd, hXL, hX1, hX2, hX3, hX4, hX5⟩ :=
    GlobalTheory.T.corrected_weight_regularization K J II (CMType H) Ω W Dc Hd M U S S' (hostRd E) (hostLval H) Ch Cu hSt hS't hU0 hUt hpos hconj
      hht hmean
  subst hXH
  obtain ⟨hdeg, hlim, hPP⟩ := GlobalTheory.T.good_origin_intersection_tower hAgr hProp hCmp hGiven hPts E H D Xo l c Y T o II hGlob hExtra hFull hp hq
    B B a K J Ω W Dc ℤ (Fin 2 → ℤ) X Or hB2 le_rfl hqp hbg hsm hGood (hgen'.trans hgen) hSc
  obtain ⟨-, -, hSemi, -, hResK, -, -, hGaga, -, hInputs, -, hAn, -, -⟩ := hGiven
  have hStk : Top.StokesAt X B :=
    GlobalTheory.T.intersection_final_estimate hInputs hAn hResK hGaga hSemi E H D Xo l c Y II K J Ω W Dc X.H T.bad Or B U hFull hAdm hcw ℤ
      (Fin 2 → ℤ) X rfl hXU hX1 B hB4 hlim
  exact ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, W, inferInstance, inferInstance, Dc, ℤ,
    Fin 2 → ℤ, inferInstance, inferInstance, inferInstance, X, hN, hj.trans o.j_eq.symm, hXrd, hXL, hX1, hX2, hX3, hX4,
    hX5, hdeg, hlim, hStk, hPP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopBase
end
end
