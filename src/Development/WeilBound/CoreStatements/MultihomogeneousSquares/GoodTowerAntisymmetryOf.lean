module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdegStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGivenStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverDegreeOneRealisationStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullbackStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven
public import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibilityStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExistsStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_model_analytic_data_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | exact GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundary

section

@[expose] public section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ConjOf

theorem flagAn_exists_conj : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) :=
  fun hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM hA hd h1 h2 =>
    flagAn_conj K ι Φ y Ψ N j M n d BM (GlobalTheory.T.flag_model_analytic_data_exists hI K ι Φ y Ψ N j M n d BM hA hd) h1 h2

end GlobalTheory.CompanionTheory.Ar.PB.ConjOf
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundaryStatement

section

@[expose] public section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flagModel_arith_dimension_boundary : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj | exact GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ConjOf.flagAn_exists_conj <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGivenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.flag_model_exists_of_given : Given → PB.FlagModelExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.ChooseTwoAdd

section

@[expose] public section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights (antisymDegree)

theorem choose_two_add (j m : ℕ) : (j + m).choose 2 = j * m + j.choose 2 + m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ' m 1,
      Nat.choose_one_right]
    ring

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω)
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem genPt_of_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'} {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X}
    {i : Ω →+* Ω'} {j : A.Li →+ A'.Li} (a : PB.HodgeOver A' A h i j) :
    GlobalTheory.CompanionTheory.Ar.genPt A'.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt A.ξ₀ := by
  have e₁ : A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom A'.fn) ≫ A'.ξ₀ := A'.fn_over
  have e₂ : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
  have e₃ : A'.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := a.1
  rw [← genPt_comp A'.fn, ← e₁, a.2.1, ← Category.assoc, e₃, Category.assoc, e₂, genPt_comp, genPt_comp]

theorem PB_eq_of_lines {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {σ : Type} [Fintype σ] {S : PB.AnSys e σ} (Re Re' : PB.Realis S P) (hd : Re.deg = Re'.deg)
    (hl : ∀ a t, Re.line a t = Re'.line a t) (II : IntersectionSystem) : Re.PB II = Re'.PB II := by
  have : ∀ t w, Re.num II t w = Re'.num II t w := fun t w => by
    simp only [PB.Realis.num, hd, hl]
  refine congrArg (PB.formPoly (e + 1)) (funext fun w => ?_)
  simp only [PB.Realis.limNum, this]

theorem tie_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) : StTie := by
  intro hG hW E _ _ _ H D l Xo c Y _ S Ω₀ _ ξ₀ hξ₀ hSp hSd hp hq
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨Ω, _, _, K₀, _, J₀, _, x₀, 𝔐, dg, ⟨k₀⟩, hgen, hcov, harith, hsnc, hR, hom⟩ :=
    hBase hRes hW E H D l Xo c Y S Ω₀ ξ₀ hξ₀ hSp hSd
  rw [← PB.card_mul_eq_dim D] at harith hsnc
  obtain ⟨⟨bW⟩, ⟨bO⟩⟩ := PB.nonempty_bases 𝔐
  obtain ⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, κ, v, φ, π, j, 𝔐', Fl, xdeg, e, ⟨-, -, -, -, hov, hR₁, -⟩,
    ⟨hcov₁, -, hsnc₁⟩, hv, htot, hFl⟩ := GlobalTheory.T.flag_model_exists_of_given hG E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 _ dg bW bO harith hcov
  obtain ⟨BM, hBM, hcj⟩ := GlobalTheory.T.base_metric_exists_of_given hG E H D l Xo c Y S K ι Φ y M 𝔐₁ tie dg hp hq hcov₁ (hsnc₁ _ hsnc)
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have hcard : 0 < Fintype.card (CMType H) := Fintype.card_pos_iff.2 hne
  have hN : antisymDegree (CMType H) (D.p + D.q) = Fintype.card (CMType H) * D.p * D.q +
      Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) := by
    show Fintype.card (CMType H) * (D.p + D.q).choose 2 = _
    rw [choose_two_add]; ring
  have hdim : dimFl (CMType H) (D.p + D.q) = antisymDegree (CMType H) (D.p + D.q) := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = antisymDegree (CMType H) (D.p + D.q) := by
    refine ⟨antisymDegree (CMType H) (D.p + D.q) - 1, Nat.sub_add_cancel ?_⟩
    rw [hN]
    have := Nat.mul_pos (Nat.mul_pos hcard hp) hq
    omega
  have hv' : IsArithVar (mCoordIdeal y) (d + 2) := by
    rw [show d + 2 = (d + 1) + 1 from rfl, hd, hN]; exact hv
  have hsub : D.p + D.q - D.p = D.q := by omega
  obtain ⟨FA, hFAc⟩ := GlobalTheory.T.flagModel_arith_dimension_boundary hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM hv' (by rw [hsub, hd, hN])
    hcj.1 hcj.2
  have hU := GlobalTheory.T.flag_analytic_data_uniformised K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA (by rw [hsub]) hd
  obtain ⟨Cv, CR, hCv, -, hCRl⟩ := GlobalTheory.T.flag_cover_degree_one_realisation K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA
  have FS : Nonempty (PB.FlagSys CR.Re D.p) := ⟨⟨M.j_le, hd, hU, fun τ a b hab hb =>
    (GlobalTheory.T.flag_cover_realisation_pullback hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA K ι Φ y M Cv CR hv' τ a b hab hb).some⟩⟩
  obtain ⟨⟨pr, j', hov', hR', -⟩, hroots, hdy, -⟩ := id htot
  choose sing hsd hho hsc using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl xdeg e hβ hroots
  have hrd : ∀ a, ((FA.Re.comap some).ref a).a = (Top.combLine sing (Cmp.fundOnRoot a)).a := fun a => by
    show (FA.Re.ref (some a)).a = ∑ r, _ • (sing r).a
    rw [FA.ref_some, RootFieldNumerics.Sq.sum_fundOnRoot]
    simp only [hsd]
    exact hdy a.1 a.2
  have hse : ∀ a x, (FA.Re.comap some).π x ∉ ReciprocityTheory.AnForm.P.bdry (FA.S.comap some).s →
      Real.log ((Top.combLine sing (Cmp.fundOnRoot a)).h ((FA.Re.comap some).R.lift x x)) =
        Real.log (((FA.Re.comap some).ref a).h ((FA.Re.comap some).R.lift x x)) +
          (FA.S.comap some).ph a ((FA.Re.comap some).π x) := fun a x hx => by
    have hx' : FA.Re.π x ∈ FA.S.open' := hx
    refine Eq.trans ?_ (FA.hom_eq a x hx')
    refine hSing E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ BM 𝔐' Fl xdeg e sing hBM htot hsd hho a _
      (FA.Re.R.mem x x (FA.Re.R.mem_U x)) (FA.pr (FA.Re.π x)) (fun h => hx' ?_) (FA.pr_eq x)
    show FA.S.s _ _ = 0
    rw [FA.s_eq]
    exact h
  have halg := hAlg E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ d BM FA hBM
  obtain ⟨x, hxa, hxs, hxc, hxl⟩ := hX _ _ K ι _ _ (FA.S.comap some) (FA.Re.comap some) sing (FA.S.reg none).1 hrd
    fun a t => hFAc (some a) t
  have hF : 0 < Module.finrank ℚ c.F := by haveI := c.fin; exact Module.finrank_pos
  have hFlpos : 0 < Fl.deg := by rw [hFl]; exact hcov.1
  have hKne : Nonempty K := ⟨(κ k₀).1⟩
  obtain ⟨hbir, -⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl hβ
  have hovT := hov'.trans hov
  have hht := hHt E H D l Xo c Y S Ω Φ K₀ K J₀ ι x₀ y 𝔐 𝔐' _ _ _ hovT (hR'.trans hR₁) hSd fun p hp => (hom p hp).2
  let M' : RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := ι, Ω := Φ, y := y, arith := by rw [hdim, hN]; exact hv, birational := hbir, xdeg := xdeg, x := x,
      x_deg := fun t r => (hxa t r).trans (hsd r), x_smooth := hxs, x_conj := hxc, kA := 1, kA_pos := one_pos,
      A := trivLine ι, A_smooth := contDiffOn_const, A_conj := fun _ => rfl,
      δ := Module.finrank ℚ c.F * Fl.deg, δ_pos := Nat.mul_pos hF hFlpos }
  have key : ∀ (D' : ℕ) (_ : d + 1 = D'), ∃ (Sy' : PB.AnSys D' (CMType H × Fin (D.p + D.q)))
      (Re' : PB.Realis Sy' (mCoordIdeal y)), (FA.S.comap some).degPoly = Sy'.degPoly ∧
      (∀ II, CR.Re.PB II = Re'.PB II) ∧ Cmp.AlgOver Re' ∧ Re'.deg = 1 ∧
      (∀ r, (Re'.ref r).a = (Top.combLine sing (Cmp.fundOnRoot r)).a) ∧
      (∀ r x, Re'.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy'.s → Real.log ((Top.combLine sing (Cmp.fundOnRoot r)).h
        (Re'.R.lift x x)) = Real.log ((Re'.ref r).h (Re'.R.lift x x)) + Sy'.ph r (Re'.π x)) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts (mCoordIdeal y),
        (x t r).h z = (Top.combLine (fun a => Re'.line a t) (Cmp.rootOnFund r)).h z := by
    intro D' h
    subst h
    exact ⟨_, FA.Re.comap some, rfl, PB_eq_of_lines _ _ ((CR.deg_eq.trans hCv).trans FA.deg_one.symm) hCRl, halg,
      FA.deg_one, hrd, hse, hxl⟩
  obtain ⟨Sy', Re', e1, e2, halg', hRd', hrd', hse', hxl'⟩ := key _ (hd.trans hdim.symm)
  let t : Cmp.HodgeTie Y S (Module.finrank ℚ c.F) M' :=
    { A := 𝔐', Fl := Fl, e := e, roots := hroots, sing := sing, sing_deg := hsd, hodge := hho,
      Sy := Sy', Re := Re', alg := halg', ref_deg := by convert hrd', sing_eq := by convert hse',
      line_eq := by
        classical
        have hi : (inferInstance : DecidableEq (CMType H)) =
            (fun a b => Subtype.instDecidableEq a b) := Subsingleton.elim _ _
        have hr : @Cmp.rootOnFund (CMType H) (inferInstance : DecidableEq (CMType H)) (D.p + D.q) =
            @Cmp.rootOnFund (CMType H) (fun a b => Subtype.instDecidableEq a b) (D.p + D.q) := by rw [hi]
        rw [hr] at hxl'
        exact hxl',
      δ_eq := rfl, discr := hSd, ht_vb := hht }
  exact ⟨M', t, d, _, K, _, ι, _, _, CR.Re, (genPt_of_over hovT).trans hgen,
    fun p hp => by rw [← hR p hp, ← hR₁, ← hR'], hRd', hFlpos, e1, FS, e2⟩

end SquareStatements
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.SqOf

section

@[expose] public section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem sq_of (hT : StTie) (hCmp : StCmp) : StSq := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hX hII hp hq B a
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := TowerPropA.mono_spMap_ringOfIntegers c.F
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.toTowerOrigin.S B := by
    intro p hp hdv
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hdv 2) _
  obtain ⟨M', t, d, S, K, _, ι, _, P, Re, hgen, hR, hdeg, hpos, hS, hF, hPB⟩ :=
    hT hG hW E H D l (Xo l) c Y (o.S B) _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ (o.Or B a).𝔐.S_prime hdisc hp hq
  obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.root_model_origin_compatibility E H D l (Xo l) c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx hmono (hX.1 a)
  obtain ⟨f₁, f₂⟩ := hCmp hIn hC II hII E H D l (Xo l) c _ _ Y _ _ _ _ t
    (RootFieldNumerics.Sq.tieOf (o.Or B a) ((o.Sys a).reg none).1 (o.omVB B a) t.discr hA) hmono hgen
    (fun p hp => (hX.2 B a p hp).trans (hR p hp).symm) hdeg (o.Or B a).Re_deg
  refine ⟨t.Fl.deg, d, S, K, _, ι, _, P, Re, Nat.cast_pos.2 hpos, by rw [o.j_eq]; exact hF, ?_, hS.trans f₂⟩
  rw [hPB II, f₁, map_smul]
  rfl

end SquareStatements
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetryOf

section

@[expose] public section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

def GoodTowerAntisymmetry : Prop :=
  Cmp.CmpSt → Given → Out.WeilSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)]
    (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem),
    o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II)

theorem good_tower_antisymmetry_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) (hCmp : StCmp)
    (hI8 : AntisymmetryFibreSquares) : GoodTowerAntisymmetry := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hE hII hp hq
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  exact hI8 GlobalTheory.T.antisymmetry' GlobalTheory.T.agreement_positive hG.2.2.2.2.2.2.2.2.2.1 II hII _ _ T _
    (sq_of (tie_of hX hAlg hHt hSing hBase) hCmp hC hG hW E H D Xo l c Y T o II hE hII hp hq)

end SquareStatements
end
end
end
