module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutationStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2Statement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibilityStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoEpsT
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoArFun

section

@[expose] public section

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top SheetDecomposition

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem herm_ext {A B : HermLine J} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem comb_some {σ : Type} [Fintype σ] (c₀ : HermLine J) (l : σ → HermLine J) (n : σ → ℤ) :
    combLine (fun o : Option σ => o.elim c₀ l) (fun o => o.elim 0 n) = combLine l n :=
  herm_ext (by simp [combLine, Fintype.sum_option]) (by funext z; simp [combLine, Fintype.prod_option])

theorem comb_none {σ : Type} [Fintype σ] (c₀ : HermLine J) (l : σ → HermLine J) :
    combLine (fun o : Option σ => o.elim c₀ l) (fun o => o.elim 1 0) = c₀ :=
  herm_ext (by simp [combLine, Fintype.sum_option]) (by funext z; simp [combLine, Fintype.prod_option])

theorem pts_deg (hI : PB.Inputs) {P : Ideal (MRing J)} {e : ℕ} (hP : IsArithVar P (e + 1)) {L L' : Fin e → HermLine J}
    (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j)) (h : ∀ j, (L j).a = (L' j).a) :
    ptsIntegral (e := e) P (fun i z => Real.log ((L i).h z)) (fun _ => 1) =
      ptsIntegral (e := e) P (fun i z => Real.log ((L' i).h z)) (fun _ => 1) := by
  have h1 := hI.degree K J P e L 2 hP hL Nat.prime_two
  have h2 := hI.degree K J P e L' 2 hP hL' Nat.prime_two
  simp only [h] at h1
  exact h1.trans h2.symm

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def gapc (c : Ψ × Fin N → ℤ) (r : Ψ × Fin N) : ℤ := (if h : (r.2 : ℕ) + 1 < N then c (r.1, ⟨r.2 + 1, h⟩) else 0) - c r

theorem sum_gapc {A : Type} [AddCommGroup A] (c : Ψ × Fin N → ℤ) (x : Ψ × Fin N → A) :
    ∑ r, gapc c r • -∑ k ∈ Finset.Iic r.2, x (r.1, k) = ∑ r, c r • x r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  let c' : ℕ → ℤ := fun i => if h : i < N then c (τ, ⟨i, h⟩) else 0
  have h1 : ∀ i : Fin N, gapc c (τ, i) = c' (i + 1) - c' i := fun i => by simp [gapc, c']
  have h2 : ∀ k : Fin N, ∑ i : Fin N, (if k ≤ i then gapc c (τ, i) else 0) = -c (τ, k) := fun k => by
    have h3 := Finset.sum_Ico_sub c' k.2.le
    have h4 : ∑ i : Fin N, (if k ≤ i then gapc c (τ, i) else 0) =
        ∑ i ∈ Finset.range N, if (k : ℕ) ≤ i then c' (i + 1) - c' i else 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => if (k : ℕ) ≤ i then c' (i + 1) - c' i else 0)]
      simp only [h1, Fin.le_def]
    rw [h4, ← Finset.sum_filter, show (Finset.range N).filter (fun i => (k : ℕ) ≤ i) = Finset.Ico (k : ℕ) N by
      ext i; simp [and_comm], h3]
    simp [c']
  calc ∑ i, gapc c (τ, i) • -∑ k ∈ Finset.Iic i, x (τ, k)
      = ∑ i, ∑ k, -((if k ≤ i then gapc c (τ, i) else 0) • x (τ, k)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_neg, Finset.smul_sum, Finset.sum_neg_distrib, show Finset.Iic i = Finset.univ.filter (· ≤ i) by ext; simp,
          Finset.sum_filter]
        simp only [ite_smul, zero_smul]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_neg_distrib, ← Finset.sum_smul, h2, neg_smul, neg_neg]

variable (M : RootModel Ψ N) {II : IntersectionSystem}

theorem line_smooth (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j
  exacts [M.A_smooth, M.x_smooth _ _]

theorem arFun_word (hII : IsFullIntersectionSystem II) (t : ℝ) (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    M.arFun II t (toA (∏ j, X (w j))) * M.δ = II M.K M.ι M.P (dimFl Ψ N + 1) fun j => M.x t (w j) := by
  classical
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  obtain ⟨h2, -, -, h4⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 M.K M.ι M.P _ _ (M.line t) (fun j => some (w j)) M.arith (line_smooth M t)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.arFun, Module.Basis.constr_basis, RootModel.arMono, if_pos h2, h3, pow_zero, mul_one,
    div_mul_cancel₀ _ hδ, h4]
  rfl

theorem arFun_prod (hII : IsFullIntersectionSystem II) (t : ℝ) {d : ℕ} (hd : d = dimFl Ψ N + 1) (c : Fin d → Ψ × Fin N → ℤ) :
    M.arFun II t (toA (∏ j, ∑ x, c j x • X x)) * M.δ = II M.K M.ι M.P d fun j => combLine (M.x t) (c j) := by
  classical
  subst hd
  rw [GlobalTheory.T.arith_intersection_multilinear_all II hII M.K M.ι M.P _ _ (M.x t) c M.arith (M.x_smooth t), Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _

  rw [h2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, smul_eq_mul, mul_assoc, arFun_word M hII, Int.cast_prod]

theorem geoFun_pts (hI : PB.Inputs) (t : ℝ) {d : ℕ} (hd : d = dimFl Ψ N) (c : Fin d → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      ptsIntegral (e := d) M.P (fun j z => Real.log ((combLine (M.x t) (c j)).h z)) fun _ => 1 := by
  classical
  subst hd
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P _ (fun j => combLine (M.x t) (c j)) M.arith
    fun j => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ _).1 (M.x_smooth t)
  refine (geoFun_prod M hI c).trans (Eq.trans ?_ h.symm)
  simp only [combLine, M.x_deg]

theorem tendsto_arFun (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have e : (monomial m a : RPA Ψ N) = a • basisMonomials (Option (Ψ × Fin N)) ℝ m := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    obtain ⟨L, hL⟩ := h m
    simp only [e, map_smul, RootModel.arFun, RootModel.PP, Module.Basis.constr_basis, hL.limUnder_eq]
    exact hL.const_smul a
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add hq

theorem test_factor' [DecidableEq Ψ] {p q n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (testPoly p : RP Ψ (p + q)) =
      ∏ j : Fin (n + 1 + r), ∑ x, Fin.append (fun _ : Fin (n + 1) => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have h := test_factor e hq hn
  rw [Fin.prod_univ_add] at h ⊢
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h ⊢
  rw [testPoly, pow_succ', mul_assoc, h, pow_succ', mul_assoc, sum_muCoef, muSmall, if_pos (by omega)]

end LevelTowerAlt.Comparison₂
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullCst

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem pull_cst' {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
    [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → Σ k, J' k} (hv : IsBlockMap κ v) :
    IsPullHerm κ v (PF.cst J) (PF.cst J') := by
  refine ⟨?_, fun z => rfl⟩
  show (0 : K' → ℤ) = pullDeg κ 0
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
  · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm

theorem root_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N n : ℕ} {M : Top.RootModel Ψ N}
    {S : PB.AnSys (Top.dimFl Ψ N) (Option (Ψ × Fin N))} (R : Top.RealTie M S n) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀)
    (c : Option (Ψ × Fin N) → ℤ) :
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).a =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).a ∧ ∀ z ∈ mcPts M.P,
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).h z =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).h z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simp only [Top.combLine, Fintype.sum_option, Option.elim, R.Re.line_deg, M.x_deg]
    congr 1
    refine (sum_gapc (c ∘ some) M.xdeg).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_deg]
  · refine Real.log_injOn_pos (HermLine.pos _ _ hz.1) (HermLine.pos _ _ hz.1) ?_
    rw [log_comb _ _ hz.1, log_comb _ _ hz.1]
    simp only [Fintype.sum_option, Option.elim, ← zsmul_eq_mul]
    congr 1
    refine (sum_gapc (c ∘ some) fun r => Real.log ((M.x t r).h z)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_reg r.1 r.2 t h0 h1 z hz]


theorem tie_of (hC : Common) (hR : Replace) (hB : BaseSide) : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  intro hAg _ _ hG _ E _ _ _ _ H D Xo l c Y _ T o II _ hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or _ hBB hqp
    hbg hsm hGood hgen hS
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hK : ResK.ResKStatement := hG.2.2.2.2.1
  have hSeq : o.S B = T.bad ∪ Dc.SB B := by
    ext r
    rw [o.S_iff, Top.RootTower.InS, Finset.mem_union, ComponentData.SB, Finset.mem_filter, hS]
    have := (o.bad_iff r).1
    by_cases h : r ∈ T.bad
    · simp [h, (this h).1]
    · simp only [h, or_false, false_or, not_false_eq_true, and_true]
      exact ⟨fun h => ⟨⟨h.1, h.2.trans hBB⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ₂, v₂, Ω₃, _, _, y, β, b, hb₁, hb₂, he₁, he₂, har, hβ, hβn, hrk, hbd, hiso⟩ :=
    hC hG E H D Xo l c Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) II K J Ω W Dc X.H T.bad Or B hSeq
      (fun p hp hd => (o.bad_iff p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩) (o.omVB B a) (hEx.2 B a) hp hbg hsm hGood hgen
  have hmono := OrLinked.mono_int' c
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.hodge_component_factor_point E H D l _ c _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hmono
  have alg := GlobalTheory.T.root_model_origin_compatibility E H D l _ c _ _ Y _ _ _ _ (o.Or B a) (spMap (o.Or B a).𝔐.fn ≫ x₀) (by
    rw [Category.assoc, ← hx₀]; exact (o.Or B a).𝔐.fn_over) hmono (hEx.1 a)
  have : Nonempty (RootIx D) := ⟨(Classical.choice (GlobalTheory.T.cm_host_rank_bounds E H).2.1, ⟨0, by omega⟩)⟩
  obtain ⟨K', _, ρ', _, κ, v, y', hb, hy, hfield, har', hcore⟩ := anCore hR hB hI hK hII ((o.Or B a).Re.comap some) alg
    (gapc (muExp D.p)) (Top.combLine (o.Or B a).sing (muExp D.p)) (by
      simp only [Top.combLine, (o.Or B a).sing_deg]
      refine (sum_gapc _ _).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      rw [← (o.Or B a).fund_deg]
      rfl) (fun x hx => by
      refine (log_comb _ _ ((o.Or B a).Re.R.mem x x ((o.Or B a).Re.R.mem_U x)).1).trans ?_
      simp only [← zsmul_eq_mul]
      refine (sum_gapc _ fun r => Real.log (((o.Or B a).sing r).h _)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      exact congrArg _ ((o.Or B a).fund_sing r.1 r.2 x hx).symm) X.H X.S B X.S_tied hb₁ hb₂ he₁ he₂ har hβ hβn hbd hiso
  have hjb := GlobalTheory.T.block_join_inclusions_compat
  have hc₁ := (hjb.2.2 _ _ K₃ ρ K' ρ' κ₁ v₁ κ v hb₁ hb).1
  have hc₂ := (hjb.2.2 K J K₃ ρ K' ρ' κ₂ v₂ κ v hb₂ hb).1
  have hy₁ : y' ∘ v ∘ v₁ = y ∘ v₁ := by rw [← hy]; rfl
  have e₁ : imageZ (v ∘ v₁) (mCoordIdeal y') = (T.M B a).P := by rw [hjb.2.1 _ _ K' ρ' _ _ Ω₃ y' hc₁, hy₁, he₁]
  have e₂ : imageZ (v ∘ v₂) (mCoordIdeal y') = mCoordIdeal Dc.y := by
    rw [hjb.2.1 K J K' ρ' _ _ Ω₃ y' hc₂, ← he₂, ← hy]
    rfl
  have hp₁ := GlobalTheory.T.block_pullback_herm_line _ _ K' ρ' _ _ hc₁
  have hp₂ := GlobalTheory.T.block_pullback_herm_line K J K' ρ' _ _ hc₂
  choose pl hpl using fun A => (hp₁.1 A).exists
  choose Mt hMt using fun t => (hp₂.1 (muReg X.H X.S B t)).exists
  have hcore' := hcore Mt (fun t r => pl ((o.Or B a).Re.line (some r) t)) hMt fun t r => hpl _
  let RT := (Top.realOf o.toTowerOrigin).tie B a
  have ht₀ : 0 < (o.Sys a).t₀ := ((o.Sys a).reg none).1
  let x' : ℝ → Option (RootIx D) → HermLine (T.M B a).ι := fun t o' => o'.elim (PF.cst _) ((T.M B a).x t)
  have hx' : ∀ t cc, IsSmoothHerm (Top.combLine (x' t) cc) := fun t cc => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ cc).1 fun o' => by
    cases o'
    exacts [PF.cst_smooth, (T.M B a).x_smooth _ _]
  have hreg := GlobalTheory.T.regularized_hodge_metric_smooth K J II _ Ω W Dc X.H X.M X.S B X.S_tied
  set e := IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) with he
  have key : ∀ (a' b' : ℕ) (cc : Fin b' → Option (RootIx D) → ℤ), a' + b' = Top.dimFl (CMType H) (D.p + D.q) + 1 →
      Tendsto (fun t => II K' ρ' (mCoordIdeal y') (a' + b') (Fin.append (fun _ : Fin a' => Mt t)
          fun j => pl (Top.combLine (x' t) (cc j))) - e * II _ _ (T.M B a).P (a' + b') (Fin.append
            (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))) (𝓝[>] 0) (𝓝 0) := by
    intro a' b' cc hab
    refine (hcore' a' b' (fun j o' => o'.elim (cc j none) (gapc (cc j ∘ some))) hab).congr' ?_
    filter_upwards [hreg, Ioc_mem_nhdsGT ht₀] with t h1 h2
    have hA : IsArithVar (mCoordIdeal y') (a' + b') := hab ▸ har'
    have hls : ∀ cc, IsSmoothHerm (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) cc) := fun cc => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ cc).1 fun o' => by
      cases o'
      exacts [PF.cst_smooth, hp₁.2.1 _ _ (hpl _) ((o.Or B a).Re.line_smooth _ t h2.1 h2.2)]
    have hq : ∀ cc : Option (RootIx D) → ℤ, (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).a =
          (pl (Top.combLine (x' t) cc)).a ∧ ∀ z ∈ mcPts (mCoordIdeal y'),
        (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).h z =
          (pl (Top.combLine (x' t) cc)).h z := by
      intro cc
      have h3 := (GlobalTheory.T.iso_line_on_equivalence K' ρ' _ ∅ har'.2.1 (Set.empty_subset _)).2.2.2 _ _ _ _ _
        (fun o' : Option (RootIx D) => o'.elim (PF.cst _) fun r => (o.Or B a).Re.line (some r) t)
        (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ') fun r => pl ((o.Or B a).Re.line (some r) t))
        (fun o' => o'.elim (cc none) (gapc (cc ∘ some))) hc₁ fun o' => by
          cases o'
          exacts [pull_cst' hc₁, hpl _]
      have h4 := root_eq RT h2.1 h2.2 cc
      exact ⟨h3.1.trans ((congrArg _ h4.1.symm).trans (hpl _).1.symm),
        fun z hz => (h3.2 z).trans ((h4.2 _ (e₁ ▸ hp₁.2.2.1 _ _ hz)).symm.trans ((hpl _).2 z).symm)⟩
    have hm := hq fun o' => o'.elim 0 (muExp D.p)
    rw [comb_some] at hm
    have hMs := hp₂.2.1 _ _ (hMt t) h1.1
    have hxs := (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ (muExp D.p)).1 ((T.M B a).x_smooth t)
    congr 1
    · refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hMs, hls _, hMs, hp₁.2.1 _ _ (hpl _) (hx' _ _), (hq _).1, fun _ _ => trivial, (hq _).2]
    · have h5 := hII.2.2.1 _ _ K' ρ' _ _ Ω₃ y' (a' + b') (Fin.append
          (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))
        (Fin.append (fun _ : Fin a' => pl (Top.combLine ((T.M B a).x t) (muExp D.p))) fun j => pl (Top.combLine (x' t) (cc j)))
        hc₁ hA (by rw [e₁, hab]; exact (T.M B a).arith)
        (Fin.addCases (fun j => by simpa using hxs) fun j => by simpa using hx' _ _)
        (Fin.addCases (fun j => by simpa using hpl _) fun j => by simpa using hpl _)
      rw [e₁, hy₁, hfield] at h5
      rw [← h5]
      refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hls _, hls _, hp₁.2.1 _ _ (hpl _) hxs, hp₁.2.1 _ _ (hpl _) (hx' _ _), hm.1, (hq _).1, hm.2, (hq _).2]
  let ee := (Fintype.equivFin (PairIx (CMType H) D.p D.q)).symm
  have hdim : Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) = Top.dimFl (CMType H) (D.p + D.q) := by
    rw [Or.n_eq, count_pairs]
  let cF := fun i (o' : Option (RootIx D)) => o'.elim 0 (fibCoef (ee i))
  have hδ : (0 : ℝ) < e * (T.M B a).δ := mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hrk)) (Nat.cast_pos.2 (T.M B a).δ_pos)
  have happ : ∀ (t : ℝ) (n : ℕ), (Fin.append (fun _ : Fin n => Top.combLine ((T.M B a).x t) (muExp D.p))
      fun j => Top.combLine (x' t) (cF j)) = fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j) := by
    intro t n
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.append_left, Fin.append_right]
    · rfl
    · exact comb_some _ _ _
  have hNa : ∀ t i, (pl (Top.combLine (x' t) (cF i))).a = (pl (Top.combLine (x' 1) (cF i))).a := fun t i => by
    rw [(hpl _).1, (hpl _).1, comb_some, comb_some]
    simp only [Top.combLine, (T.M B a).x_deg]
  have hNs : ∀ t i, IsSmoothHerm (pl (Top.combLine (x' t) (cF i))) := fun t i => hp₁.2.1 _ _ (hpl _) (hx' _ _)
  refine ⟨K', inferInstance, ρ', inferInstance, κ ∘ κ₂, v ∘ v₂, mCoordIdeal y', _, 1, fun _ => 1, Mt,
    fun t _ i => pl (Top.combLine (x' t) (cF i)), e * (T.M B a).δ, hc₂, by rw [Nat.add_right_comm, hdim]; exact har', e₂, hδ,
    fun t _ i => hNa t i, fun t _ i => hNs t i, Eventually.of_forall hMt, ?_, ?_⟩
  · have h1 := key (Dc.n + 1) _ cF (by rw [Nat.add_right_comm, hdim])
    have h2 := (tendsto_arFun (T.M B a) ((GlobalTheory.T.real_tower_conv_I2 hAg hI II hII _ _ T (Top.realOf o.toTowerOrigin)).1 B a)
      (Top.toA (Top.testPoly T.j))).const_mul (e * (T.M B a).δ : ℝ)
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun t => ?_
    rw [happ, ← arFun_prod (T.M B a) hII t (by rw [Nat.add_right_comm, hdim]), ← test_factor' ee hqp Or.n_eq, o.j_eq]
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    ring
  · have h1 := key Dc.n _ (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF fun o' => o'.elim 1 0) (by rw [← hdim]; rfl)
    have hA : IsArithVar (mCoordIdeal y') (Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) + 1) := hdim ▸ har'
    have hs : ∀ t t', IsSmoothHerm (muReg X.H X.S B t) → ∀ j, IsSmoothHerm (Fin.append (fun _ : Fin Dc.n => Mt t)
        (fun i => pl (Top.combLine (x' t') (cF i))) j) := fun t t' ht =>
      Fin.addCases (fun j => by simpa using hp₂.2.1 _ _ (hMt t) ht) fun j => by simpa using hNs _ _
    have hcst : ∀ t t' u u', IsSmoothHerm (muReg X.H X.S B t) → IsSmoothHerm (muReg X.H X.S B u) →
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t)
          (fun i => pl (Top.combLine (x' t') (cF i))) i).h z)) (fun _ => 1) =
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt u)
          (fun i => pl (Top.combLine (x' u') (cF i))) i).h z)) (fun _ => 1) := fun t t' u u' ht hu =>
      pts_deg hI hA (hs t t' ht) (hs u u' hu) (Fin.addCases (fun j => by
        simp only [Fin.append_left, (hMt _).1, muReg, smoothRep_a]
        rfl) fun j => by simp only [Fin.append_right, hNa])
    filter_upwards [hreg] with u hu
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    refine sub_eq_zero.1 (neg_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds (h1.congr' ?_)))
    filter_upwards [hreg] with t ht
    have a1 : (fun j => pl (Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j))) =
        Fin.snoc (α := fun _ => HermLine ρ') (fun j => pl (Top.combLine (x' t) (cF j))) (PF.cst ρ') := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [comb_none]
      exact (hp₁.1 _).unique (hpl _) (pull_cst' hc₁)
    have a2 : (fun j => Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j)) =
        Fin.snoc (α := fun _ => HermLine (T.M B a).ι) (fun j => Top.combLine (x' t) (cF j)) (PF.cst _) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact comb_none _ _
    rw [a1, a2, Fin.append_snoc, Fin.append_snoc, happ]
    have a3 := LevelTowerAlt.ii_cst_int hII.1 hA _ (hs t t ht.1)
    have a4 := LevelTowerAlt.ii_cst_int hII.1 (show IsArithVar (T.M B a).P _ from hdim ▸ (T.M B a).arith)
      (fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin Dc.n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j))
      fun j => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ _).1 ((T.M B a).x_smooth t)
    rw [← geoFun_pts (T.M B a) hI t hdim, ← test_factor ee hqp Or.n_eq] at a4
    rw [hcst t t u 1 ht.1 hu.1] at a3
    refine (congrArg₂ (fun r s : ℝ => r - e * s) a3 a4).trans ?_
    rw [o.j_eq]
    ring

end LevelTowerAlt.Comparison₂
end
end
end
