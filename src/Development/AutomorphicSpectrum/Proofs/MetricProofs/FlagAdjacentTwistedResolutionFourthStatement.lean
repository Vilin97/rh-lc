module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUpperOfMinors
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecondStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IsParabolicTransvection

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.Parab

def IsParabolic {N : ℕ} (ca cb : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b, b < a → ¬ (a = cb ∧ b = ca) → M a b = 0

theorem IsParabolic.mul {N : ℕ} {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsParabolic ca cb A) (hB : IsParabolic ca cb B) :
    IsParabolic ca cb (A * B) := by
  intro a b hba hne
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : c < a ∧ ¬ (a = cb ∧ c = ca)
  · rw [hA a c h1.1 h1.2, zero_mul]
  by_cases h2 : b < c ∧ ¬ (c = cb ∧ b = ca)
  · rw [hB c b h2.1 h2.2, mul_zero]
  exfalso
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

theorem isParabolic_of_upper {N : ℕ} (ca cb : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.BlockTriangular id) : IsParabolic ca cb M := fun _ _ h _ => hM h

theorem isParabolic_transvection {N : ℕ} (ca cb : Fin N) (t : ℂ) :
    IsParabolic ca cb (1 + Matrix.single cb ca t) := by
  intro a b hba hne
  rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]
  intro h
  exact hne ⟨h.1.symm, h.2.symm⟩

theorem eq_transvection {N : ℕ} {ca cb : Fin N} {Y : Matrix (Fin N) (Fin N) ℂ} (hne : cb ≠ ca)
    (hlt : ca < cb) (hY : IsLowerUni Y) (hP : IsParabolic ca cb Y) :
    Y = 1 + Matrix.single cb ca (Y cb ca) := by
  ext a b
  rw [Matrix.add_apply]
  by_cases e : a = cb ∧ b = ca
  · obtain ⟨rfl, rfl⟩ := e
    rw [Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
  · have hs : Matrix.single cb ca (Y cb ca) a b = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)
    rw [hs, add_zero]
    rcases lt_trichotomy a b with h | h | h
    · rw [hY.2 a b h, Matrix.one_apply_ne h.ne]
    · subst h
      rw [hY.1 a, Matrix.one_apply_eq]
    · rw [hP a b h e, Matrix.one_apply_ne h.ne']

theorem mul_transvection_eq : ∀ (N : ℕ) (h B₀ B₁ : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ),
    (cb : ℕ) = ca + 1 → B₀.BlockTriangular id → B₁.BlockTriangular id → B₀.det ≠ 0 → B₁.det ≠ 0 →
    IsLowerUni (h * B₀) → IsLowerUni (h * (1 + Matrix.single cb ca t) * B₁) →
    ∃ y : ℂ, h * (1 + Matrix.single cb ca t) * B₁ = h * B₀ * (1 + Matrix.single cb ca y) := by
  intro N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1
  have hlt : ca < cb := by simp only [Fin.lt_def]; omega
  have hL0 : IsUnit (h * B₀).det := by rw [L0.det]; exact isUnit_one
  have hB0 : IsUnit B₀.det := isUnit_iff_ne_zero.mpr d0
  letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0
  letI := Matrix.invertibleOfIsUnitDet B₀ hB0
  set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE
  set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef
  have hY : h * B₀ * Y = h * E * B₁ := by
    rw [hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]
  have low : Y.BlockTriangular OrderDual.toDual := by
    have e1 : (h * B₀).BlockTriangular OrderDual.toDual := fun a b e => L0.2 _ _ e
    have e2 : (h * E * B₁).BlockTriangular OrderDual.toDual := fun a b e => L1.2 _ _ e
    have := (blockTriangular_inv_of_blockTriangular e1).mul e2
    rwa [← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0] at this
  have hYl : IsLowerUni Y := by
    refine ⟨fun a => ?_, fun a b e => low e⟩
    have := L1.1 a
    rw [← hY, Matrix.mul_apply, Finset.sum_eq_single a
      (fun c _ hc' => by
        rcases lt_or_gt_of_ne hc' with e | e
        · rw [low e, mul_zero]
        · rw [L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul] at this
    exact this
  have hP : IsParabolic ca cb Y :=
    (isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc
      ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))
  exact ⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩

end GlobalTheory.CompanionTheory.Ar.PB.Parab
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourth

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_fstPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem orbit_sndPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, if_neg hk]

end Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem orbit_wVec_mul (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h B₀ : Ψ → Matrix (Fin N) (Fin N) ℂ) (B₁ : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (t s : ℂ) (hB₀ : ∀ τ', IsBlockDiag j (B₀ τ') ∧ (B₀ τ').BlockTriangular id ∧ (B₀ τ').det ≠ 0)
    (hd : IsBlockDiag j B₁) (ht : B₁.BlockTriangular id) (hdet : B₁.det ≠ 0)
    (e : h τ * (1 + Matrix.single cb ca t) * B₁ = h τ * B₀ τ * (1 + Matrix.single cb ca s)) :
    SameOrbit (wVec M F b (fun τ' => h τ' * B₀ τ') τ a k₀ ca cb s) (wVec M F b h τ a k₀ ca cb t) := by
  obtain ⟨c, hc, hcz⟩ := sameOrbit_flagPt_mul K ι Φ y Ψ N j M F b h B₀ hB₀
  have hne : ∏ i ∈ stepCols N j a, B₁ i i ≠ 0 := by
    rw [Matrix.det_of_upperTriangular ht] at hdet
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  refine ⟨fun o => o.elim (∏ i ∈ stepCols N j a, B₁ i i) c, ?_, ?_⟩
  · rintro (_ | k)
    · exact hne
    · exact hc k
  · funext p
    obtain ⟨o, m⟩ := p
    cases o with
    | none =>
      simp only [wVec, Option.elim_none]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← e, (MinorCalc.minors_main ℂ N j a M.j_le).2.2.1 _ B₁ I hd ht]
      ring
    | some k =>
      exact congrFun hcz ⟨k, m⟩

theorem minor_ne_zero_of_plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    (b : (Σ k, baseIdx ι M.blk k) → ℂ) (hF : M.IsFrame F) (hb : b ∈ mcPts (mCoordIdeal M.x))
    (hG : M.GoodAt F (mCoordIdeal b)) (g : Ψ → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ τ', IsBlockDiag j (g τ'))
    (hp : ∀ p, plk M F b (flagPt M F b g) p ≠ 0) (τ' : Ψ) (i : Fin N) (hi : IsProperStep N j i) :
    minorIJ (g τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have e := plk_flagPt K ι Φ y Ψ N j M F b g (τ', i) k hF hb hG hg hk
  have := hp (τ', i)
  rwa [e] at this

theorem vector_of_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb RW q hq h0 h1 hinj l x hO hp0 hp1
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  obtain ⟨x₀, hx₀⟩ := (re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 x)
  have hz := RW.mem x x (RW.mem_U x)
  have hbase : SameOrbit (basePart M.blk (fstPt k₀ (RW.lift x x)))
      (BM.Rb.lift (FA.pr (q 0 x)) (FA.pr (q 0 x))) := by
    have e1 := orbit_basePart M.blk (h0 x x₀ hx₀)
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm e1) e2
  obtain ⟨h, t, hh, ho⟩ := GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb FA.Re.arith l _ hO _
    hz hbase
  obtain ⟨hbv, hgood, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l _ hO
  obtain ⟨hw0, hw1⟩ := fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l)
    (bvec BM l (FA.pr (q 0 x))) h t
  have hf := orbit_fstPt ho
  have hg := orbit_sndPt ho
  rw [hw0] at hf
  rw [hw1] at hg
  have hE : IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
    intro r s hrs
    have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
    have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hrs hs.symm
    rw [Matrix.add_apply, e1, e2, add_zero]
  have hEdet : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
    refine (Matrix.det_of_lowerTriangular _ fun r s hrs => ?_).trans (Finset.prod_eq_one fun r _ => ?_)
    · have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne (ne_of_lt (show r < s from hrs))
      have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlt hrs
      rw [Matrix.add_apply, e1, e2, add_zero]
    · have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r r = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, h'⟩
        exact hlt.ne h'
      rw [Matrix.add_apply, e2, add_zero, Matrix.one_apply_eq]
  have hbd₁ : IsBlockDiag j (h τ * (1 + Matrix.single cb ca t)) :=
    ((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ).1 hE).1
  have hdet₁ : (h τ * (1 + Matrix.single cb ca t)).det ≠ 0 := by
    rw [Matrix.det_mul, hEdet, mul_one]
    exact (hh τ).2
  have hbdU : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hbd₁
    · rw [Function.update_of_ne e]
      exact (hh τ').1
  have m0 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood h (fun τ' => (hh τ').1)
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hf).1 (hp0 p))
  have m1 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood _ hbdU
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hg).1 (hp1 p)) τ
  rw [Function.update_self] at m1
  choose B₀ hd₀ ht₀ hdet₀ hu₀ using fun τ' =>
    BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (m0 τ')
  obtain ⟨B₁, hd₁, ht₁, hdetB₁, hu₁⟩ := BigCell.exists_upper_of_minors N j _ M.j_le hbd₁ hdet₁ m1
  obtain ⟨s, es⟩ := Parab.mul_transvection_eq N (h τ) (B₀ τ) B₁ ca cb t hcb (ht₀ τ) ht₁ (hdet₀ τ) hdetB₁ (hu₀ τ) hu₁
  obtain ⟨c, a₀, hL⟩ := (LcFam.lc_main Ψ N j τ ca cb hlt hs.symm).2.2.1 (fun τ' => h τ' * B₀ τ') fun τ' =>
    ⟨((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ').1 (hd₀ τ')).1, hu₀ τ'⟩
  refine ⟨c, a₀, a₀ + s, ?_⟩
  rw [hL, add_sub_cancel_left]
  exact orbit_trans ho (orbit_symm (orbit_wVec_mul M (BM.F l) _ h B₀ B₁ τ a k₀ ca cb t s
    (fun τ' => ⟨hd₀ τ', ht₀ τ', hdet₀ τ'⟩) hd₁ ht₁ hdetB₁ es))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourthStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart <;> assumption)
end
end
