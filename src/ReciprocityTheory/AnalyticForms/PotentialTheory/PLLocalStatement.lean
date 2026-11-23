module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffMulOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.AnalyticForms.PotentialTheory.MIntSumCont

section

@[expose] public section

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] in
theorem prod_sigma {r n : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) (z : Fin n → ℂ)
    (g : Fin r → ℂ) (hg : ∀ k, g k = (σ k).elim 1 (fun i => z i ^ m k)) :
    ∏ k, g k = ∏ i, z i ^ ((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) := by
  simp_rw [hg]
  have h1 : ∀ k, (σ k).elim 1 (fun i => z i ^ m k) = ∏ i, (if σ k = some i then z i ^ m k else 1) := by
    intro k
    cases h : σ k with
    | none => simp
    | some j => simp [Finset.prod_ite_eq]
  simp_rw [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_natCast, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] in
theorem sum_sigma {r n : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) (Xs : Fin n → ℝ) :
    ∑ i, (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) : ℝ) * Xs i =
      ∑ k, (m k : ℝ) * ∑ i, (if σ k = some i then Xs i else 0) := by
  calc ∑ i, (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ) : ℝ) * Xs i
      = ∑ i, ∑ k, (m k : ℝ) * (if σ k = some i then Xs i else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k, (m k : ℝ) * ∑ i, (if σ k = some i then Xs i else 0) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]

theorem mInt_sum_cont {e' : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (A : FinHolAtlas e' Y) (Φ : Fin e' → LocPot Y) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type}
    (s : Finset ι) (f : ι → Y → ℝ) (hf : ∀ j, Continuous (f j)) :
    mInt A Φ (fun p => ∑ j ∈ s, f j p) = ∑ j ∈ s, mInt A Φ (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mInt_zero_fun A Φ (fun _ => rfl)
  | insert j s hj ih =>
    have hcont : Continuous (fun p => ∑ j ∈ s, f j p) := continuous_finsetSum _ fun j _ => hf j
    have h := mIntLinear A Φ hΦ 1 (f j) (fun p => ∑ j ∈ s, f j p)
      (mIntegrableCont A Φ hΦ _ (hf j)) (mIntegrableCont A Φ hΦ _ hcont)
    simp only [one_mul] at h
    simp_rw [Finset.sum_insert hj]
    rw [← ih]
    exact h

theorem lhs_sum (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ)
    (hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) →
      MIntegrable A Φ' (logNormSec L s))
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) {ι : Type} (t : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ j, A.Smooth (f j)) :
    mInt A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) (logNormSec L s) =
      ∑ j ∈ t, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) := by
  classical
  have hdens : ∀ (j' : Fin A.n) (y : Fin (e + 1) → ℂ), y ∈ (A.chart j').target →
      locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y =
        ∑ j ∈ t, locDens A (Fin.cons (LocPot.ofFun (f j)) Φ) j' y := by
    intro j' y hy
    let ψs : Fin e → (Fin (e + 1) → ℂ) → ℝ :=
      fun i y' => (Φ i).φ ((A.chart j').symm y) ((A.chart j').symm y')
    have hfam : ∀ u : X → ℝ, (fun i y' => ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i).φ
        ((A.chart j').symm y) ((A.chart j').symm y')) = Fin.cons (u ∘ (A.chart j').symm) ψs := by
      intro u
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have hmem : (A.chart j').target ∩ (A.chart j').symm ⁻¹' Set.univ ∈ nhds y := by
      simpa using (A.chart j').open_target.mem_nhds hy
    have hsmooth : ∀ j, ContDiffAt ℝ 2 (f j ∘ (A.chart j').symm) y := fun j => by
      have h := ((hf j) j').contDiffAt hmem
      have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
        first
          | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
          | exact WithTop.coe_le_coe.2 le_top
          | (norm_num; done)
          | (simp; done)
      exact h.of_le hle
    have key : ∀ F G : (Fin (e + 1) → ℂ) → ℝ, ContDiffAt ℝ 2 F y → ContDiffAt ℝ 2 G y →
        maDens (Fin.cons (fun w => F w + G w) ψs) y =
          maDens (Fin.cons F ψs) y + maDens (Fin.cons G ψs) y := by
      intro F G hF hG
      unfold maDens
      have e1 : ∀ H : (Fin (e + 1) → ℂ) → ℝ,
          (fun k => hessC ((Fin.cons H ψs : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ) k) y) =
            Fin.cons (hessC H y) (fun k => hessC (ψs k) y) := by
        intro H
        funext k
        refine Fin.cases ?_ (fun k => ?_) k <;> rfl
      rw [e1, e1, e1, ReciprocityTheory.AnForm.A.hessC_add F G y hF hG]
      have h := ReciprocityTheory.AnForm.A.mdisc_cons_smul_add 1 1 (hessC F y) (hessC G y) (fun k => hessC (ψs k) y)
      simp only [one_smul, one_mul] at h
      rw [h, Complex.add_re]
      ring
    have key0 : maDens (Fin.cons (fun _ => (0 : ℝ)) ψs) y = 0 := by
      have h := key (fun _ => 0) (fun _ => 0) contDiffAt_const contDiffAt_const
      simp only [add_zero] at h
      linarith
    simp only [locDens, hfam]
    induction t using Finset.induction_on with
    | empty =>
      have h0 : ((fun p => ∑ i ∈ (∅ : Finset ι), f i p) ∘ (A.chart j').symm) = fun _ => (0 : ℝ) := by
        funext w
        simp
      rw [h0, Finset.sum_empty, key0]
    | insert j t hj ih =>
      rw [Finset.sum_insert hj, ← ih]
      have e2 : ((fun p => ∑ i ∈ insert j t, f i p) ∘ (A.chart j').symm) =
          fun w => (f j ∘ (A.chart j').symm) w + ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) w := by
        funext w
        simp [Finset.sum_insert hj]
      have hsum : ContDiffAt ℝ 2 ((fun p => ∑ i ∈ t, f i p) ∘ (A.chart j').symm) y := by
        show ContDiffAt ℝ 2 (fun w => ∑ i ∈ t, (f i ∘ (A.chart j').symm) w) y
        exact ContDiffAt.sum fun i _ => hsmooth i
      rw [e2, key _ _ (hsmooth j) hsum]
  have hint : ∀ j, MIntegrable A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) := fun j =>
    hℓ _ (fun i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact isPotential_ofFun A (f j) (hf j)
      · exact hΦ i)
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← MeasureTheory.integral_finsetSum t (fun j _ => integrableOn_weight A hP.some _ _ (hint j) j')]
    have heq : Set.EqOn
        (fun y => hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) *
          locDens A (Fin.cons (LocPot.ofFun fun p => ∑ j ∈ t, f j p) Φ) j' y)
        (fun y => ∑ j ∈ t, hP.some.χ j' ((A.chart j').symm y) * logNormSec L s ((A.chart j').symm y) *
          locDens A (Fin.cons (LocPot.ofFun (f j)) Φ) j' y) (A.chart j').target := by
      intro y hy
      simp only
      rw [hdens j' y hy, Finset.mul_sum]
    first
      | exact setIntegral_congr_fun (A.chart j').open_target.measurableSet heq
      | exact setIntegral_congr (A.chart j').open_target.measurableSet heq
  · simp

theorem pl_good (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hSNC : IsSNC A L s m W) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X)
    (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (hψ : IsCompatChart A ψ)
    (hψL : ψ.source ⊆ L.U x) (σ : Fin r → Option (Fin (e + 1)))
    (hWψ : ∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0})
    (u : X → ℂ) (hu : A.HoloOn ψ.source u) (hu0 : ∀ y ∈ ψ.source, u y ≠ 0)
    (hsu : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k))
    {V : Set X} (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x)
    (hxW : ∀ k, x ∉ W k → V ∩ W k = ∅) {v : X → ℝ} (hv : A.Smooth v) (hvV : tsupport v ⊆ V) :
    mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
          (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v := by
  classical
  have hℓ : ∀ Φ' : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Φ' i)) →
      MIntegrable A Φ' (logNormSec L s) :=
    fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ'
  have hsu' : ∀ p ∈ ψ.source, s x p =
      u p * ∏ i, ψ p i ^ (((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ)) := by
    intro p hp
    rw [hsu p hp, prod_sigma σ m (ψ p) (fun k => (σ k).elim 1 (fun i => ψ p i ^ m k)) (fun k => rfl)]
  rw [pl_chart A L s hL hs hℓ Φ hΦ x ψ hψ hψL u hu hu0
    (fun i => ((∑ k, if σ k = some i then m k else 0 : ℕ) : ℤ)) hsu' hV hVψ hVΦ hv hvV]
  congr 1
  rw [sum_sigma σ m (fun i => ∫ w, chartExt ψ v (hypInclAt i w) *
    densHypAt i (fun k => (Φ k).φ x ∘ ψ.symm) w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  cases hσ : σ k with
  | none =>
    simp only [reduceCtorEq, if_false, Finset.sum_const_zero]
    have hv0 (p : W k) : v p.1 = 0 := by
      by_contra hne
      have hp : p.1 ∈ tsupport v := subset_tsupport _ hne
      have hpψ := hVψ (hvV hp)
      have hmem : p.1 ∈ W k ∩ ψ.source := ⟨p.2, hpψ⟩
      rw [hWψ k] at hmem
      obtain ⟨i, hi, -⟩ := hmem.2
      rw [hσ] at hi
      exact absurd hi (by simp)
    exact (mInt_zero_fun (B k) _ (g := v ∘ Subtype.val) hv0).symm
  | some i =>
    simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    haveI : CompactSpace (W k) :=
      isCompact_iff_compactSpace.1 (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hSNC k).isCompact
    have hWψ' : W k ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0} := by
      rw [hWψ k, hσ]
      ext y
      simp
    exact (slice_mInt (B k) (hB k) Φ hΦ hψ hWψ' x hV hVψ hVΦ (hxW k) hv hvV).symm

end

end ReciprocityTheory.AnForm.M.PLAux
end
end

-- Source module: ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartRestrOpen

section

@[expose] public section

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

omit [T2Space X] [CompactSpace X] in
theorem restrOpen_source' (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {V : Set X} (hV : IsOpen V) :
    (ψ.restrOpen V hV).source = ψ.source ∩ V := by
  rfl

omit [T2Space X] [CompactSpace X] in
theorem isCompatChart_restrOpen {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {V : Set X} (hV : IsOpen V) : IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : (A.chart j).symm y ∈ ψ.source ∩ V := hy2
    exact ⟨hy1, h'.1⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : y ∈ ψ.target ∩ ψ.symm ⁻¹' V := hy1
    exact ⟨h'.1, hy2⟩

theorem pl_exists_chart (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hSNC : IsSNC A L s m W) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X) :
    ∃ ψ' : OpenPartialHomeomorph X (Fin (e + 1) → ℂ), IsCompatChart A ψ' ∧ x ∈ ψ'.source ∧
      ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ'.source →
        mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
          ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v := by
  classical
  obtain ⟨ψ, hψ, hx, hψL, σ, -, hWψ, u, hu, hu0, hsu⟩ := hSNC x
  have hsu' : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k) := by
    intro y hy
    rw [hsu y hy]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases σ k with _ | i <;> rfl
  obtain ⟨V, hVdef⟩ : ∃ V : Set X, V = ψ.source ∩ (⋂ k, (Φ k).U x) ∩
      ⋂ k, (if x ∈ W k then Set.univ else (W k)ᶜ) := ⟨_, rfl⟩
  have hVo : IsOpen V := by
    rw [hVdef]
    refine (ψ.open_source.inter (isOpen_iInter_of_finite fun k => (Φ k).isOpen_U x)).inter
      (isOpen_iInter_of_finite fun k => ?_)
    split_ifs
    · exact isOpen_univ
    · exact (sncClosed A L s m W hSNC k).isOpen_compl
  have hxV : x ∈ V := by
    rw [hVdef]
    refine ⟨⟨hx, Set.mem_iInter.2 fun k => (Φ k).mem_U x⟩, Set.mem_iInter.2 fun k => ?_⟩
    split_ifs with h
    · exact Set.mem_univ _
    · exact h
  refine ⟨ψ.restrOpen V hVo, isCompatChart_restrOpen hψ hVo, ?_, fun v hv hvV => ?_⟩
  · rw [restrOpen_source']
    exact ⟨hx, hxV⟩
  · have hvV' : tsupport v ⊆ V := hvV.trans (by rw [restrOpen_source']; exact Set.inter_subset_right)
    refine pl_good A L s m W B hL hs hSNC hB Φ hΦ x ψ hψ hψL σ hWψ u hu hu0 hsu' hVo
      (fun p hp => by rw [hVdef] at hp; exact hp.1.1)
      (fun k p hp => by rw [hVdef] at hp; exact Set.mem_iInter.1 hp.1.2 k) (fun k hk => ?_) hv hvV'
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hpW
    rw [hVdef] at hp
    have := Set.mem_iInter.1 hp.2 k
    rw [if_neg hk] at this
    exact this hpW

theorem pl_global : PoincareLelongStatement := by
  intro e X _ _ _ A L s r m W B hL hs hSNC hB v hv Φ hΦ
  classical
  choose ψ hψ hxψ hpl using fun x => pl_exists_chart A L s m W B hL hs hSNC hB Φ hΦ x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source)
    (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)
  have hcov : ∀ y, ∃ i, y ∈ (ψ (t.equivFin.symm i : X)).source := by
    intro y
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨t.equivFin ⟨x, hxt⟩, by simpa using hy⟩
  obtain ⟨AC, hAC, -, hAC2⟩ :=
    atlasOfCompat A (fun i => ψ (t.equivFin.symm i : X)) (fun i => hψ _) hcov
  obtain ⟨P⟩ := existsPartition AC
  obtain ⟨f, hf⟩ : ∃ f : Fin AC.n → X → ℝ, f = fun j p => P.χ j p * v p := ⟨_, rfl⟩
  have hfs : ∀ j, A.Smooth (f j) := by
    intro j
    have h1 : A.Smooth (P.χ j) := smoothOn_of_compatible ⟨hAC.2, hAC.1⟩ isOpen_univ (P.smooth j)
    rw [hf]
    exact smoothOn_mul h1 hv
  have hfpl : ∀ j, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) =
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) - mInt A (Fin.cons L Φ) (f j) := by
    intro j
    obtain ⟨i, hi⟩ := hAC2 j
    refine hpl (t.equivFin.symm i : X) (f j) (hfs j) ?_
    have h2 := P.tsupport_subset j
    rw [hi] at h2
    rw [hf]
    exact tsupport_mul_subset_left.trans h2
  have hvsum : v = fun p => ∑ j ∈ Finset.univ, f j p := by
    funext p
    rw [hf]
    simp only [← Finset.sum_mul, P.sum_eq_one, one_mul]
  have hpot : ∀ i, IsPotential A ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hL
    · exact hΦ k
  have : ∀ k, CompactSpace (W k) := fun k =>
    isCompact_iff_compactSpace.1 (sncClosed A L s m W hSNC k).isCompact
  have hΦB : ∀ k i, IsPotential (B k) ((Φ i).pullback Subtype.val continuous_subtype_val) :=
    fun k i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i)
  have hc : ∀ j, Continuous (f j) := fun j => smooth_continuous (hfs j)
  have hk : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      ((fun p => ∑ j ∈ Finset.univ, f j p) ∘ Subtype.val) =
      ∑ j, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) := fun k =>
    mInt_sum_cont (B k) _ (hΦB k) Finset.univ (fun j => f j ∘ Subtype.val)
      (fun j => (hc j).comp continuous_subtype_val)
  rw [hvsum, lhs_sum A L s (fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ') Φ hΦ
    Finset.univ f hfs, mInt_sum_cont A (Fin.cons L Φ) hpot Finset.univ f hc,
    Finset.sum_congr rfl fun j _ => hfpl j, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hk k, Finset.mul_sum]

end

end ReciprocityTheory.AnForm.M.PLAux
end
end

-- Source module: ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement

section

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem poincareLelong : PoincareLelongStatement := PLAux.pl_global

end

end ReciprocityTheory.AnForm.M
end
end
