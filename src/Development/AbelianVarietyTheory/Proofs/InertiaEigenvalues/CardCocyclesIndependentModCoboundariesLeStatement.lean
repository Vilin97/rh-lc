module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeSmulMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityLaurentShiftEqSumSenStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomialStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRankStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeights

section

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam.PolarKernel
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam Module

section lin
variable {k : Type} [Field k] {U : Type} [AddCommGroup U] [Module k U]

theorem finrank_quot (A B : Submodule k U) :
    finrank k (↥A ⧸ B.submoduleOf A) = finrank k (A.map B.mkQ) := by
  have h := (LinearMap.quotKerEquivRange (B.mkQ.domRestrict A)).finrank_eq
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  exact h

theorem finrank_le_gmult (T : Module.End k U) (P Q Z S : Submodule k U) [FiniteDimensional k S]
    (hP : P ≤ S ⊔ Q) (hZ : ∀ x ∈ Z, x ∈ P ∧ T x ∈ Q) :
    finrank k (↥Z ⧸ Q.submoduleOf Z) ≤ gmult T P Q 0 := by
  unfold gmult
  rw [finrank_quot, finrank_quot, map_zero (algebraMap k (Module.End k U)), sub_zero]
  have hfin : FiniteDimensional k ((P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ) := by
    have h : (P ⊓ ⨆ m : ℕ, Q.comap (T ^ m)).map Q.mkQ ≤ S.map Q.mkQ := by
      have := Submodule.map_mono (f := Q.mkQ) ((inf_le_left (b := ⨆ m : ℕ, Q.comap (T ^ m))).trans hP)
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at this
    exact Submodule.finiteDimensional_of_le h
  refine Submodule.finrank_mono (Submodule.map_mono fun x hx => ⟨(hZ x hx).1, ?_⟩)
  refine Submodule.mem_iSup_of_mem 1 ?_
  rw [Submodule.mem_comap, pow_one]
  exact (hZ x hx).2
end lin

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem le_span_sup {ι : Type} (e : ι → V) (P : Submodule k⟦X⟧ V)
    (hP : Submodule.span k⟦X⟧ (Set.range e) = P) :
    P.restrictScalars k ≤ Submodule.span k (Set.range e) ⊔ (sh 1 P).restrictScalars k := by
  intro x hx
  rw [Submodule.restrictScalars_mem, ← hP, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  refine Submodule.sum_mem _ fun i _ => ?_
  show c i • e i ∈ _
  have he : e i ∈ P := hP ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : k⟦X⟧, c i = algebraMap k k⟦X⟧ (PowerSeries.constantCoeff (c i)) + PowerSeries.X * d :=
    ⟨_, by rw [add_comm]; exact PowerSeries.eq_X_mul_shift_add_const (c i)⟩
  rw [hd, add_smul, algebraMap_smul]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) ?_
  refine mem_sh_iff_exists.2 ⟨d • e i, P.smul_mem _ he, ?_⟩
  rw [zpow_one, vv_eq_coe_X, mul_smul]
  exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) _

theorem exists_finite_le_sup (N : Submodule k⟦X⟧ V) (hN : N.FG) (a : ℤ) (m : ℕ) :
    ∃ S : Submodule k V, FiniteDimensional k S ∧
      (sh a N).restrictScalars k ≤ S ⊔ (sh (a + m) N).restrictScalars k := by
  induction m with
  | zero => exact ⟨⊥, inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨S, hS, h⟩ := ih
    have hfg : (sh (a + m) N).FG := hN.map _
    obtain ⟨n, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
    have h2 := le_span_sup e _ he
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h2
    have : FiniteDimensional k (Submodule.span k (Set.range e)) :=
      FiniteDimensional.span_of_finite k (Set.finite_range e)
    refine ⟨S ⊔ Submodule.span k (Set.range e), inferInstance, h.trans ?_⟩
    rw [sup_assoc]
    refine sup_le_sup_left ?_ _
    rw [Nat.cast_succ, ← add_assoc]
    exact h2

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC w Z hZ
  have hr := GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen R g hg N hN hC (-w) w 0
  simp only [zero_add, neg_add_cancel, sh_zero_eq] at hr
  obtain ⟨S, hS, hF⟩ := exists_finite_le_sup N hN.1 (-w) w
  rw [neg_add_cancel, sh_zero_eq] at hF
  rw [← hr]
  exact finrank_le_gmult (nab g) _ _ Z S hF hZ

end GlobalTheory.PhiGam.PolarKernel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement

section

@[expose] public section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  first | exact @GlobalTheory.PhiGam.PolarKernel.main | exact GlobalTheory.PhiGam.PolarKernel.main | (intros; apply GlobalTheory.PhiGam.PolarKernel.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLe

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.PolarBound

theorem card_le_sum {k V ι : Type} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] {s : ℕ}
    (c : ι → Fin s → V) (N : ι → Submodule k V) (d : ι → ℕ)
    (hd : ∀ i, Module.finrank k (↥(LinearMap.range (Fintype.linearCombination k (c i))) ⧸
      (N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))) ≤ d i)
    (hinj : ∀ t : Fin s → k, (∀ i, ∑ a, t a • c i a ∈ N i) → t = 0) : s ≤ ∑ i, d i := by
  let f := LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ
    (Fintype.linearCombination k (c i)).rangeRestrict
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    refine hinj t fun i => ?_
    have h1 : f t i = 0 := congrFun ht i
    exact (Submodule.Quotient.mk_eq_zero ((N i).submoduleOf
      (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h2
  exact h2.trans (Finset.sum_le_sum fun i _ => hd i)

variable {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem cob_mem (D : ModPG R n (Vc k m)) (y : ZMod n → Vc k m) :
    ((fun i => D.φ i (y (i - 1)) - y i, fun i => D.γ i (y i) - y i) :
      (ZMod n → Vc k m) × (ZMod n → Vc k m)) ∈ herrB D := ⟨y, rfl⟩

theorem gauge_one (D : ModPG R n (Vc k m)) (Dt : TopData n m) (N : Lats k n m)
    (hI : ∀ i, (Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i)
    (hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i) (hN : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i (a : ℕ), a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0)
    (z : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : InZZ D Dt N z.1 z.2) :
    ∃ (z' : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (c : ZMod n → Vc k m), z - z' ∈ herrB D ∧
      ∀ i, D.γ i (z'.1 i) - z'.1 i = D.φ i (z'.2 (i - 1)) - z'.2 i ∧ z'.2 i ∈ sh (Dt.sg l i + 3) (N i) ∧
        c i - z'.1 i ∈ N i ∧
        (Dt.ty i = LType.G → c i ∈ sh (-Dt.w i) (N i) ∧ D.γ i (c i) - c i ∈ sh 1 (N i)) ∧
        (Dt.ty i = LType.Bd → c i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
          D.γ i (c i) - c i ∈ sh (Dt.wst i + 2) (N i)) := by
  obtain ⟨b, g⟩ := z
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  obtain ⟨y, hy, hy'⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
    (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g
    (fun i => (hz i).1) (fun i => (hz i).2.1)).1
  have hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧
      (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i)) := by
    intro i
    cases h : Dt.ty i with
    | G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩
    | Bd =>
      obtain ⟨x, hx, hx'⟩ := ((hz i).2.2.2 h).2
      exact ⟨x, hx, fun h => (by cases h), fun _ => hx'⟩
  choose x hx hxG hxB using hx
  refine ⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)),
    fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩
  · convert cob_mem D y using 1
    ext i : 2 <;> simp
  have h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i := (hz i).1
  have hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hy _, rfl⟩
  have hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i) := by
    have h1 := Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3)
      (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))
    refine sh_le_sh_of_le ?_ _ h1
    have := hI i
    unfold TopData.wst
    push_cast; nlinarith
  have hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) =
      D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i)) := by
    simp only [map_sub, map_add (f := _), D.comm]
    linear_combination (norm := module) h0
  have hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    simpa [sh_zero_eq] using sh_le_sh_of_le (a := 0) (b := -a) (by omega) P
  refine ⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp only [map_sub, D.comm]
    linear_combination (norm := module) h0
  · convert (N i).sub_mem (hx i) (hy i) using 1
    simp only []
    abel
  · exact Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))
  · beta_reduce
    rw [hc, hxG i h]
    refine Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))
    · have := (hw i).2; omega
    · omega
  · refine Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_
    have := sh_le_sh (-Dt.wst i) (hAB i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
  · beta_reduce
    rw [hc]
    exact Submodule.sub_mem _ hdeep (hxB i h)


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem span_prop {s : ℕ} (c : Fin s → Vc k m) (g : Vc k m →ₗ[k] Vc k m) (P Q : Submodule k⟦X⟧ (Vc k m))
    (h : ∀ a, c a ∈ P ∧ g (c a) - c a ∈ Q) :
    ∀ x ∈ LinearMap.range (Fintype.linearCombination k c), x ∈ P ∧ g x - x ∈ Q := by
  rintro _ ⟨t, rfl⟩

  rw [Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]
  refine ⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1,
    Submodule.sum_mem _ fun a _ => ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ _ (h a).2

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli
  have hW := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3
  have hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i := fun i => by
    have h1 := Dt.one_le_letterBlockLength
    have := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
    unfold TopData.wst
    omega
  choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl5 : 5 ≤ l := by have := T1 0; omega
  obtain ⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩ := hΨ.modPG l k hl5 R ι hι
  choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i
  refine card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)
  · cases h : Dt.ty i with
    | G =>
      have e : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (hw i).1
      have := GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by
          have := span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx
          rw [e]
          refine ⟨this.1, ?_⟩
          have h2 := mem_sh_iff_smul_mem.1 this.2
          rwa [zpow_neg_one] at h2)
      rw [e, (hs i).2.1 h] at this
      exact this
    | Bd =>
      have e : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (hw i).2
      obtain ⟨-, -, w1, w2⟩ := (hW i).2.2.2 h
      have h1 := Dt.one_le_letterBlockLength
      have h2 := T1 i
      have h3 := (hW i).1
      obtain ⟨s1, s2⟩ := (hs i).2.2 h
      have := GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2
        (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat
        (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [e]; exact (hAB i).2)
        (hAB i).1 (by rw [e]; unfold TopData.wst; nlinarith) (hs _).1
        (fun y hy hy0 => by
          rw [e] at hy ⊢
          have h4 := (hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)
          have h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1) :=
            ⟨by rwa [neg_add_eq_sub], hy0⟩
          rw [← h4] at h5
          obtain ⟨x, ⟨hx, hx0⟩, hxy⟩ := h5
          exact ⟨x, hx, hx0, hxy⟩)
        (by rw [e]; exact GlobalTheory.T.gammaNabla_mem_of_killing_polynomial D i (N i) _ (hC i) s2)
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by
          rw [e]; exact span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))
      rw [Module.finrank_fin_fun] at this
      omega
  · have hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i) := fun i => by
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1
    obtain ⟨y, -, hy⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
      (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1)
      (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by

        simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
        map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        exact Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])
      (fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by
        have h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1
        have h2 : ∑ a, t a • c a i ∈ N i := ht i
        convert (N i).sub_mem h2 h1 using 1
        simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib,
          ← smul_sub, sub_sub_cancel])
    have h1 : ∑ a, t a • z' a ∈ herrB D := by
      convert cob_mem D y using 1
      exact Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)
    have h2 : ∑ a, t a • (z a - z' a) ∈ herrB D :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)
    have h3 : ∑ a, t a • z a ∈ herrB D := by
      convert (herrB D).add_mem h1 h2 using 1
      simp only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]
    funext a
    refine Fintype.linearIndependent_iff.1 hli t ?_ a
    have h4 : (herrB D).mkQ (∑ a, t a • z a) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h3

    simpa only [map_sum, map_smul] using h4

end GlobalTheory.Models.PolarBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesIndependentModCoboundariesLeStatement

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  first | exact @GlobalTheory.Models.PolarBound.main | exact GlobalTheory.Models.PolarBound.main | (intros; apply GlobalTheory.Models.PolarBound.main <;> assumption)
end
end
