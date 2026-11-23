module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantMatrixLiftOfAdicCompleteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfSplitStatement
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorTraceOneFiniteLevel

section

@[expose] public section

namespace GlobalTheory.UnramifiedCrys

theorem exists_witt_trace_one : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  intro p hp G _ R _ _ _ _ ρ m hm hfin
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  obtain ⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by
    by_contra hc
    push Not at hc
    have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      funext θ
      simp only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]
      exact hc θ) (QuotientGroup.mk 1)
    exact one_ne_zero this
  have hθm : (θ : R) ^ p ^ m = θ := θ.2
  have hsum : ∀ (f : G → WittVector p R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  set t := ∑ x : G ⧸ N, ρ x.out θ with ht
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  have hθN : ∀ n ∈ N, WittVector.map (ρ n).toRingHom (WittVector.teichmuller p (θ : R)) =
      WittVector.teichmuller p (θ : R) := fun n hn => by
    rw [WittVector.map_teichmuller]
    congr 1
    exact hn θ hθm
  set T := ∑ x : G ⧸ N, WittVector.map (ρ x.out).toRingHom (WittVector.teichmuller p (θ : R))
    with hT
  have hTg : ∀ g, WittVector.map (ρ g).toRingHom T = T := fun g => by

    rw [hT, map_sum, ← hsum (fun g => WittVector.map (ρ g).toRingHom
    (WittVector.teichmuller p (θ : R))) (fun g n hn => by
      simp only [wittMap_mul, hθN n hn]) g]
    simp only [wittMap_mul]
  have hT0 : WittVector.constantCoeff T = t := by

    rw [hT, map_sum, ht]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WittVector.map_teichmuller, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    rfl
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have hmem : T * WittVector.teichmuller p (t ^ (p ^ m - 2)) - 1 ∈
      Ideal.span {(p : WittVector p R)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      map_mul, map_one, hT0, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      mul_comm, hu, sub_self]
  have hunit : IsUnit T := by
    have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hmem) 1
    rw [mul_one, sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨S, hS⟩ := hunit.exists_left_inv
  have hSg : ∀ g, WittVector.map (ρ g).toRingHom S = S := fun g => by
    have h2 := congrArg (WittVector.map (ρ g).toRingHom) hS
    rw [map_mul, hTg, map_one] at h2
    exact hunit.mul_right_cancel (h2.trans hS.symm)
  refine ⟨S * WittVector.teichmuller p (θ : R), fun g hg => ?_, ?_⟩
  · rw [map_mul, hSg, hθN g hg]
  · rw [finsum_eq_sum_of_fintype]
    simp only [map_mul, hSg]
    rw [← Finset.mul_sum, ← hT, hS]

end GlobalTheory.UnramifiedCrys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorTraceOneFiniteLevelStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_wittVector_trace_one_finiteLevel : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  first | exact @GlobalTheory.UnramifiedCrys.exists_witt_trace_one | exact GlobalTheory.UnramifiedCrys.exists_witt_trace_one | (intros; apply GlobalTheory.UnramifiedCrys.exists_witt_trace_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparisonStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.period_data_comparison : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) (W W' : Matrix (Fin n) (Fin n) BdR), W * W' = 1 → (∀ i j, W i j ∈ PD.Fil 0) → (∀ i j, W' i j ∈ PD.Fil 0) → (∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a → a = 0 := by
  first | exact @GlobalTheory.SplitJump.jump_eq_zero | exact GlobalTheory.SplitJump.jump_eq_zero | (intros; apply GlobalTheory.SplitJump.jump_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedRep

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R] (ρ : G →* (R ≃+* R))

theorem normal_fixer (p m : ℕ) : (fixer ρ p m).Normal := ⟨fun a ha g y hy => by
  have h : ρ g⁻¹ y ^ p ^ m = ρ g⁻¹ y := by rw [← map_pow, hy]
  rw [map_mul, map_mul, RingAut.mul_apply, RingAut.mul_apply, ha _ h, ← RingAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, RingAut.one_apply]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]


omit [CharP R p] in
theorem exists_fixer_subset
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (U : Set G) (hU : IsOpen U) (hJU : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → g ∈ U) :
    ∃ m, 0 < m ∧ ∀ g ∈ fixer ρ p m, g ∈ U := by
  obtain ⟨⟨m, hm⟩, hmU⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2))
    (by
      rw [Set.disjoint_left]
      intro g hg hg'
      exact hg (hJU g fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))
    (by
      intro a b
      refine ⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg y hy => hg y ?_⟩
      have := pow_pow_mul hy a.1
      rwa [mul_comm] at this)
  refine ⟨m, hm, fun g hg => ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 hmU hc hg


omit [CharP R p] in
theorem exists_fixer_dvd
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → M g = 1) (k : ℕ) :
    ∃ m, 0 < m ∧ ∀ g ∈ fixer ρ p m, ∀ i j, (p : ℤ_[p]) ^ k ∣ (M g - 1) i j := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
    have := hp.out.pos
    positivity
  obtain ⟨m, hm, h⟩ := exists_fixer_subset ρ hopen
    (⋂ i, ⋂ j, {g | ‖(M g - 1) i j‖ < (p : ℝ) ^ (-(k : ℤ))})
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((hM.sub continuous_const).matrix_elem i j).norm continuous_const)
    (fun g hg => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => by
      change ‖(M g - 1) i j‖ < _
      rw [hJ g hg, sub_self, Matrix.zero_apply, norm_zero]
      exact hpos)
  refine ⟨m, hm, fun g hg i j => ?_⟩
  have h1 := Set.mem_iInter.1 (Set.mem_iInter.1 (h g hg) i) j
  exact Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (le_of_lt h1))

variable [PerfectRing R p]

omit [IsDomain R] in
theorem dvd_iff_constantCoeff (x : WittVector p R) :
    (p : WittVector p R) ∣ x ↔ WittVector.constantCoeff x = 0 := by
  rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  rfl


omit [IsDomain R] in
theorem isUnit_of_constantCoeff (x : WittVector p R) (hx : IsUnit (WittVector.constantCoeff x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have h1 : x * WittVector.teichmuller p y - 1 ∈ Ideal.span {(p : WittVector p R)} := by
    rw [Ideal.mem_span_singleton, dvd_iff_constantCoeff, map_sub, map_mul, map_one, sub_eq_zero, ← hy]
    rfl
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem exists_witt_matrix
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W := by
  have hfin : ∀ m, 0 < m → Finite (G ⧸ fixer ρ p m) := fun m hm =>
    Subgroup.quotient_finite_of_isOpen _ (isOpen_fixer ρ hopen hm)
  let c : WittVector p R →+* R := WittVector.constantCoeff
  have hc : ∀ g x, c (WittVector.map (ρ g).toRingHom x) = ρ g (c x) := fun g x => rfl
  have hz : ∀ z : ℤ_[p], c (zlW p R z) ^ p = c (zlW p R z) := fun z => by
    have := congrArg c (map_zlW p (frobenius R p) z)
    exact this
  obtain ⟨m, hm, h1⟩ := exists_fixer_dvd ρ hopen M hM hJ 1
  obtain ⟨W₁, hW₁, hW₁m, hW₁g⟩ := GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow p G R ρ m hm (hfin m hm) r
    ((c.comp (zlW p R)).mapMatrix.toMonoidHom.comp M)
    (fun g h i j => by
      change ρ g (c (zlW p R (M h i j))) = c (zlW p R (M h i j))
      rw [← hc, map_zlW])
    (fun h i j => by
      have := pow_pow_mul (p := p) (a := 1) (y := c (zlW p R (M h i j))) (by rw [pow_one, hz]) m
      rwa [one_mul] at this)
    (fun g hg => by
      change (c.comp (zlW p R)).mapMatrix (M g) = 1
      rw [← sub_eq_zero, ← map_one (c.comp (zlW p R)).mapMatrix, ← map_sub]
      ext i j
      obtain ⟨z, hz⟩ := h1 g hg i j
      change (c.comp (zlW p R)) ((M g - 1) i j) = 0
      rw [hz, map_mul, pow_one, map_natCast, CharP.cast_eq_zero, zero_mul])
  have hct : ∀ y : R, c (WittVector.teichmuller p y) = y := fun y => rfl
  obtain ⟨W, hW, hWg⟩ := GlobalTheory.T.exists_invariant_matrix_lift_of_adic_complete G (WittVector p R) p WittVector.isAdicCompleteIdealSpanP
    (fun g => WittVector.map (ρ g).toRingHom) (wittMap_mul ρ) (fun g => map_natCast _ _) r
    ((zlW p R).mapMatrix.toMonoidHom.comp M) (fun g h i j => map_zlW p _ _)
    {N | ∃ m, 0 < m ∧ N = fixer ρ p m}
    (by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨normal_fixer ρ p m, hfin m hm, GlobalTheory.T.exists_wittVector_trace_one_finiteLevel p G R ρ m hm (hfin m hm)⟩)
    (by
      rintro _ ⟨a, ha, rfl⟩ k
      obtain ⟨b, hb, h⟩ := exists_fixer_dvd ρ hopen M hM hJ k
      refine ⟨_, ⟨a * b, Nat.mul_pos ha hb, rfl⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg i j => ?_⟩
      have h2 := map_dvd (zlW p R) (h g (fun y hy => hg y (by
        have := pow_pow_mul hy a
        rwa [mul_comm] at this)) i j)
      rw [map_pow, map_natCast] at h2
      have h3 : (zlW p R).mapMatrix (M g - 1) = (zlW p R).mapMatrix (M g) - 1 := by
        rw [map_sub, map_one]
      exact (congrFun (congrFun h3 i) j) ▸ h2)
    (W₁.map (WittVector.teichmuller p))
    ⟨_, ⟨m, hm, rfl⟩, fun g hg => by
      ext i j : 1
      simp only [Matrix.map_apply, WittVector.map_teichmuller]
      exact congrArg _ (hg _ (hW₁m i j))⟩
    (fun g i j => by
      rw [dvd_iff_constantCoeff]
      have := congrFun (congrFun (hW₁g g) i) j

      rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]
      rw [Matrix.mul_apply] at this
      simp only [map_mul]
      exact this)
  refine ⟨W, isUnit_of_constantCoeff _ ?_, hWg⟩
  have h4 : c.mapMatrix W = W₁ := by
    ext i j
    have := (dvd_iff_constantCoeff _).1 (hW i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    exact this
  change IsUnit (c W.det)
  rw [RingHom.map_det, h4]
  exact hW₁

end Witt

theorem exists_matrixHom {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {L V : Type} [Field L] [Algebra ℚ_[l] L]
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] (ρ : Representation L G V)
    {n : ℕ} (e : Module.Basis (Fin n) ℚ_[l] V) (hint : ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1) :
    ∃ M : G →* Matrix (Fin n) (Fin n) ℤ_[l], ∀ g i j, ((M g i j : ℤ_[l]) : ℚ_[l]) = e.repr (ρ g (e j)) i := by
  refine ⟨{ toFun := fun g => Matrix.of fun i j => ⟨e.repr (ρ g (e j)) i, hint g i j⟩
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun _ _ _ => rfl⟩
  · ext i j
    change e.repr (ρ 1 (e j)) i = _
    rw [map_one, Module.End.one_apply, e.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm, PadicInt.coe_one]
    · rw [if_neg h, if_neg (Ne.symm h), PadicInt.coe_zero]
  · ext i j
    rw [Matrix.mul_apply, PadicInt.coe_sum]
    simp only [PadicInt.coe_mul]
    change e.repr (ρ (g * h) (e j)) i = ∑ k, e.repr (ρ g (e k)) i * e.repr (ρ h (e j)) k
    rw [map_mul, Module.End.mul_apply]
    conv_lhs => rw [← e.sum_repr (ρ h (e j))]
    have : ∀ (a : ℚ_[l]) v, ρ g (a • v) = a • ρ g v := fun a v => (ρ g).map_smul_of_tower _ _

    simp only [map_sum, this, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

theorem map_mul_map_eq {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') {n : ℕ}
    {M W : Matrix (Fin n) (Fin n) A} {M' : Matrix (Fin n) (Fin n) A'} {s : A → A} {s' : A' → A'}
    (h : M * W.map s = W) (hM : ∀ i j, f (M i j) = M' i j) (hs : ∀ a, f (s a) = s' (f a)) :
    M' * (W.map f).map s' = W.map f := by
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)

  rw [Matrix.mul_apply, map_sum] at this
  simp only [map_mul, hM, Matrix.map_apply, hs] at this
  exact this

theorem isCrys_and_jump_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ g ∈ IK K, ∀ x, T.ρ g x = x) → IsCrys (P.PD K) T.ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T.ρ τ a → a = 0 := by
  intro l _ P AI Ti K LL T hI
  have := compactSpace_GK K
  have := LL.2
  obtain ⟨n, e, he, hcont, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l (GK K) LL T
  have hint : ∀ g i j, ‖e.repr (T.ρ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 (T.L.stable g _ ((he _).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := exists_matrixHom T.ρ e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (continuous_apply i).comp (hcont.comp (T.cont (e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (T.ρ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  refine ⟨GlobalTheory.T.isCrys_of_split_alt (P.PD K) T.ρ e (AI.ιA.mapMatrix W) ?_ hB, ?_⟩
  · rw [← RingHom.map_det]
    exact hW.map _
  · let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
    have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
      change (P.PD K).ι (AI.ιA a) ∈ _
      rw [P.PD_ι]
      exact AI.ainf_image_mem_filtration_zero K a
    refine GlobalTheory.T.period_data_comparison (P.PD K) T.ρ e (f.mapMatrix W) (f.mapMatrix W⁻¹) ?_ (fun i j => hf _) (fun i j => hf _)
      fun g => ?_
    · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
    · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
          algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
      exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
        ((P.PD K).ι_comm g)

end GlobalTheory.UnramifiedRep
end
end
