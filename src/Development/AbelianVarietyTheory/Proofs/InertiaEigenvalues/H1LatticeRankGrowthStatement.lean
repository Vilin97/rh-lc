module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
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
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.Localization.Finiteness

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModuleStatement

section

@[expose] public section

open Module

theorem _root_.GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t → (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤ C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  first | exact @GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | exact GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | (intros; apply GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomain

section

@[expose] public section

open Module

namespace GlobalTheory

theorem card_quot_span_pow_succ_eq_mul_domain (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by
  set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH
  set K := (Ideal.span {t ^ r}).toAddSubgroup with hK
  have hHK : H ≤ K := by
    intro x hx
    simp only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow t (Nat.le_succ r)).trans hx
  have e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index := rfl
  have e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index := rfl
  have e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index := rfl
  rw [e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]
  congr 1
  let φ : O →+ K :=
    { toFun := fun x => ⟨t ^ r * x, by
        simp only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span {t ^ r} := hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨a, rfl⟩
  have hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    change t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x
    rw [pow_succ]
    exact mul_dvd_mul_iff_left (pow_ne_zero r ht)
  rw [AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]

theorem card_quot_span_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) →
      ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  intro O _ _ t ht _ r
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    rw [card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomainStatement

section

@[expose] public section

open Module

theorem _root_.GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  first | exact @GlobalTheory.card_quot_span_pow | exact GlobalTheory.card_quot_span_pow | (intros; apply GlobalTheory.card_quot_span_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFinrankOfLocalizes

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (x : A.V), ∃ n : ℕ, ((l : ℕ) : O) ^ n • x ∈ LA.T := by
  intro l _ K LL _ _ _ O _ _ hG A LA x
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  haveI := IsModuleTopology.toContinuousSMul LL A.V
  have h1 : Filter.Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have h2 : Filter.Tendsto (fun n : ℕ => algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x) Filter.atTop (nhds 0) := by
    have := ((GlobalTheory.GoodCoeff.continuous_algebraMap_padic (l := l) (LL := LL)).tendsto 0).comp h1
    rw [map_zero] at this
    simpa using this.smul_const x
  have h3 : ∀ n : ℕ, ((l : ℕ) : O) ^ n • x = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x := by
    intro n
    rw [← algebraMap_smul LL, map_pow, map_pow, map_natCast, map_natCast]
  obtain ⟨n, hn⟩ := (h2.eventually (hT.mem_nhds LA.T.zero_mem)).exists
  exact ⟨n, by rw [h3]; exact hn⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem not_isUnit_l : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ¬ IsUnit ((l : ℕ) : O) := by
  intro l _ LL _ _ _ O _ _ hG hu
  obtain ⟨u, hu⟩ := hu
  have hint := ((GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).1 (algebraMap O LL (↑u⁻¹ : O))).1 ⟨_, rfl⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hx : algebraMap O LL (↑u⁻¹ : O) = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by
    have h1 : algebraMap O LL (↑u⁻¹ : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap O LL (u : O) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by
      rw [hu, map_natCast, map_natCast]
    rw [h2] at h1
    calc algebraMap O LL (↑u⁻¹ : O)
        = algebraMap O LL (↑u⁻¹ : O) * (algebraMap ℚ_[l] LL (l : ℚ_[l]) * algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹)) := by
          rw [← map_mul, mul_inv_cancel₀ hl0, map_one, mul_one]
      _ = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by rw [← mul_assoc, h1, one_mul]
  rw [hx] at hint
  obtain ⟨p, hpm, hp⟩ := hint
  have hp' : Polynomial.eval₂ (algebraMap ℤ_[l] ℚ_[l]) ((l : ℚ_[l])⁻¹) p = 0 := by
    apply (algebraMap ℚ_[l] LL).injective
    rw [map_zero, Polynomial.hom_eval₂]
    exact hp
  have hI : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have h1 : ‖(z : ℚ_[l])‖ ≤ 1 := PadicInt.norm_le_one z
  have h3 : algebraMap ℤ_[l] ℚ_[l] z = (z : ℚ_[l]) := rfl
  rw [← h3, hz, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem finite_finrank_of_localizes : ∀ (O LL M N : Type) [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup M] [Module O M] [Module.Finite O M] [AddCommGroup N] [Module LL N] [Module O N] [IsScalarTower O LL N] (f : M →ₗ[O] N) (t : O), t ≠ 0 → (∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) → (∀ x : M, f x = 0 → ∃ n : ℕ, t ^ n • x = 0) → Module.Finite LL N ∧ finrank LL N = finrank O M := by
  intro O LL M N _ _ _ _ _ _ _ _ _ _ _ _ f t ht hs hk
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors O := fun n => pow_mem (mem_nonZeroDivisors_of_ne_zero ht) n
  haveI : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        have ha : algebraMap O LL (s : O) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (nonZeroDivisors.ne_zero s.2)
        have he : ∀ y : N, (algebraMap O (Module.End O N) (s : O)) y = algebraMap O LL (s : O) • y := fun y => by
          rw [Module.algebraMap_end_apply, algebraMap_smul]
        refine ⟨fun y z h => ?_, fun y => ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩⟩
        · rw [he, he] at h
          exact smul_right_injective N ha h
        · rw [he, smul_smul, mul_inv_cancel₀ ha, one_smul]
      surj := by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        exact ⟨(x, ⟨t ^ n, htn n⟩), hx.symm⟩
      exists_of_eq := by
        intro x₁ x₂ h
        obtain ⟨n, hn⟩ := hk (x₁ - x₂) (by rw [map_sub, h, sub_self])
        exact ⟨⟨t ^ n, htn n⟩, by rw [Submonoid.smul_def]; rw [smul_sub, sub_eq_zero] at hn; exact hn⟩ }
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) f, ?_⟩
  rw [IsLocalization.finrank_eq LL (nonZeroDivisors O) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_B1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ latticeCocycles LA, c ∈ B1 A.ρ → ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCoboundaries LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c _ hc
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨n, hn⟩ := pow_smul_mem_lattice l K LL O hG A LA x
  exact ⟨n, _, hn, by rw [LinearMap.map_smul_of_tower]; rfl⟩

theorem pow_smul_mem_Z1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ continuousCocycles A.ρ, ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCocycles LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c hc
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  have hG' := hG
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG'
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  let U : ℕ → Set A.V := fun n => (fun v : A.V => ((l : ℕ) : O) ^ n • v) ⁻¹' (LA.T : Set A.V)
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    refine hT.preimage ?_
    have : (fun v : A.V => ((l : ℕ) : O) ^ n • v) = fun v : A.V => algebraMap O LL (((l : ℕ) : O) ^ n) • v :=
      funext fun v => (algebraMap_smul LL _ v).symm
    rw [this]
    exact continuous_const_smul _
  have hUm : Monotone U := by
    refine monotone_nat_of_le_succ fun n v hv => ?_
    show ((l : ℕ) : O) ^ (n + 1) • v ∈ LA.T
    rw [pow_succ', mul_smul]
    exact LA.T.smul_mem _ hv
  have hcov : Set.range c ⊆ ⋃ n, U n := fun v _ => Set.mem_iUnion.2 (pow_smul_mem_lattice l K LL O hG A LA v)
  obtain ⟨n, hn⟩ := (isCompact_range hc.1).elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨n, ⟨(continuousCocycles A.ρ).smul_of_tower_mem _ hc, fun g _ => hn ⟨g, rfl⟩⟩⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank
section
variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A : GRep ↥(GK K) ℚ_[l] LL O} (LA : Lattice (O := O) A.ρ)

def incl : ↥(latticeCocycles LA) →ₗ[O] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def toH1V : LatticeCohomology LA →ₗ[O] H1V A.ρ :=
  Submodule.liftQ ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype)
    ((((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ.restrictScalars O).comp (incl LA)) (by
      intro c hc
      obtain ⟨x, -, hx⟩ := hc
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, hx⟩)

theorem toH1V_mk (c : ↥(latticeCocycles LA)) :
    toH1V LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incl LA c) := rfl
end
end GlobalTheory.H1Rank
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowth

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowthStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.H1_lattice_rank_growth_of_goodO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  first | exact @GlobalTheory.H1Rank.growth_H1T_dim_H1V | exact GlobalTheory.H1Rank.growth_H1T_dim_H1V | (intros; apply GlobalTheory.H1Rank.growth_H1T_dim_H1V <;> assumption)
end
end
