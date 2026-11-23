module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotientsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLattice
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
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1EqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePowStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_cyclotomic_integral_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  first | exact @GlobalTheory.CycIntegral.cyc_lattice | exact GlobalTheory.CycIntegral.cyc_lattice | (intros; apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotient

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_finset_pow_torsion : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  intro l _ LL _ _ _ O _ _ hG k
  classical
  haveI hfin : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ k}) :=
    (good_coeff_integers l LL O hG).2.2.1 k
  have hl : (l : LL) ≠ 0 := by
    have := (algebraMap ℚ_[l] LL).injective.ne
      (show (l : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using this
  have hlk : (l : LL) ^ k ≠ 0 := pow_ne_zero _ hl
  let f : O ⧸ Ideal.span {((l : ℕ) : O) ^ k} → LL ⧸ LinearMap.range (Algebra.linearMap O LL) :=
    fun q => Submodule.Quotient.mk (((l : LL) ^ k)⁻¹ * algebraMap O LL q.out)
  refine ⟨(Set.finite_range f).toFinset, fun e he => ?_⟩
  rw [Set.Finite.mem_toFinset]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at he
  obtain ⟨a, ha⟩ := he
  rw [Algebra.linearMap_apply, Algebra.smul_def, map_pow, map_natCast] at ha
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have h1 : (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : O) ^ k}) a).out - a ∈
      Ideal.span {((l : ℕ) : O) ^ k} :=
    Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have hc' := congrArg (algebraMap O LL) hc
  rw [map_mul, map_pow, map_natCast, RingHom.map_sub, ha] at hc'
  refine (Submodule.Quotient.eq _).2 ⟨c, ?_⟩
  rw [Algebra.linearMap_apply]
  field_simp
  linear_combination hc'

end GlobalTheory.GoodCoeff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotientStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_finset_primePow_torsion_quotient : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  first | exact @GlobalTheory.GoodCoeff.exists_finset_pow_torsion | exact GlobalTheory.GoodCoeff.exists_finset_pow_torsion | (intros; apply GlobalTheory.GoodCoeff.exists_finset_pow_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1Reduction

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem finite_H1Q_lpow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA r hI
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hrest⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl : ((l : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h0, map_zero]
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] LL)] at h1
    have h2 : ((l : ℕ) : ℚ_[l]) = 0 := (algebraMap ℚ_[l] LL).injective (by rw [h1, map_zero])
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero r hl) hϖ
  have hspan : Ideal.span {((l : ℕ) : O) ^ r} = Ideal.span {ϖ ^ m} :=
    Ideal.span_singleton_eq_span_singleton.2 hm
  have key : ∀ (I : Submodule O ↥LA.T) (hI' : StableSub LA I),
      I = (Ideal.span {ϖ ^ m} • ⊤ : Submodule O ↥LA.T) → Finite (QuotientCohomology LA I hI') := by
    rintro I hI' rfl
    have hZ := finite_Z1Q hT l K LL O hO A LA ϖ hϖ m hI'
    have : Finite ↥(quotientCocycles LA _ hI') := hZ.to_subtype
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact key _ hI (by rw [hspan])

end GlobalTheory.CocycleModPow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1ReductionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_H1_reduction : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  first | exact @GlobalTheory.CocycleModPow.finite_H1Q_lpow | exact GlobalTheory.CocycleModPow.finite_H1Q_lpow | (intros; apply GlobalTheory.CocycleModPow.finite_H1Q_lpow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocycles

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DivLift

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mk_inv_smul_liftQ (L : Lattice (O := O) ρ) (a : O) (ha : algebraMap O LL a ≠ 0)
    (y : ↥L.T) :
    (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y)) : V ⧸ L.T) =
      Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (y : V)) := by
  obtain ⟨y0, hy0, hs⟩ : ∃ y0 : ↥L.T, (y0 : V) = Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y) ∧
      (Submodule.Quotient.mk y0 : ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) =
        Submodule.Quotient.mk y :=
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk y)).choose_spec⟩
  rw [← hy0]
  have hmem := (Submodule.Quotient.eq _).1 hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  have ht' : a • (t : V) = (y0 : V) - (y : V) := congrArg Subtype.val ht
  rw [Submodule.Quotient.eq, ← smul_sub, ← ht', ← algebraMap_smul LL a, smul_smul,
    inv_mul_cancel₀ ha, one_smul]
  exact t.2

theorem inv_smul_liftQ_mem_Z1D [TopologicalSpace G] (L : Lattice (O := O) ρ) (a : O)
    (ha : algebraMap O LL a ≠ 0) (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T))
    (c : G → ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (hc : c ∈ quotientCocycles L _ hI) :
    (fun g => (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) :
      V ⧸ L.T)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (fun x => (Submodule.Quotient.mk
    ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ x) : V ⧸ L.T)), fun g h => ?_⟩
  have hgh := hc.2 g h
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have h1 : c (g * h) = Submodule.Quotient.mk (x + actT L g y) := by
    rw [hgh, ← hx, ← hy]; rfl
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + actD L g (Submodule.Quotient.mk _)
  rw [h1, ← hx, ← hy, mk_inv_smul_liftQ L a ha, mk_inv_smul_liftQ L a ha,
    mk_inv_smul_liftQ L a ha]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (ρ g ((algebraMap O LL a)⁻¹ • (y : V)))
  rw [← Submodule.Quotient.mk_add, map_smul, ← smul_add]
  rfl

end Gen

theorem pow_inv_smul_liftQ_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  intro l _ K LL _ _ _ O _ _ _ A' LA' r hI' c'
  have he : algebraMap O LL (((l : ℕ) : O) ^ r) = ((l : ℕ) : LL) ^ r := by
    rw [map_pow, map_natCast]
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have := inv_smul_liftQ_mem_Z1D LA' (((l : ℕ) : O) ^ r) (by rw [he]; exact pow_ne_zero _ hl)
    hI' c'.1 c'.2
  rwa [he] at this

end GlobalTheory.DivLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocyclesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  first | exact @GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | exact GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | (intros; apply GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDual

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BoundedIndex



theorem h1_reduction_index_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' LA LA' m hm
  obtain ⟨L1, hL1⟩ := GlobalTheory.T.exists_cyclotomic_integral_lattice l P K LL O hO
  obtain ⟨C0, k0, hF⟩ := GlobalTheory.T.bounded_finite_cohomology_quotients hT l P K LL O hO A' LA'
  obtain ⟨Es, hEs⟩ := GlobalTheory.T.exists_finset_primePow_torsion_quotient l LL O hO k0
  have hEs1 : 1 ≤ Es.card := Finset.card_pos.2 ⟨0, hEs 0 (smul_zero _)⟩
  refine ⟨Es.card ^ C0, pow_pos hEs1 _, fun r hI => ?_⟩
  have hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) :=
    GlobalTheory.TateOrth.stable_span_smul_top LA' _
  haveI hX := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A LA r hI
  haveI hY := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A' LA' r hI'
  haveI : Module.Finite O (QuotientCohomology LA' _ hI') := Module.Finite.of_finite
  obtain ⟨f, hker, hf⟩ := GlobalTheory.T.ker_reduction_H1_eq l P K LL O hO A LA r hI
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.tate_pairing_lattice_level_primePow hT l P K LL O hO L1 hL1 A A' LA LA' m hm r hI hI'
  obtain ⟨F, hFc, hFm⟩ := hF r hI'
  have hcardS : Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) =
      Nat.card (LinearMap.range f) := by
    have key : ∀ N : Submodule O (LatticeCohomology LA), LinearMap.ker f = N → Nat.card (LatticeCohomology LA ⧸ N) = Nat.card (LinearMap.range f) := by
      rintro N rfl
      exact Nat.card_congr f.quotKerEquivRange.toEquiv
    exact key _ hker
  rw [hcardS]
  refine ⟨Nat.card_le_card_of_injective _ Subtype.val_injective, ?_⟩
  have hdd : ∀ c, (∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → β y c = 0) → c ∈ LinearMap.range f :=
    GlobalTheory.mem_of_forall_annihilator_annihilator l LL O hO _ _ β (LinearMap.range f)
      (fun c hc => by rw [hβ1 c hc]; exact Submodule.zero_mem _)
  have hA : ∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → y ∈ F ∧ ((l : ℕ) : O) ^ k0 • y = 0 := by
    intro y hy
    obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hFm c'
    refine GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m hm _
      (GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles l K LL O hO A' LA' r hI' c') fun d hd => ?_
    obtain ⟨h, hfd⟩ := hf ⟨d, hd⟩
    have h0 : β (Submodule.Quotient.mk c') (f (Submodule.Quotient.mk ⟨d, hd⟩)) = 0 := hy _ ⟨_, rfl⟩
    exact hβ2 ⟨d, hd⟩ h c' ((congrArg (β (Submodule.Quotient.mk c')) hfd).symm.trans h0)
  calc Nat.card (QuotientCohomology LA _ hI) ≤ Es.card ^ F.card * Nat.card (LinearMap.range f) :=
        GlobalTheory.T.card_le_of_double_annihilator_pairing O _ _ _ β (LinearMap.range f) F Es _ hdd hA hEs
    _ ≤ Es.card ^ C0 * Nat.card (LinearMap.range f) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hEs1 hFc)

end GlobalTheory.BoundedIndex
end
end
