module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatumStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDual

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.BlochKatoDuality.Br

namespace GlobalTheory.TatePair

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

theorem cup_coboundary_right (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) (hc : (c : G → A'.V ⧸ LA'.T) ∈ BD LA') :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hcg : ∀ h, (c : G → A'.V ⧸ LA'.T) h =
      repD LA' h (Submodule.Quotient.mk v) - Submodule.Quotient.mk v := fun h =>
    (congrFun hw h).symm
  have hT : IsOpen (L1.T : Set LL) := integers_isOpen PD L1 hL1 hopen
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  have hlc : IsLocallyConstant fun g : G =>
      -(Submodule.Quotient.mk (P ((d : G → A.V) g) (A'.ρ g v)) : LL ⧸ L1.T) :=
    (locConst_mk L1.T hT _ hcont).neg
  refine ⟨fun g => -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d),
    ⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  show repD L1 g (-torsionPairing PD hd L1 hL1 (repD LA' h (Submodule.Quotient.mk v)) (evT LA h d))
      - -torsionPairing PD hd L1 hL1 (repD LA' (g * h) (Submodule.Quotient.mk v)) (evT LA (g * h) d)
      + -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d) =
    cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt]
  simp only [hcg, map_neg, ← torsionPairing_equivariant, lattice_cocycle_mul, map_mul, Module.End.mul_apply, map_add (f := _),
    map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Gen

theorem integral_pairing : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
      (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m →
    ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T),
      (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧
      (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd
  obtain ⟨e⟩ := GlobalTheory.T.tate_H2_period_datum hT l P K LL O hG L1 hL1
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  obtain ⟨pr, hpr⟩ := exists_pr (P.PD K) hopen hd L1 hL1
  refine ⟨(pr.compr₂ e.toLinearMap).flip ∘ₗ Submodule.mkQ _, ?_, ?_, ?_⟩
  · intro d c
    show e (pr c (Submodule.Quotient.mk d)) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact hpr c d
  · intro d c hdB
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_mem_coboundaries (P.PD K) hd L1 hL1 c d hdB
  · intro d c hc
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_coboundary_right (P.PD K) hd L1 hL1 hopen c d hc

end GlobalTheory.TatePair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDualStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.integral_tate_pairing_lattice_dual : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T), (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧ (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  first | exact @GlobalTheory.TatePair.integral_pairing | exact GlobalTheory.TatePair.integral_pairing | (intros; apply GlobalTheory.TatePair.integral_pairing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomicStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_dual_pairing_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  first | exact @GlobalTheory.TateOrth.mem_BD_of_orthogonal | exact GlobalTheory.TateOrth.mem_BD_of_orthogonal | (intros; apply GlobalTheory.TateOrth.mem_BD_of_orthogonal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModIntegerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O M] (β : M →ₗ[O] N →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL))) (S : Submodule O N), (∀ c, (∀ d, β d c = 0) → c ∈ S) → ∀ c, (∀ d, (∀ s ∈ S, β d s = 0) → β d c = 0) → c ∈ S := by
  first | exact @GlobalTheory.mem_of_forall_annihilator_annihilator | exact GlobalTheory.mem_of_forall_annihilator_annihilator | (intros; apply GlobalTheory.mem_of_forall_annihilator_annihilator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tate_double_annihilator : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdual S hBS hSZ c hc hann
  obtain ⟨β, hβ0, hβB, -⟩ := GlobalTheory.T.integral_tate_pairing_lattice_dual hT l P K LL O hO L1 hL1 A A' LA LA' m hdual
  haveI : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hT l P K LL O hO A LA
  let e : (LL ⧸ L1.T) ≃ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    Submodule.quotEquivOfEq _ _ hL1
  let β₁ : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    β.compr₂ e.toLinearMap
  have hβ₁ : ∀ d c, β₁ d c = 0 ↔ β d c = 0 := fun d c => by
    simp only [β₁, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.map_eq_zero_iff
  have hker : (latticeCoboundaries LA).comap (latticeCocycles LA).subtype ≤ LinearMap.ker β₁ := by
    intro d hd
    rw [LinearMap.mem_ker]
    ext c
    exact (hβ₁ d c).2 (hβB d c hd)
  let β₂ : LatticeCohomology LA →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype).liftQ β₁ hker
  have hβ₂ : ∀ d c, β₂ (Submodule.Quotient.mk d) c = β₁ d c := fun d c => rfl
  have key := GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers l LL O hO (LatticeCohomology LA) ↥(divisibleCocycles LA') β₂ (S.comap (divisibleCocycles LA').subtype) ?_
    ⟨c, hc⟩ ?_
  · exact key
  · intro c' hc'
    show c'.1 ∈ S
    apply hBS
    apply GlobalTheory.T.lattice_dual_pairing_cyclotomic hT l P K LL O hO L1 hL1 A A' LA LA' m hdual c'.1 c'.2
    intro d hd
    have h := hc' (Submodule.Quotient.mk ⟨d, hd⟩)
    rw [hβ₂, hβ₁] at h
    exact (hβ0 ⟨d, hd⟩ c').1 h
  · intro d hd
    induction d using Submodule.Quotient.induction_on with
    | _ d0 =>
    rw [hβ₂, hβ₁]
    apply (hβ0 d0 ⟨c, hc⟩).2
    apply hann d0.1 d0.2
    intro s hs
    have h := hd ⟨s, hSZ hs⟩ hs
    rw [hβ₂, hβ₁] at h
    exact (hβ0 d0 ⟨s, hSZ hs⟩).1 h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_dual_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  first | exact @GlobalTheory.tate_double_annihilator | exact GlobalTheory.tate_double_annihilator | (intros; apply GlobalTheory.tate_double_annihilator <;> assumption)
end
end
