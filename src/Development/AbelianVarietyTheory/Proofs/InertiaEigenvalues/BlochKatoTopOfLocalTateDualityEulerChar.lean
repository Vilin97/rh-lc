module

public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDiag
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocalStatement
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwistsStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatOfTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionRuleStmt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedLatticeCohomologyTheoremTOP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionSaturationUnramified

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a :=
  antitone_int_of_succ_le PD.Fil_anti h

theorem filV_anti {a b : ℤ} (h : a ≤ b) :
    FilV PD (LL := LL) (V := V) b ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    refine ⟨v ⊗ₜ ⟨(c : BdR), fil_anti PD h c.2⟩, ?_⟩
    simp
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem exists_mem_filV (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, v ⊗ₜ ⟨c, ha⟩, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem exists_DdRE_le_filV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ a, DdRE PD ρ τ ≤ FilV PD (LL := LL) (V := V) a := by
  have key : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s _ ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := exists_mem_filV PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact filV_anti PD (min_le_right a b) hb
      · exact filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ : (DdRE PD ρ τ).FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨a, ha⟩ := key s
  exact ⟨a, hs ▸ Submodule.span_le.mpr ha⟩

theorem finsum_multV_neg (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) := by
  obtain ⟨a₀, ha₀⟩ := exists_DdRE_le_filV PD ρ τ
  have hF : ∀ b ≤ a₀, FildR PD ρ τ b = DdRE PD ρ τ := fun b hb =>
    inf_eq_left.mpr (ha₀.trans (filV_anti PD hb))
  set N : ℕ := (-a₀).toNat with hN
  have hNa : -(N : ℤ) ≤ a₀ := by have := Int.self_le_toNat (-a₀); omega
  set f : ℤ → ℤ := fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ) with hf
  have hg : ∀ a, multV PD ρ τ a = f a - f (a + 1) := fun a => rfl
  have hzero : ∀ a, a < -(N : ℤ) → multV PD ρ τ a = 0 := by
    intro a ha
    have h1 := hF a (by omega)
    have h2 := hF (a + 1) (by omega)
    rw [multV, h1, h2, sub_self]
  let e : ℕ ↪ ℤ := ⟨fun i => -((i : ℤ) + 1), fun i j h => by
    have : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega⟩
  have he : ∀ i, e i = -((i : ℤ) + 1) := fun _ => rfl
  have hsum : ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ a ∈ (Finset.range N).map e, multV PD ρ τ a := by
    apply finsum_mem_eq_sum_of_inter_support_eq (s := Set.Iio (0 : ℤ))
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_map, Finset.coe_range,
      Set.mem_image, Set.mem_Iio, Function.mem_support, he]
    constructor
    · rintro ⟨ha, hs⟩
      refine ⟨⟨(-a - 1).toNat, ?_, ?_⟩, hs⟩
      · by_contra h; exact hs (hzero a (by omega))
      · omega
    · rintro ⟨⟨i, hi, rfl⟩, hs⟩
      exact ⟨by omega, hs⟩
  rw [hsum, Finset.sum_map]
  have hT := Finset.sum_range_sub (fun i : ℕ => f (-(i : ℤ))) N
  have h2 : ∀ i ∈ Finset.range N, multV PD ρ τ (e i) = f (-((i + 1 : ℕ) : ℤ)) - f (-(i : ℤ)) := by
    intro i _
    rw [hg, he]
    congr 2 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h2, hT]
  simp only [Nat.cast_zero, neg_zero, hf]
  rw [hF (-(N : ℤ)) hNa]

end Gen
end GlobalTheory.FiltrationJumpMultiplicity

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Sat
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem coboundary_mem_blochKatoCocycles (ρ : Representation LL G V) (hc : ∀ x, Continuous fun g => ρ g x) (x : V) :
    cob ρ x ∈ finiteCocycles PD ρ := by
  have hcob : ∀ g, cob ρ x g = ρ g x - x := fun g => rfl
  refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : (cob ρ x : G → V) = fun g => ρ g x + (-x) := funext fun g => by rw [hcob, sub_eq_add_neg]
    rw [this]
    exact (hc x).add continuous_const
  · simp only [hcob, map_mul, Module.End.mul_apply, map_sub]
    abel
  · rw [hcob, sub_tmul]
    simp [actVB]

theorem mem_H1fT_of_smul (ρ : Representation LL G V) (L : Lattice (O := O) ρ)
    (hc : ∀ x, Continuous fun g => ρ g x) (κ : LatticeCohomology L) (a : O) (ha : algebraMap O LL a ≠ 0)
    (h : a • κ ∈ latticeFiniteCohomology PD L) : κ ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  obtain ⟨c', hc', hq⟩ := h
  rw [← Submodule.Quotient.mk_smul] at hq
  have hq' := (Submodule.Quotient.eq _).mp hq
  obtain ⟨x, -, hx⟩ := hq'
  have hx' : (c' : G → V) - a • (c : G → V) = cob ρ x := by
    have h3 : ((latticeCocycles L).subtype (c' - a • c) : G → V) = (c' : G → V) - a • (c : G → V) := by simp
    rw [← h3, ← hx]; rfl
  have h1 : a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have : a • (c : G → V) = (c' : G → V) - cob ρ x := by rw [← hx']; abel
    rw [this]
    exact (finiteCocycles PD ρ).sub_mem hc'.2 (coboundary_mem_blochKatoCocycles PD ρ hc x)
  have h2 : (c : G → V) ∈ finiteCocycles PD ρ := by
    have e : a • (c : G → V) = algebraMap O LL a • (c : G → V) := (algebraMap_smul LL a _).symm
    rw [e] at h1
    have := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h1
    rwa [inv_smul_smul₀ ha] at this
  exact ⟨c, ⟨c.2, h2⟩, rfl⟩

end Sat

theorem blochKato_dimension_saturation_unramified : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm19 D := by
  intro D l _ K LL hA
  haveI := K.2
  haveI := LL.2
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ _ _ _ _ _ _ _ ρ hc hcrys
    letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have hBK := GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL
      (GlobalTheory.H1fGeneratorBoundAlt.splits_of_good hA.2.2) V ρ hc hcrys
    rw [hBK, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    haveI := ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL V ρ).1 τ).1
    exact (finsum_multV_neg _ ρ τ).symm
  · intro V _ _ _ _ _ _ _ _ _ _ _ ρ L hc _ κ a ha h
    refine mem_H1fT_of_smul _ ρ L hc κ a ?_ h
    intro h0
    exact ha (Subtype.ext h0)
  · exact GlobalTheory.T.unramified_trivial_local l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.FiltrationJumpMultiplicity
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLitAll

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.CrysFormalism

theorem crysLit_all : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm22 D := by
  intro D l _ K LL _
  have T := D.locT l
  refine ⟨?_, ?_, ?_⟩
  · intro μ a _ hμ hm
    refine ⟨GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l (D.loc l) (D.locA l) T K LL μ a hμ hm, ?_⟩
    intro V _ _ _ _ _ _ _ ρ ρ' _ hρ hρ'
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ']⟩
    obtain ⟨hc, hmult⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL
      V ρ V ρ' μ htw hμ hρ
    refine ⟨hc, fun τ b => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ (a τ) := by
      rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (D.loc l) (D.locA l) T K LL _ (charRep μ) τ (a τ)).2.2, hm]
      simp
    have := hmult τ (b - a τ) (a τ) hj
    rwa [sub_add_cancel] at this
  · intro V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ hι hπ hinj hsurj hex h1
    have h0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hinj h1
    have h2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hsurj h1).1
    have hdr := GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL V₁ ρ₁ h1
    refine ⟨h0, h2, fun τ a => ?_⟩
    exact ((GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π
      hι hπ hinj hsurj hex hdr.1).2.2 τ a).2.1
  · intro V _ _ _ _ _ _ _ ρ _ τ
    obtain ⟨h1, _⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) T K LL V ρ
    exact ⟨(h1 τ).1, (h1 τ).2.1⟩

end GlobalTheory.CrysFormalism
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeOfPowMem

section

@[expose] public section

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.EtaleExact TensorProduct

namespace GlobalTheory.EtaleSub

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)


include E in
theorem surjective_of_tie (hfl : Module.Flat O RW) {T' T : LocLat G Qp LL O}
    (hfix : ∀ b, TWmap φR T' b = b → ∃ t : ↥T'.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (hone : Function.Injective fun t : ↥T.L.T => (1 : RW) ⊗ₜ[O] t)
    (ι : LatHom T'.L T.L) (hι : Function.Injective ι.f) (m : ℕ) (hm : (m : LL) ≠ 0)
    (hall : ∀ x : W.DD T, ((m : ℕ) : W.EE) • x ∈ LinearMap.range (W.map ι)) :
    Function.Surjective ι.f := by
  have hU := span_range_map E ι
  have hkill : ∀ y : TW RW T, m • y ∈ LinearMap.range ((latMap ι).baseChange RW) := by
    intro y
    have hy : y ∈ Submodule.span RW (Set.range (E.jD T)) := by
      rw [E.jD_span T]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← hU]
      refine Submodule.subset_span ⟨_, hall x, ?_⟩
      rw [E.jD_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add z w _ _ hz hw => rw [smul_add]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  have hinj : Function.Injective ((latMap ι).baseChange RW) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := RW) (latMap ι)
      (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
  have hcomm : ∀ c : TW RW T', (latMap ι).baseChange RW (TWmap φR T' c) =
      TWmap φR T ((latMap ι).baseChange RW c) := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul r t => simp [TWmap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ t : ↥T.L.T, ∃ t' : ↥T'.L.T, latMap ι t' = m • t := by
    intro t
    obtain ⟨c, hc⟩ := hkill ((1 : RW) ⊗ₜ[O] t)
    rw [← TensorProduct.tmul_smul] at hc
    have hf : TWmap φR T' c = c := by
      apply hinj
      rw [hcomm, hc]
      simp [TWmap]
    obtain ⟨t', rfl⟩ := hfix c hf
    refine ⟨t', hone ?_⟩
    simpa using hc
  have hle : (T.L.T : Set T.V) ⊆ (LinearMap.range ι.f : Submodule LL T.V) := by
    intro t ht
    obtain ⟨t', h'⟩ := h2 ⟨t, ht⟩
    refine ⟨(m : LL)⁻¹ • (t' : T'.V), ?_⟩
    have h3 : ι.f (t' : T'.V) = m • t := congrArg Subtype.val h'
    rw [map_smul, h3, ← Nat.cast_smul_eq_nsmul LL, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have htop : LinearMap.range ι.f = ⊤ :=
    top_le_iff.1 (T.L.span ▸ Submodule.span_le.2 hle)
  exact LinearMap.range_eq_top.1 htop

end Generic

theorem exists_lattice_of_pow_mem : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitSub D HW F := by
  intro D HW F l _ K LL hA T D' hpow hφ hγ
  obtain ⟨T', ι, hι, hr⟩ := exists_sublattice (D.locA l) (HW l) (F l) K 1 LL hA.2.2 T D' hφ hγ
  obtain ⟨a, ha⟩ := hpow
  refine ⟨T', ι, ⟨hι, ?_⟩, hr⟩
  haveI := flat_RW LL
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hp : (((D.loc l).PD K).p : ℕ) = l := (D.loc l).PD_p K
  refine surjective_of_tie ((F l).E K 1 LL hA.2.2).tie (flat_RW LL)
    (fun b hb => ((GlobalTheory.WittTensorFixed.main l K LL T').2.1 b).1 hb)
    (GlobalTheory.WittTensorFixed.main l K LL T).2.2 ι hι (l ^ a) ?_ ?_
  · exact_mod_cast pow_ne_zero a (Fact.out : l.Prime).ne_zero
  · intro x
    rw [hr]
    have := ha x
    rw [hp] at this
    simpa using this

end GlobalTheory.EtaleSub
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHoldsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.invariants_statement_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.H0InvariantsTheorem D HW F := by
  first | exact @GlobalTheory.invariants_of_field_of_norms | exact GlobalTheory.invariants_of_field_of_norms | (intros; apply GlobalTheory.invariants_of_field_of_norms <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TopClosing

theorem blochKatoTop_of_localTateDuality_eulerChar_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  intro _ hdual heul D HW F Cm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -, hE⟩ :
      Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨a23, a24⟩ := tableLineDegreeTwo.ainf_clauses_of_theorem D HW F hE
  have hA : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  have hFN : Formalism.MainNotions.HerrComplexNaturality.FN D HW F := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have a16 : tableLineDegreeTwo.adm16 D HW F :=
    Formalism.MainNotions.InvariantsGenerators.herr_lattice_of_fon D HW F ⟨hA, GlobalTheory.T.invariants_statement_holds D HW F hFN, GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F⟩
  have a17 : tableLineDegreeTwo.adm17 D HW F :=
    (Formalism.MainNotions.InvariantsGenerators.herr_lattice_rest_iff D HW F).2
      ⟨GlobalTheory.EtaleSub.exists_lattice_of_pow_mem D HW F, GlobalTheory.ExtDict.extension_rule D HW F⟩
  have a21 : tableLineDegreeTwo.adm21 D HW F := GlobalTheory.SenMult.stmtSen D HW F Cm ⟨a2, a4, a5, a9, a11⟩
  exact GlobalTheory.TopBridge.twistedLatticeCohomology_theoremTOP D HW F Cm
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ⟨hdual, heul⟩,
      GlobalTheory.FiltrationJumpMultiplicity.blochKato_dimension_saturation_unramified D, GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists D HW F, a21, GlobalTheory.CrysFormalism.crysLit_all D, a23, a24⟩

end GlobalTheory.TopClosing
end
end
