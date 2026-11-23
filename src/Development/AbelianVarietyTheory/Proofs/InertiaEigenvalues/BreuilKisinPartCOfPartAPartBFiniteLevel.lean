module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoQuotientOfDivisibleImageMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoReductionsOrthogonalModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupDivisibleImageCoboundaryIffFiniteLevelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLevelCupSwapCoboundaryIffStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAl

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAlStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  first | exact @GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | exact GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | (intros; apply GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocycles

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevelCocycle

theorem ioL_actQ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (g : G)
    (x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    GlobalTheory.BKFinLevel.ioL L ϖ r (actQ L _ hI g x) = actD L g (GlobalTheory.BKFinLevel.ioL L ϖ r x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [actQ, Submodule.mapQ_apply, GlobalTheory.BKFinLevel.ioL_mk, actD, actT]
    congr 1
    simp only [LinearMap.coe_restrictScalars, map_smul]
    rfl

theorem ioL_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ r hI c hc
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  simp only [hc.2 g h, map_add (f := _), ioL_actQ]

end GlobalTheory.BKFinLevelCocycle
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocyclesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  first | exact @GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | exact GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | (intros; apply GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocyclesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  first | exact @GlobalTheory.RedLocConst.redT_mem_Z1Q | exact GlobalTheory.RedLocConst.redT_mem_Z1Q | (intros; apply GlobalTheory.RedLocConst.redT_mem_Z1Q <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReduction

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKTorsionRed

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {ρ : Representation LL G V}

theorem coboundary_mem_blochKato_cocycles (m : V) (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

def latticeCoboundaryCocycle (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) : ↥(latticeCocycles L) :=
  ⟨fun g => ρ g x - x, Submodule.mem_inf.2 ⟨(coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)).1,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩⟩

theorem lattice_reduction_coboundary_mem_cocycles (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (x : ↥L.T) :
    redT L I (latticeCoboundaryCocycle PD L hρ x) = LinearMap.pi (fun g => actQ L I hI g - LinearMap.id) (I.mkQ x) := by
  funext g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mkQ_apply, actQ,
    Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rfl

theorem mem_HfQ_iff (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ a : ↥(latticeCocycles L), (a : G → V) ∈ finiteCocycles PD ρ ∧ c = redT L I a := by
  constructor
  · intro h
    obtain ⟨_, ⟨a0, ha0, rfl⟩, _, ⟨xb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨a0 + latticeCoboundaryCocycle PD L hρ x, (finiteCocycles PD ρ).add_mem ha0.2 (coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)), ?_⟩
    rw [map_add (f := _), lattice_reduction_coboundary_mem_cocycles PD L hρ I hI x]
    rfl
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.mem_sup_left ⟨a, ⟨a.2, ha⟩, rfl⟩

theorem mem_HfQ_iff_red : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  intro l _ P K LL _ _ _ O _ _ _hO A LA ϖ r hI c
  exact mem_HfQ_iff (P.PD K) LA A.cont _ hI c

end GlobalTheory.BKTorsionRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlochKatoQuotientPowIffReductionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  first | exact @GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | exact GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | (intros; apply GlobalTheory.BKTorsionRed.mem_HfQ_iff_red <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevel

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevel

theorem bkC_of_bkA_bkB : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  intro hT _ l _ P _ _ K hA hB LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ hϖ r hI hI'
  show (∀ c ∈ quotientCocycles LA _ hI, (c ∈ HfQ (P.PD K) LA _ hI ↔ ∀ c' ∈ HfQ (P.PD K) LA' _ hI',
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c'))) ∧
    (∀ c' ∈ quotientCocycles LA' _ hI', (c' ∈ HfQ (P.PD K) LA' _ hI' ↔ ∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')))
  have orth := GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow l P K hA LL O hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI'

  have hfz : ∀ s ∈ HfQ (P.PD K) LA _ hI, s ∈ quotientCocycles LA _ hI := by
    intro s hs
    obtain ⟨a, -, has⟩ := (GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI s).1 hs
    rw [has]
    exact GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A LA ϖ hϖ r hI a

  have clause2 : ∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')) → c' ∈ HfQ (P.PD K) LA' _ hI' := by
    intro c' hc' horth
    apply GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A' LA' ϖ hϖ r hI' c'
    have hZ := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A' LA' ϖ r hI' c' hc'
    refine ((hB LL O hO L1 hL1 A A' LA LA' m hDR hd).1 _ hZ).2 ?_
    intro d hdf
    have hdT : d ∈ latticeCocycles LA := hdf.1
    rw [GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r ⟨d, hdT⟩ c']
    exact horth _ ((GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI _).2 ⟨⟨d, hdT⟩, hdf.2, rfl⟩)
  refine ⟨fun c hc => ⟨fun h c' hc' => orth c h c' hc', fun h => ?_⟩,
    fun c' hc' => ⟨fun h c hc => orth c hc c' h, clause2 c' hc'⟩⟩

  let S : Submodule O (↥(GK K) → A.V ⧸ LA.T) :=
    (HfQ (P.PD K) LA _ hI).map ((GlobalTheory.BKFinLevel.ioL LA ϖ r).compLeft ↥(GK K)) ⊔ BD LA
  have hS1 : BD LA ≤ S := le_sup_right
  have hS2 : S ≤ divisibleCocycles LA := by
    refine sup_le ?_ (GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' l P K LL O hO A LA)
    rintro _ ⟨s, hs, rfl⟩
    exact GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI s (hfz s hs)
  have hflip : IsDualLat1 (P.PD K) LA' LA m.flip := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, htr, -⟩ := id hO
    exact Formalism.MainNotions.BlochKatoDuality.Br.isDualLat1_flip (P.PD K) hd
  have hC := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI c hc
  have key := GlobalTheory.T.lattice_dual_cyclotomic hT l P K LL O hO L1 hL1 A' A LA' LA m.flip hflip S hS1 hS2 _ hC (by
    intro d hdZ hdS
    rw [← GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI c hc ⟨d, hdZ⟩]
    apply h
    apply clause2 _ (GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A' LA' ϖ hϖ r hI' ⟨d, hdZ⟩)
    intro s hs
    rw [GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI s (hfz s hs) ⟨d, hdZ⟩]
    exact hdS _ (Submodule.mem_sup_left ⟨s, hs, rfl⟩))
  obtain ⟨y, ⟨a, ha, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 key
  have hdiff : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) ∈ HfD (P.PD K) LA := by
    have : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) = z := by
      funext g
      have := congrFun hyz g
      simp only [Pi.sub_apply, map_sub, LinearMap.compLeft_apply, Function.comp_apply,
        Pi.add_apply] at this ⊢
      rw [← this]; abel
    rw [this]
    exact Submodule.mem_sup_right hz
  have := GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A LA ϖ hϖ r hI _ hdiff
  simpa using (HfQ (P.PD K) LA _ hI).add_mem this ha

end GlobalTheory.BKFinLevel
end
end
