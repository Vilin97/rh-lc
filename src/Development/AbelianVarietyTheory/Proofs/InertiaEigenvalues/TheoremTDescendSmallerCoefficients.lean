module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtensStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtens
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientFieldStatement
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocal

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem lattice_basis_exists : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  intro l _ G _ _ LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI hfr : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI := T.L.free
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let e0 := Module.Free.chooseBasis ↥(OL LL) ↥T.L.T
  let e := e0.reindex (Fintype.equivFin _)
  let v : Fin (Fintype.card (Module.Free.ChooseBasisIndex ↥(OL LL) ↥T.L.T)) → T.V := fun i => (e i : T.V)
  have hliO : LinearIndependent ↥(OL LL) v := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ↥LL.1 v := (LinearIndependent.iff_fractionRing ↥(OL LL) ↥LL.1).1 hliO

  have hexp : ∀ (x : T.V) (hx : x ∈ T.L.T), x = ∑ i, (((e.repr ⟨x, hx⟩ i : ↥(OL LL)) : ↥LL.1)) • v i := by
    intro x hx
    have h1 := e.sum_repr ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥T.L.T => (y : T.V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ↥LL.1 (e.repr ⟨x, hx⟩ i) (v i)).symm
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range v) := by
    rw [← T.L.span]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨_, Module.Basis.mk hli hsp, fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (e i).2
  · have h3 : (Module.Basis.mk hli hsp).repr x = fun j => (((e.repr ⟨x, hx⟩ j : ↥(OL LL)) : ↥LL.1)) := by
      conv_lhs => rw [hexp x hx]
      simp_rw [← Module.Basis.mk_apply hli hsp]
      exact (Module.Basis.mk hli hsp).repr_sum_self _
    rw [h3]
    exact (e.repr ⟨x, hx⟩ i).2

end GlobalTheory.BaseCoef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocalStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.exists_integralLatticeBasisLocal : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V), IsLatBasis T b := by
  first | exact @GlobalTheory.BaseCoef.lattice_basis_exists | exact GlobalTheory.BaseCoef.lattice_basis_exists | (intros; apply GlobalTheory.BaseCoef.lattice_basis_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQlStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.exists_integral_retraction_finiteExtension_ql : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1), ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧ (∀ x ∈ OL LL', r x ∈ OL LL) := by
  first | exact @GlobalTheory.CoefRetraction.exists_integral_retraction | exact GlobalTheory.CoefRetraction.exists_integral_retraction | (intros; apply GlobalTheory.CoefRetraction.exists_integral_retraction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtension

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem bot_emb_factor {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (hL : LL.1 ≤ LL'.1)
    (τ' : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL'.1) :
    ∃ τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1, τ' = (incl hL).comp τ := by
  refine ⟨IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ_[l] _) ≤ LL.1), ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 (show x.1 ∈ (⊥ : IntermediateField ℚ_[l] _) from x.2)
  have hx : x = algebraMap ℚ_[l] _ c := Subtype.ext hc.symm
  rw [hx, AlgHom.commutes, AlgHom.commutes]




theorem jumpsInV_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb U H τ' a ha
  obtain ⟨τ, rfl⟩ := bot_emb_factor hL τ'
  refine H τ a ?_
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr (pc Pl h hN hF hS).PD b.equivFun
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf_equiv b T.ρ) τ a
  have e2 := Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general (pc Pl h hN hF hS).PD (incl hL)
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf b T.ρ) τ a
  exact e1.2 (e2.2 ha)

end GlobalTheory.BaseCoef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtensionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  first | exact @GlobalTheory.BaseCoef.jumpsInV_extLat | exact GlobalTheory.BaseCoef.jumpsInV_extLat | (intros; apply GlobalTheory.BaseCoef.jumpsInV_extLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtensStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  first | exact @GlobalTheory.BaseCoef.isPotCrys_extLat | exact GlobalTheory.BaseCoef.isPotCrys_extLat | (intros; apply GlobalTheory.BaseCoef.isPotCrys_extLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOnto

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef




theorem extHom_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  intro l _ G _ _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hF
  choose x hx hfx using fun i => hF (b₂ i) (hb₂.1 i)
  have key : ∀ i j, ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m =
      (1 : Matrix (Fin k₂) (Fin k₂) ↥LL.1) i j := by
    intro i j
    have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ F.f (x j)) i
    rw [hfx j, Module.Basis.repr_self] at h1
    rw [Matrix.one_apply, ← show _ = ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m from rfl.symm]
    refine Eq.trans h1 ?_
    rw [Finsupp.single_apply]
    simp only [eq_comm]
  let X : Matrix (Fin k₁) (Fin k₂) ↥LL'.1 := fun m j => incl hL (b₁.repr (x j) m)
  have hX : extMat hL b₁ b₂ F * X = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrArg (incl hL) (key i j)

    rw [map_sum] at this
    simp only [map_mul] at this
    rw [Matrix.mul_apply]
    refine Eq.trans this ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  intro y hy
  refine ⟨X.mulVec y, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (incl_integral hL (hb₁.2 _ (hx j) i)) (hy j)
  · change (extMat hL b₁ b₂ F).mulVec (X.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]

end GlobalTheory.BaseCoef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOntoStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

theorem _root_.GlobalTheory.T.latticeHomBaseChange_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  first | exact @GlobalTheory.BaseCoef.extHom_onto | exact GlobalTheory.BaseCoef.extHom_onto | (intros; apply GlobalTheory.BaseCoef.extHom_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.exists_integral_retraction_finiteExtension_ql l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := GlobalTheory.T.characterSetMapCoefficientField_properties (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (GlobalTheory.T.latticeHomBaseChange_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, GlobalTheory.T.liftable_descends_from_larger_coefficientField l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
end
end
