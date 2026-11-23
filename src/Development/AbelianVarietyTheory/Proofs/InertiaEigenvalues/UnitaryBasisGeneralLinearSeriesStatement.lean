module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightKTypeMapStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetMatrixUnitCompactTotalDegreeLeStatement
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryRepresentativesExistVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeight

section

@[expose] public section

namespace GlobalTheory.DownLift

theorem abstract_irreducible_of_highestWeight (V : Type) [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (hfin : FiniteDimensional ℂ U) (J : Type) (E : J → Module.End ℂ V)
    (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop)
    (hU : ∀ j, ∀ x ∈ U, E j x ∈ U) (han : ∀ x ∈ U, B x x = 0 → x = 0)
    (hadj : ∀ j x y, B (E j x) y = B x (E (st j) y)) (hst : ∀ j, st (st j) = j)
    (hex : ∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) →
      ∃ x ∈ T, x ≠ 0 ∧ Hw x)
    (hprop : ∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x)
    (S : Submodule ℂ V) (hSU : S ≤ U) (hS : S ≠ ⊥) (hSE : ∀ j, ∀ x ∈ S, E j x ∈ S) :
    S = U := by
  classical
  let P : Submodule ℂ V := U ⊓ ⨅ s : S, LinearMap.ker (B (s : V))
  have hP : ∀ y, y ∈ P ↔ y ∈ U ∧ ∀ s ∈ S, B s y = 0 := by
    intro y
    simp [P, Submodule.mem_iInf]
  have hPbot : P = ⊥ := by
    by_contra hne
    have hPE : ∀ j, ∀ x ∈ P, E j x ∈ P := by
      intro j y hy
      rw [hP] at hy ⊢
      refine ⟨hU j y hy.1, fun s hs => ?_⟩
      have h := hadj (st j) s y
      rw [hst] at h
      rw [← h]
      exact hy.2 _ (hSE _ _ hs)
    obtain ⟨y, hyP, hy0, hyw⟩ := hex P inf_le_left hne hPE
    obtain ⟨x, hxS, hx0, hxw⟩ := hex S hSU hS hSE
    rw [hP] at hyP
    obtain ⟨c, hc⟩ := hprop x y (hSU hxS) hyP.1 hxw hyw hx0
    have hyS : y ∈ S := hc ▸ S.smul_mem c hxS
    exact hy0 (han y hyP.1 (hyP.2 y hyS))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let b := Module.finBasis ℂ S
  let φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.pi fun i => (B (b i : V)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hy' : ∀ i, B (b i : V) (y : V) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hy) i
    have hyP : (y : V) ∈ P := by
      rw [hP]
      refine ⟨y.2, fun s hs => ?_⟩
      have h := congrArg (fun z : S => (z : V)) (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h

      rw [← h, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero]
    rw [hPbot, Submodule.mem_bot] at hyP
    rw [Submodule.mem_bot]
    exact Subtype.ext hyP
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fin_fun] at hle
  exact Submodule.eq_of_le_of_finrank_le hSU hle

end GlobalTheory.DownLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeightStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ (J : Type) (E : J → Module.End ℂ V) (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop), (∀ j, ∀ x ∈ U, E j x ∈ U) → (∀ x ∈ U, B x x = 0 → x = 0) → (∀ j x y, B (E j x) y = B x (E (st j) y)) → (∀ j, st (st j) = j) → (∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) → ∃ x ∈ T, x ≠ 0 ∧ Hw x) → (∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x) → ∀ S : Submodule ℂ V, S ≤ U → S ≠ ⊥ → (∀ j, ∀ x ∈ S, E j x ∈ S) → S = U := by
  first | exact @GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | exact GlobalTheory.DownLift.abstract_irreducible_of_highestWeight | (intros; apply GlobalTheory.DownLift.abstract_irreducible_of_highestWeight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryRepresentativesExistVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.unitary_representatives_exist_vector : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W) (ψ : W →ₗ[ℂ] PolF D m n), Function.Injective ψ → (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) → ∀ (τ : D.what₂.Tau) (a b : Fin n), ∃ A : Module.End ℂ W, ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), φ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ x)) → φ ∘ₗ A = GlobalTheory.LowestKType.sop w τ a b ∘ₗ φ := by
  first | exact @GlobalTheory.UnitaryToGl.exists_transport_sop | exact GlobalTheory.UnitaryToGl.exists_transport_sop | (intros; apply GlobalTheory.UnitaryToGl.exists_transport_sop <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryBasisGeneralLinearSeries

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LowestKType

theorem lowestKType_irreducible : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ S : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ S, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ S, ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0) → (∀ ψ ∈ S, ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ)) ∘ₗ ψ ∈ S) → S ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ S := by
  intro D n m w BS K _ r hU1 hU2 W _ _ _ ρ hρ S hSeq hSharm hSstab hS0 φ hφeq hφharm
  classical
  have hinj : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) →
      ψ ≠ 0 → Function.Injective ψ := by
    intro ψ hψ h0
    rw [← LinearMap.ker_eq_bot]
    rcases hρ (LinearMap.ker ψ) (fun k => Submodule.map_le_iff_le_comap.2 fun x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
      rw [hψ, hx, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ext fun x => by
        have : x ∈ LinearMap.ker ψ := h ▸ Submodule.mem_top
        simpa using this) h0
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hseq := hSeq s hsS
  have hsinj := hinj s hseq hs0
  choose A hA using fun τ a b => GlobalTheory.T.unitary_representatives_exist_vector D n m w BS K r hU2 W ρ s hsinj hseq τ a b
  have hV0 : LinearMap.range s ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  have hVst : ∀ P ∈ LinearMap.range s, ∀ (τ : D.what₂.Tau) (a b : Fin n),
      GlobalTheory.LowestKType.sop w τ a b P ∈ LinearMap.range s := by
    rintro _ ⟨x, rfl⟩ τ a b
    exact ⟨A τ a b x, by simpa using LinearMap.congr_fun (hA τ a b s hseq) x⟩
  obtain ⟨P0, ⟨w0, rfl⟩, hP0, lam, hlam⟩ := GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace D n m w _ inferInstance hV0 hVst
  have hw0 : w0 ≠ 0 := by rintro rfl; exact hP0 (map_zero s)
  have hN : ∀ φ' : W →ₗ[ℂ] PolF D m n,
      (∀ (k : K) (x : W), φ' (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ' x)) →
      GlobalTheory.LowestKType.IsNHw w lam (φ' w0) := by
    intro φ' hφ'
    refine ⟨fun τ a b hab => ?_, fun τ a => ?_⟩
    · have h1 : s (A τ a b w0) = 0 := by
        rw [show s (A τ a b w0) = GlobalTheory.LowestKType.sop w τ a b (s w0) from LinearMap.congr_fun (hA τ a b s hseq) w0]
        exact hlam.1 τ a b hab
      have h2 : A τ a b w0 = 0 := hsinj (by rw [h1, map_zero])
      have h3 := LinearMap.congr_fun (hA τ a b φ' hφ') w0
      simp only [LinearMap.comp_apply, h2, map_zero] at h3
      exact h3.symm
    · have h1 : s (A τ a a w0) = s (lam τ a • w0) := by
        rw [show s (A τ a a w0) = GlobalTheory.LowestKType.sop w τ a a (s w0) from LinearMap.congr_fun (hA τ a a s hseq) w0,
          map_smul]
        exact hlam.2 τ a
      have h3 := LinearMap.congr_fun (hA τ a a φ' hφ') w0
      simp only [LinearMap.comp_apply, hsinj h1, map_smul] at h3
      exact h3.symm
  let J := {j : D.what₂.Tau × Fin m × Fin m // GlobalTheory.LowestKType.Cpt w j.1 j.2.1 j.2.2}
  let E : J → Module.End ℂ (W →ₗ[ℂ] PolF D m n) := fun j =>
    LinearMap.llcomp ℂ W (PolF D m n) (PolF D m n) (GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2)
  have hE : ∀ j ψ, E j ψ = GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2 ∘ₗ ψ := fun _ _ => rfl
  let st : J → J := fun j => ⟨(j.1.1, j.1.2.2, j.1.2.1), Iff.symm j.2⟩
  obtain ⟨B, hBpos, hBani, hBadj⟩ := GlobalTheory.T.fockInnerProduct_posDef_compact_matrixUnit_adjoint D n m
  let e := Module.finBasis ℂ W
  let BM : (W →ₗ[ℂ] PolF D m n) →ₗ⋆[ℂ] (W →ₗ[ℂ] PolF D m n) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ψ χ => ∑ i, B (ψ (e i)) (χ (e i)))
      (fun ψ ψ' χ => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
      (fun ψ χ χ' => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
  have hBM : ∀ ψ χ, BM ψ χ = ∑ i, B (ψ (e i)) (χ (e i)) := fun _ _ => rfl
  have hBMani : ∀ ψ : W →ₗ[ℂ] PolF D m n, BM ψ ψ = 0 → ψ = 0 := by
    intro ψ h
    rw [hBM] at h
    have hre : ∑ i, (B (ψ (e i)) (ψ (e i))).re = 0 := by
      have := congrArg Complex.re h
      simpa [Complex.re_sum] using this
    have hz : ∀ i, B (ψ (e i)) (ψ (e i)) = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hBpos (ψ (e i))).2)).1 hre i (Finset.mem_univ _)
      exact Complex.ext this (hBpos _).1
    exact e.ext fun i => by rw [hBani _ (hz i), LinearMap.zero_apply]
  have hBMadj : ∀ j ψ χ, BM (E j ψ) χ = BM ψ (E (st j) χ) := by
    intro j ψ χ
    simp only [hBM, hE, LinearMap.comp_apply]
    exact Finset.sum_congr rfl fun i _ => hBadj w _ _ _ j.2 _ _
  obtain ⟨d, hdφ, hds⟩ : ∃ d, (∀ i, (φ (e i)).totalDegree ≤ d) ∧ ∀ i, (s (e i)).totalDegree ≤ d :=
    ⟨Finset.univ.sup (fun i => (φ (e i)).totalDegree) ⊔ Finset.univ.sup (fun i => (s (e i)).totalDegree),
      fun i => le_sup_of_le_left (Finset.le_sup (f := fun i => (φ (e i)).totalDegree) (Finset.mem_univ i)),
      fun i => le_sup_of_le_right (Finset.le_sup (f := fun i => (s (e i)).totalDegree) (Finset.mem_univ i))⟩
  have hdeg : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ i, (ψ (e i)).totalDegree ≤ d) →
      ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d := by
    intro ψ hψ x

    rw [← e.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hψ i))
  let U : Submodule ℂ (W →ₗ[ℂ] PolF D m n) :=
    { carrier := {ψ | (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) ∧
        (∀ x, GlobalTheory.LowestKType.IsHarm w (ψ x)) ∧ ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d}
      add_mem' := by
        rintro ψ χ ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
        refine ⟨fun k x => by simp [h1, g1], fun x τ i l hi hl => ?_, fun x => add_mem (h3 x) (g3 x)⟩
        simp only [LinearMap.add_apply, map_add (f := _), h2 x τ i l hi hl, g2 x τ i l hi hl, add_zero]
      zero_mem' := ⟨fun k x => by simp, fun x τ i l _ _ => by simp, fun x => zero_mem _⟩
      smul_mem' := by
        rintro c ψ ⟨h1, h2, h3⟩
        refine ⟨fun k x => by simp [h1], fun x τ i l hi hl => ?_, fun x => Submodule.smul_mem _ c (h3 x)⟩
        simp only [LinearMap.smul_apply, map_smul, h2 x τ i l hi hl, smul_zero] }
  have hUfd : FiniteDimensional ℂ U := by
    let f : U →ₗ[ℂ] (Fin (Module.finrank ℂ W) → MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d) :=
      { toFun := fun ψ i => ⟨(ψ : W →ₗ[ℂ] PolF D m n) (e i), ψ.2.2.2 (e i)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    exact Module.Finite.of_injective f (fun ψ χ h => Subtype.ext (e.ext fun i => by
      have := congrArg (fun g => (g i : PolF D m n)) h
      simpa [f] using this))
  have hUst : ∀ j, ∀ ψ ∈ U, E j ψ ∈ U := by
    rintro ⟨⟨τ, a, b⟩, hab⟩ ψ ⟨h1, h2, h3⟩
    refine ⟨fun k x => ?_, fun x => ?_, fun x => ?_⟩
    · show GlobalTheory.LowestKType.kop w τ a b (ψ (ρ k x)) =
        GlobalTheory.ExportSeries.fockGL m w BS (r k) (GlobalTheory.LowestKType.kop w τ a b (ψ x))
      rw [h1, GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
      congr 1
      exact (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ _ _).symm
    · exact GlobalTheory.CompactHarm.fockT_compact_harm D n m w.p (ψ x) (h2 x) τ a b hab
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.T.fockTargetMatrixUnit_compact_totalDegree_le D n m w τ a b hab d _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 (h3 x)))
  have hsU : s ∈ U := ⟨hseq, hSharm s hsS, hdeg s hds⟩
  have hφU : φ ∈ U := ⟨hφeq, hφharm, hdeg φ hdφ⟩
  have hKHw : ∀ x : W →ₗ[ℂ] PolF D m n, GlobalTheory.LowestKType.IsKHwMap w x → GlobalTheory.LowestKType.IsKHw w (x w0) :=
    fun x hxh => ⟨fun τ a b hab hlt => by simpa using LinearMap.congr_fun (hxh.1 τ a b hab hlt) w0,
      fun τ a => (hxh.2 τ a).imp fun c hc => by simpa using LinearMap.congr_fun hc w0⟩
  have key := GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight (W →ₗ[ℂ] PolF D m n) U hUfd J E st BM (GlobalTheory.LowestKType.IsKHwMap w) hUst
    (fun x _ => hBMani x) hBMadj (fun j => rfl)
    (fun T hTU hT0 hTst => by
      haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTU
      exact GlobalTheory.T.exists_highest_weight_K_type_map D n m w W T inferInstance hT0 (fun ψ hψ τ a b hab => hTst ⟨(τ, a, b), hab⟩ ψ hψ))
    (fun x y hx hy hxh hyh hx0 => by
      obtain ⟨c, hc⟩ := GlobalTheory.T.jointHarmonic_highestWeight_multiplicity_one D n m w lam (x w0) (y w0)
        (fun h => hw0 (hinj x hx.1 hx0 (h.trans (map_zero x).symm))) (hx.2.1 w0) (hy.2.1 w0)
        (hN x hx.1) (hN y hy.1) (hKHw x hxh) (hKHw y hyh)
      refine ⟨c, ?_⟩
      by_contra hne
      have h0 : y - c • x ≠ 0 := sub_ne_zero.2 hne
      have := hinj (y - c • x) (fun k z => by simp [hx.1, hy.1]) h0
        (show (y - c • x) w0 = (y - c • x) 0 by simp [hc])
      exact hw0 this)
  have hS'U : S ⊓ U = U := key (S ⊓ U) inf_le_right (by
      intro h
      apply hs0
      have : s ∈ S ⊓ U := ⟨hsS, hsU⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this)
    (fun j ψ hψ => ⟨hSstab ψ hψ.1 j.1.1 j.1.2.1 j.1.2.2 j.2, hUst j ψ hψ.2⟩)
  have : φ ∈ S ⊓ U := by rw [hS'U]; exact hφU
  exact this.1

end GlobalTheory.LowestKType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryBasisGeneralLinearSeriesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.unitary_basis_general_linear_series : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ S : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ S, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ S, ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0) → (∀ ψ ∈ S, ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ)) ∘ₗ ψ ∈ S) → S ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ S := by
  first | exact @GlobalTheory.LowestKType.lowestKType_irreducible | exact GlobalTheory.LowestKType.lowestKType_irreducible | (intros; apply GlobalTheory.LowestKType.lowestKType_irreducible <;> assumption)
end
end
