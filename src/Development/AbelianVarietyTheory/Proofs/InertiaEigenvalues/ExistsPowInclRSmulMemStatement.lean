module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootPowIdealsTendstoZeroWeakTop
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordsOneTmulSmul

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakTop

theorem coords_one_tmul_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (w : W) (z : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    GlobalTheory.WeakTop.coords W O b (((1 : O) ⊗ₜ[R] w) • z) i = w * GlobalTheory.WeakTop.coords W O b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        coords_tmul, coords_tmul]
      simp only [Algebra.smul_def]
      ring

end GlobalTheory.WeakTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootPowIdealsTendstoZeroWeakTopStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.teichmullerRootPow_ideals_tendsto_zero_weakTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U := by
  first | exact @GlobalTheory.WeakClosed.SmallW.main | exact GlobalTheory.WeakClosed.SmallW.main | (intros; apply GlobalTheory.WeakClosed.SmallW.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMem

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem inclR_pow_mul_smul_eq_sum {l : ℕ} [Fact l.Prime] {LL : FinExt l} {M : Type} [AddCommGroup M]
    [Module (RW LL) M] {ι : Type} [Fintype ι] [DecidableEq ι]
    (bO : Module.Basis ι ℤ_[l] ↥(OL LL)) (x : Ainf l) (k : ℕ) (z : RA LL) (y : M) :
    inclR LL (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x : RA LL) ^ k * z) • y =
      ∑ α, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (x ^ k * TensorProduct.equivFinsuppOfBasisLeft bO z α) : RW LL) •
        ((bO α ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL) • y) := by
  have hz : z = ∑ α, bO α ⊗ₜ[ℤ_[l]] TensorProduct.equivFinsuppOfBasisLeft bO z α := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft bO).symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  conv_lhs => rw [hz]

  rw [Finset.mul_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, ← mul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

theorem coords_sum_one_tmul_smul {R O W T ι κ : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W]
    [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι]
    [DecidableEq ι] [Fintype κ] (b : Module.Basis ι R T) (w : κ → W) (Y : κ → (O ⊗[R] W) ⊗[O] T)
    (i : ι) :
    GlobalTheory.WeakTop.coords W O b (∑ α, ((1 : O) ⊗ₜ[R] w α) • Y α) i =
      ∑ α, w α * GlobalTheory.WeakTop.coords W O b (Y α) i := by

  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun α _ => GlobalTheory.WeakTop.coords_one_tmul_smul b _ _ i

theorem exists_pow_wittCoords_inclR_smul_mem_nhds {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
    {K LL : FinExt l} {m : ℕ} (bO : Module.Basis (Fin m) ℤ_[l] ↥(OL LL)) {T : Lt K LL} {d : ℕ}
    (b : LatB T d) (y : TW (RW LL) T) (V : Set (Fin d → WCb l))
    (hV : letI := wTop l; V ∈ 𝓝 (0 : Fin d → WCb l)) :
    ∃ k : ℕ, ∀ z : RA LL, letI := zlMod T; haveI := zlTower T;
      GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b (inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]]
        (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y) ∈ V := by
  letI := zlMod T
  haveI := zlTower T
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  set x : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1 with hx
  let Y : Fin m → TW (RW LL) T := fun α => ((bO α ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL)) • y
  let F : (Fin m → WCb l) → (Fin d → WCb l) := fun w i =>
    ∑ α, w α * GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b (Y α) i
  have hF : Continuous F := continuous_pi fun i =>
    continuous_finsetSum _ fun α _ => (continuous_apply α).mul continuous_const
  have hF0 : F 0 = 0 := by funext i; simp [F]
  have hFV : F ⁻¹' V ∈ 𝓝 (0 : Fin m → WCb l) := hF.tendsto 0 (hF0 ▸ hV)
  rw [nhds_pi] at hFV
  obtain ⟨I, -, t, ht, hIt⟩ := Filter.mem_pi.1 hFV
  have hV0 : (⋂ α, t α) ∈ 𝓝 (0 : WCb l) := Filter.iInter_mem.2 ht
  obtain ⟨k, hk⟩ := GlobalTheory.T.teichmullerRootPow_ideals_tendsto_zero_weakTop AI s (⋂ α, t α) hV0
  refine ⟨k, fun z => ?_⟩
  have key : GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b
      (inclR LL (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x : RA LL) ^ k * z) • y) =
      F (fun α => inclW l (x ^ k * TensorProduct.equivFinsuppOfBasisLeft bO z α)) := by
    exact (congrArg (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
      (inclR_pow_mul_smul_eq_sum (M := TW (RW LL) T) bO x k z y)).trans
      (funext fun i => coords_sum_one_tmul_smul b _ _ i)
  rw [key]
  exact hIt fun α _ => Set.mem_iInter.1 (hk _) α

theorem exists_pow_inclR_smul_mem : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL, inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U := by
  intro l _ P AI s K LL T d b y
  letI := zlMod T
  haveI := zlTower T
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  intro U hU
  obtain ⟨-, -, -, -, hfree, hfin, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hU' : U ∈ Filter.comap (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
      (𝓝 (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b 0)) := by
    have := hU
    rw [nhds_induced] at this
    exact this
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU'
  rw [map_zero] at hV
  obtain ⟨k, hk⟩ := exists_pow_wittCoords_inclR_smul_mem_nhds AI s (Module.finBasis ℤ_[l] ↥(OL LL)) b y V hV
  exact ⟨k, fun z => hVU (Set.mem_preimage.2 (hk z))⟩

end GlobalTheory.WeakClosed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_inclR_smul_mem' :
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
      {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T),
      letI := twTop T b
      ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL,
        inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]]
          (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U :=
  @GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem
end
end
