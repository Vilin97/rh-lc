module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTailStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmul

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakTop

theorem coords_algebraMap_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O]
    [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (c : R) (x : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    coords W O b (algebraMap R O c • x) i = algebraMap R W c * coords W O b x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', coords_tmul, coords_tmul, smul_eq_mul,
        mul_smul, algebraMap_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
        Algebra.smul_def]

end GlobalTheory.WeakTop

theorem GlobalTheory.WeakClosed.continuous_zl_smul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  intro l _ K LL T d b m
  letI := twTop T b
  letI := zlMod T
  haveI := zlTower T
  letI := cbTop l
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, GlobalTheory.WeakTop.coords_algebraMap_smul]
  exact hW.mul continuous_const
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmulStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_padicInt_smul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  first | exact @GlobalTheory.WeakClosed.continuous_zl_smul | exact GlobalTheory.WeakClosed.continuous_zl_smul | (intros; apply GlobalTheory.WeakClosed.continuous_zl_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoord

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory

theorem linearMap_pi_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type}
    [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O),
    (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) →
    ∀ f : (ι → O) →ₗ[O] M,
      @Continuous (ι → O) M
        (Pi.topologicalSpace (t₂ := fun _ => TopologicalSpace.induced bO.equivFun inferInstance))
        inferInstance f := by
  intro l _ O M ι _ _ _ _ _ _ _ e bO hcont f
  classical
  letI : TopologicalSpace O := TopologicalSpace.induced bO.equivFun inferInstance
  have key : ∀ c : ι → O, f c = ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ f c]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (fun j => if i = j then (1:O) else 0) = Pi.single i 1 := by
      funext j; by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hc]
    conv_lhs => rw [← bO.sum_equivFun (c i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Algebra.smul_def, mul_smul]
  have hf : (f : (ι → O) → M) = fun c => ∑ i, ∑ α, algebraMap ℤ_[l] O (bO.equivFun (c i) α) • (bO α • f (Pi.single i 1)) := funext key
  rw [hf]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun α _ => ?_
  exact (hcont _).comp ((continuous_apply α).comp (continuous_induced_dom.comp (continuous_apply i)))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoordStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord : ∀ {l : ℕ} [Fact l.Prime] {O M ι : Type} [CommRing O] [Algebra ℤ_[l] O] [Fintype ι] [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] O), (∀ m : M, Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] O c • m) → ∀ f : (ι → O) →ₗ[O] M, letI := TopologicalSpace.induced bO.equivFun inferInstance; Continuous f := by
  first | exact @GlobalTheory.linearMap_pi_continuous_coord | exact GlobalTheory.linearMap_pi_continuous_coord | (intros; apply GlobalTheory.linearMap_pi_continuous_coord <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopology

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp only [map_zero, zero_smul]
      map_add' := fun a c => by simp only [map_add, add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; exact map_add PowerSeries.C (c i) (c' i)
          simp only [this, map_add (f := _), add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; rw [Pi.mul_apply, Pi.pow_apply]; rfl
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  let := cbValued l
  let := zlMod T
  have := zlTower T
  let : TopologicalSpace (WCb l) := wTop l
  let : TopologicalSpace (TW (RW LL) T) := twTop T b
  have : IsTopologicalRing (Cb l) := inferInstance
  have : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.isTopologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] (K0 K) :=
    let := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact Module.finrank_pos

-- Resolve the tensor-product actions while the scalar rings are still abstract.
private theorem tensorProduct_left_scalarTower {O R N : Type} [CommRing O] [CommRing R]
    [Algebra O R] [AddCommGroup N] [Module O N] : IsScalarTower O R (R ⊗[O] N) :=
  TensorProduct.isScalarTower_left

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l hl P AI K s LL h W E T d e b bO y
  let algA : Algebra ↥(OL LL) (RA LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l)
  let algW : Algebra ↥(OL LL) (RW LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)
  let modW : Module ↥(OL LL) (RW LL) := Algebra.toModule
  let modSelf : Module (RW LL) (RW LL) := Semiring.toModule
  let modO : Module ↥(OL LL) (TW (RW LL) T) :=
    TensorProduct.instModule (R := ↥(OL LL)) (M := RW LL) (N := ↥T.L.T)
  let modRW : Module (RW LL) (TW (RW LL) T) :=
    TensorProduct.leftModule (R := ↥(OL LL)) (R'' := RW LL) (M := RW LL) (N := ↥T.L.T)
  let tT := twTop T b
  let tO := oTop bO
  have ht := isTopologicalAddGroup_twTop T b
  have hn : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hTower := @tensorProduct_left_scalarTower ↥(OL LL) (RW LL) ↥T.L.T _ _ algW _ _
  have hlin := @GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord l hl
    ↥(OL LL) (TW (RW LL) T) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    _ _ (ZMod.fintype _) _ modO tT ht e bO (GlobalTheory.T.continuous_padicInt_smul_latB T b)
  exact @continuous_io_smul_of ↥(OL LL) (RA LL) (RW LL) (TW (RW LL) T)
    _ tO _ algA _ algW _ modRW modO hTower tT ht _
    E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
end
end
end
