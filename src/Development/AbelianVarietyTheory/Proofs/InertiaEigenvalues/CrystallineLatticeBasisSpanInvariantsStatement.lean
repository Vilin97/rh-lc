module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisSpanTensorBcrisRat

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.Per.RatSpan

theorem crisSpan_rat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI hT K V _ _ _ ρ hC y
  have hreg := (tied_regular_and_onto l P AI hT).1
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρ g, map_add' := (ρ g).map_add, map_smul' := fun x v => (ρ g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.B), actVB (P.PD K) ρ' g x = actVB (P.PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.B, x ∈ Dcris (P.PD K) ρ' ↔ x ∈ Dcris (P.PD K) ρ := by
    intro x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(Dcris (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hC' : IsCrys (P.PD K) ρ' := by
    unfold IsCrys at hC ⊢
    rw [hfr, hfr, eq.finrank_eq, hC]
  obtain ⟨m, b, d, hd, hy⟩ := TiedSpan.tied_crisSpan l P AI hT hreg K LL V ρ' hC' y
  refine ⟨m, b, d, fun i => (hmem _).1 (hd i), ?_⟩
  rw [hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  induction d i using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rfl
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]

end GlobalTheory.Per.RatSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisSpanTensorBcrisRatStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.dcris_span_tensorBcris_rat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.B, ∃ (m : ℕ) (b : Fin m → P.R.B) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.Per.RatSpan.crisSpan_rat | exact GlobalTheory.Per.RatSpan.crisSpan_rat | (intros; apply GlobalTheory.Per.RatSpan.crisSpan_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariants

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrisCoord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : Type} [CommRing B] [Algebra F B] {d : ℕ}

def crd (bV : Module.Basis (Fin d) F V) (r : Fin d) : V ⊗[F] B →ₗ[F] B :=
  (TensorProduct.lid F B).toLinearMap ∘ₗ TensorProduct.map (bV.coord r) LinearMap.id

theorem crd_tmul (bV : Module.Basis (Fin d) F V) (r : Fin d) (v : V) (x : B) :
    crd bV r (v ⊗ₜ[F] x) = bV.coord r v • x := by
  simp [crd]

theorem crd_mulLeft (bV : Module.Basis (Fin d) F V) (r : Fin d) (β : B) (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[F] V) (LinearMap.mulLeft F β) z) =
      β * crd bV r z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [crd_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem crd_map (bV : Module.Basis (Fin d) F V) (r : Fin d) (f : V →ₗ[F] V) (σ : B →ₗ[F] B)
    (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map f σ z) =
      ∑ s, LinearMap.toMatrix bV bV f r s • σ (crd bV s z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    have h := congrFun (LinearMap.toMatrix_mulVec_repr bV bV f v) r
    simp only [Matrix.mulVec, dotProduct] at h
    simp only [AlgebraTensorModule.map_tmul, crd_tmul, Module.Basis.coord_apply, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]

theorem crd_basis (bV : Module.Basis (Fin d) F V) (r j : Fin d) :
    crd bV r ((bV j) ⊗ₜ[F] (1 : B)) = if r = j then 1 else 0 := by
  rw [crd_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : r = j
  · subst h; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm h), if_neg h, zero_smul]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V] {d : ℕ}

theorem linIndep_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) :
    LinearIndependent ℚ_[l] (fun i => (b i : V)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
  exact b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)

theorem sum_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) :
    (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • (b i : V) := by
  have h := congrArg T.subtype (b.sum_repr w)

  rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  simp only [algebraMap_smul]
  exact h.symm

theorem span_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
  rw [← hT]
  refine Submodule.span_le.mpr fun x hx => ?_
  rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, sum_lat T b]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def bVL (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (linIndep_lat T b) (span_lat T hT b)

theorem bVL_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : bVL T hT b i = (b i : V) := by
  simp [bVL]

theorem repr_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) (r : Fin d) :
    (bVL T hT b).repr (w : V) r = algebraMap ℤ_[l] ℚ_[l] (b.repr w r) := by
  have h : (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • bVL T hT b i := by
    simp only [bVL_apply]; exact sum_lat T b w
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

theorem toMatrix_lat {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] G V}
    (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] L.T) (g : G) (r s : Fin d) :
    LinearMap.toMatrix (bVL L.T L.span b) (bVL L.T L.span b) (ρ g) r s =
      algebraMap ℤ_[l] ℚ_[l] (LinearMap.toMatrix b b (actT L g) r s) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, bVL_apply, ← repr_lat L.T L.span b]
  rfl

theorem lattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hC d b j
  obtain ⟨m, β, δ, hδ, hy⟩ :=
    GlobalTheory.T.dcris_span_tensorBcris_rat l P AI T K V ρ hC ((bVL L.T L.span b j) ⊗ₜ[ℚ_[l]] (1 : P.R.B))
  refine ⟨m, fun i => T.eB (β i), fun i r => T.eB (crd (bVL L.T L.span b) r (δ i)), ?_, ?_⟩
  · intro i g
    have hinv : actVB (P.PD K) ρ g (δ i) = δ i := by
      have h := hδ i
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at h
      exact h g
    funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hinv
    beta_reduce
    rw [← key, actVB, crd_map]

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [toMatrix_lat, Algebra.smul_def, map_mul, PadicInt.algebraMap_apply, T.zB]
    congr 1
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      AlgHom.coe_coe]
    rw [← T.actB]
    congr 1
    exact (P.PD_actB K g _).symm
  · funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hy

    simp only [map_sum, crd_mulLeft, crd_basis, map_mul] at key
    beta_reduce
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← key]
    by_cases h : r = j
    · subst h; simp
    · simp [h]

end GlobalTheory.CrisCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariantsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.crystallineLattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.CrisCoord.lattice_basis_span_invariants | exact GlobalTheory.CrisCoord.lattice_basis_span_invariants | (intros; apply GlobalTheory.CrisCoord.lattice_basis_span_invariants <;> assumption)
end
end
