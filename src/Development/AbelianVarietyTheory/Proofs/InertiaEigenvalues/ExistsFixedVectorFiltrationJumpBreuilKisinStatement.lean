module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisCommStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJumpStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltrationStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariant

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.BKGal.JumpDR

theorem cB_gal {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (g : Gl l) (b : Per.Bcris l) :
    cB Td (Per.σB (sQ l g) b) = Pl.actQdR (sQ l g) (cB Td b) := by
  have h1 : Td.eB.symm (Per.σB (sQ l g) b) = Pl.actQ (sQ l g) (Td.eB.symm b) := by
    apply Td.eB.injective
    rw [RingEquiv.apply_symm_apply, Td.actB, RingEquiv.apply_symm_apply]
  have h2 := (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).ι_comm g (Td.eB.symm b)
  rw [Pl.PD_ι, Pl.PD_ι, Pl.PD_actB, Pl.PD_actdR] at h2
  change Pl.ιB (Td.eB.symm (Per.σB (sQ l g) b)) = Pl.actQdR (sQ l g) (Pl.ιB (Td.eB.symm b))
  rw [h1]; exact h2

theorem X_equivariant (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)
    (hX : ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T),
      X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (g : Gl l) (b : TW (OB l ↥(OL LL)) T) :
    X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u x =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv]
    | tmul o b =>
      have e1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (sQ l g) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [e1, hX, hX]
      have e2 : ((T.actT g x : ↥T.L.T) : T.V) = T.ρ g (x : T.V) := rfl
      rw [e2, cB_gal]
      show _ = (T.ρ g ((o : ↥LL.1) • (x : T.V))) ⊗ₜ[ℚ_[l]] ((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actdR g (cB Td b))
      rw [map_smul, Pl.PD_actdR]
      rfl

end GlobalTheory.BKGal.JumpDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariantStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  exact @GlobalTheory.BKGal.JumpDR.X_equivariant
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMap

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.BKGal.CrisTensDR

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
  {LL : FinExt l} (T : QLat LL)

theorem coe_smul_lat (o : ↥(OL LL)) (x : ↥T.L.T) :
    ((o • x : ↥T.L.T) : T.V) = (o : ↥LL.1) • (x : T.V) := by
  rw [Submodule.coe_smul]
  exact (algebraMap_smul (↥LL.1) o (x : T.V)).symm

def gx (o : ↥(OL LL)) (b : Per.Bcris l) : ↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR :=
  AddMonoidHom.mk' (fun x => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (fun x y => by
      simp only [Submodule.coe_add, smul_add, TensorProduct.add_tmul])

def gb (o : ↥(OL LL)) : Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun b => gx Td T o b)
    (fun b c => by
      ext x
      simp only [gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.tmul_add])

def g : ↥(OL LL) →+ Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun o => gb Td T o)
    (fun o o' => by
      ext b x
      simp only [gb, gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Subalgebra.coe_add, add_smul,
        TensorProduct.add_tmul])

theorem cB_smul (z : ℤ_[l]) (b : Per.Bcris l) :
    GlobalTheory.BKGal.JumpDR.cB Td (z • b) = (z : ℚ_[l]) • GlobalTheory.BKGal.JumpDR.cB Td b := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.BKGal.JumpDR.cB_algebraMap, ← Algebra.smul_def]

theorem zsmul_lat (z : ℤ_[l]) (o : ↥(OL LL)) (x : ↥T.L.T) :
    (((z • o : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (z : ℚ_[l]) • ((o : ↥LL.1) • (x : T.V)) := by
  show ((z : ℚ_[l]) • (o : ↥LL.1)) • (x : T.V) = _
  exact smul_assoc _ _ _

theorem g_balanced (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.Bcris l) : g Td T (z • o) b = g Td T o (z • b) := by
  ext x
  have h1 := congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (zsmul_lat T z o x)
  have h2 := congrArg (fun w => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] w) (cB_smul Td z b)
  exact h1.trans ((TensorProduct.smul_tmul _ _ _).trans h2.symm)

def f1 : OB l ↥(OL LL) →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  TensorProduct.liftAddHom (g Td T) (g_balanced Td T)

theorem mul_smul_lat (o o' : ↥(OL LL)) (x : ↥T.L.T) :
    (((o * o' : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (o' : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
  rw [coe_smul_lat, smul_smul, Subalgebra.coe_mul, mul_comm]

theorem crisTensorDRLiftFromCoeffBcris_smul_comm (o : ↥(OL LL)) :
    (f1 Td T).comp (DistribSMul.toAddMonoidHom (OB l ↥(OL LL)) o) =
      (AddMonoidHom.compHom' (DistribSMul.toAddMonoidHom (↥T.L.T) o)).comp (f1 Td T) := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul o' b =>
    refine AddMonoidHom.ext fun x => ?_
    show g Td T (o * o') b x = g Td T o' b (o • x)
    exact congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (mul_smul_lat T o o' x)
  | add u v hu hv => exact (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add _ u v).symm)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  intro l _ Pl AI Td LL T
  exact ⟨TensorProduct.liftAddHom (f1 Td T) fun o u x =>
    DFunLike.congr_fun (DFunLike.congr_fun (crisTensorDRLiftFromCoeffBcris_smul_comm Td T o) u) x, fun o b x => rfl⟩

end GlobalTheory.BKGal.CrisTensDR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMapStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  exact @GlobalTheory.BKGal.CrisTensDR.main
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdR

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR




theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdRStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  first | exact @GlobalTheory.BKGal.JumpDR.exists_odAction | exact GlobalTheory.BKGal.JumpDR.exists_odAction | (intros; apply GlobalTheory.BKGal.JumpDR.exists_odAction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisin

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



theorem GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  intro hF l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN i hi
  have Td : LocTied l Pl AI := hStd.some
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map l Pl AI Td LL T
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR l Pl AI Td LL T
  obtain ⟨n, d, c, hd, h1, h2⟩ := GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump l a e LL hl ι P hEN i hi
  let m : Fin n → P.MMl := fun k => ⟨P.xi (d k), hd k⟩
  have key := fun j => GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration hF l a e ϖ LL hl ι P T I jB Pl AI Td hCmp X hX A hA n
    (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) m j
  refine ⟨∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)))
    (X (jB (toBcris (thetaW a LL) ϖ P (m k)))), ?_, (key i).1 h1, fun h => h2 ((key (i + 1)).2 h)⟩
  intro g hg

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm l Pl AI Td LL T A hA a e ϖ (c k) g hg (X (jB (toBcris (thetaW a LL) ϖ P (m k))))
  have e2 := GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant l Pl AI Td LL T X hX g (jB (toBcris (thetaW a LL) ϖ P (m k)))
  have e3 := hHor g hg (d k) (hd k)
  rw [e1, ← e2]
  exact congrArg _ (congrArg X e3)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisinStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  first | exact @GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | exact GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | (intros; apply GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector <;> assumption)
end
end
