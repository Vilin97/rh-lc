module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmLocU
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OmFibreUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaSpHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfSp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPerf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrPerfOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitNormOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitaryOrbitCounting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FibTop

section

@[expose] public section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of' (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU' σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have h2' : FibU σ J ψ v Λ a Y := by
    intro hG hfib ϖ hϖ
    obtain ⟨hW, hH⟩ := hSd hG.1
    exact h2 hG hW hH hfib ϖ hϖ
  exact omLocU_of σ J ψ v Λ a Y hSd hOm hU h1 h2' h3 h4 h5

theorem omLocU_of_fib (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a)
    (h1 : OrbAll σ J ψ v Λ a Y) (hL : LamOC v Λ a) (hH : HermOC σ v a) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of' σ J ψ v Λ a Y hSd hOm (unifEx_holds v) h1 (fibU'_of σ J ψ v Λ a Y hL hH hHe) h3 h4 h5

theorem omLocU_of_hens (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_fib σ J ψ v Λ a Y hSd hOm h1 (lamOC_holds v Λ a hFull) (hermOC_holds v σ a) hHe h3 h4 h5

end PI.OmLocU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmLocUOfOnto

section

@[expose] public section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of_onto (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hO : HensOnto σ J v Λ ψ a Y)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_hens σ J ψ v Λ a Y hSd hOm h1 hFull (fibHens_of σ J v Λ ψ a Y hO) h3 h4 h5

theorem omLocU_of_tr (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_onto σ J ψ v Λ a Y hSd hOm h1 (hensOnto_of σ J v Λ ψ a Y hGI hTr) hFull h3 h4 h5

end PI.OmLocU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.Done

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F))

attribute [local instance] LocMassOrdSF.isModTop_tens in
private theorem fullLattice_of_isSDLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hSD : IsSDLoc σ J v (L : Set (Fin n → E))) :
    Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hL, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro x _
  by_contra hx
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem hx
  let A := Fv F v ⊗[F] E
  let ι : E →+* A := inclR (F := F) (Fv F v)
  let f : (Fin n → A) →ₗ[A] A :=
    ∑ i : Fin n, ι (φ (Pi.single i 1)) • LinearMap.proj i
  have hf (y : Fin n → E) : f (ratV (F := F) (Fv F v) y) = ι (φ y) := by
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, ratV,
      smul_eq_mul]
    change (∑ i : Fin n, ι (φ (Pi.single i 1)) * ι (y i)) = _
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  let fF := f.restrictScalars (Fv F v)
  let fO := fF.restrictScalars (v.adicCompletionIntegers F)
  have hfL : latLoc (E := E) v (L : Set (Fin n → E)) ≤ LinearMap.ker fO := by
    rw [latLoc, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change f (ratV (F := F) (Fv F v) y) = 0
    rw [hf, LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy)), map_zero]
  have hOpen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hSD (basLat_fg v L hL)
  obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v (hOpen.mem_nhds (Submodule.zero_mem _))
    (fun _ : Unit => ratV (F := F) (Fv F v) x)
  have hz := LinearMap.mem_ker.mp (hfL (htx ()))
  change fF (t • ratV (F := F) (Fv F v) x) = 0 at hz
  rw [map_smul] at hz
  change t • f (ratV (F := F) (Fv F v) x) = 0 at hz
  rw [hf] at hz
  exact ((map_ne_zero ι).2 hφx) ((smul_eq_zero.mp hz).resolve_left ht)

theorem local_omega_volume_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)
    (hOm : OmUnique σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hUN := UnN.unitNorm_of_res σ J ψ v Λ hR
  have hP : SdB.TrPerf σ J ψ v := SdB.trPerf_of_res σ J ψ v hR
  intro hS hLat hSD
  have hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ := by
    obtain ⟨L, hL, rfl⟩ := hLat
    exact ⟨L, fullLattice_of_isSDLoc σ J v L hL hSD, rfl⟩
  exact omLocU_of_tr σ J ψ v Λ a Y hSd hOm (UnitaryOrbitCounting.orbAll_of_res σ J ψ v Λ a Y hR hUN)
    (gramInvO_holds σ J v Λ ψ a Y) (Red.trOnto_holds σ J ψ v hS) hFull
    (UnitaryOrbitCounting.countU_of_res' σ J ψ v Λ a Y hR hUN)
    (SdB.sdVolW_of_perf σ J ψ v Λ a hP) (SdB.sdVolH_of_perf σ J ψ v a hP) hS hLat hSD

theorem omLocU_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  local_omega_volume_unique σ J ψ v Λ a Y
    (fun hS => ⟨(PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).1,
      (PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).2.1⟩)
    (omUnique σ J ψ v a)

end PI.OmLocU.Done
end
end
end
