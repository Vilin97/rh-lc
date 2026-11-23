module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointsTransferIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisorsStatement
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroup
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLatticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  first | exact @GlobalTheory.DefTransfer.LatMove.exists_finite_point | exact GlobalTheory.DefTransfer.LatMove.exists_finite_point | (intros; apply GlobalTheory.DefTransfer.LatMove.exists_finite_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDefiniteUnitaryAdelicUnitaryGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef →
    ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 ∧
      (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) ∧
      (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) ∧
      (∀ x, x ∈ infU D.host.E V.rank ↔ j x ∈ GinfC V) ∧
      (∃ A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (A τ)) ∧
        ∀ τ x, infMat D.sp.cm.sig V.gram (θ τ) (j x) =
          A τ * (cEmb (tauE D τ) x : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (A τ)⁻¹) ∧
      (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.DefTransfer.Glob.exists_iso | exact GlobalTheory.DefTransfer.Glob.exists_iso | (intros; apply GlobalTheory.DefTransfer.Glob.exists_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalCartan

theorem doubleCoset_of_hasDiv : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  intro D _ n P d x y hx hy hdx hdy
  obtain ⟨a, b, e⟩ := GlobalTheory.SphGal.HasDiv.exists_eq_mul_mul (O := Ov D.host.E P) (fun _ h => h) hdy hdx
  by_cases hs : IsSplitAt P
  · obtain ⟨φ, hφ⟩ := GlobalTheory.locU_equiv_GL D.host.E n P hs
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g := fun g => by rw [← hφ, φ.apply_symm_apply]
    refine ⟨φ.symm a, ⟨(φ.symm a).2, by rw [hc]; exact a.2⟩, φ.symm b, ⟨(φ.symm b).2, by rw [hc]; exact b.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm a * ⟨x, hx⟩ * φ.symm b := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply, hφ, hφ]
      exact e
    exact congrArg Subtype.val h
  · obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E P
      (GlobalTheory.ToricDistribution.host_unram P) hs
    obtain ⟨φ, hφ⟩ := GlobalTheory.DefU.Inert.locU_equiv D.host.E n P s hs hU.2.1
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g.1 := fun g => by rw [← hφ, φ.apply_symm_apply]
    obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := GlobalTheory.UnramDoubleCoset.doubleCoset_one hU _ (φ ⟨x, hx⟩).2 _ (φ ⟨y, hy⟩).2
      a a.2 b b.2 (by rw [hφ, hφ]; exact e)
    refine ⟨φ.symm ⟨k₁, hk₁.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₁.2⟩,
      φ.symm ⟨k₂, hk₂.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₂.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm ⟨k₁, hk₁.1⟩ * ⟨x, hx⟩ * φ.symm ⟨k₂, hk₂.1⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply]
      exact Subtype.ext e'
    exact congrArg Subtype.val h

end GlobalTheory.LocalCartan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSameDoubleCosetOfHasElementaryDivisorsDefinitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  first | exact @GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | exact GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | (intros; apply GlobalTheory.LocalCartan.doubleCoset_of_hasDiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DefTransfer

theorem sphOp_of_local : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (c : UA D.host.E V.rank ≃* GA D V),
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ c x ∈ GfC V ∧ SuppF V f (c x)) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, c x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (c x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (x y : UA D.host.E V.rank), x ∈ locU V.rank P →
      y ∈ locU V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
      ∃ k₁ ∈ KP V.rank P, ∃ k₂ ∈ KP V.rank P, y = k₁ * x * k₂) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
      (∀ γ ∈ R, c.symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P (c.symm γ))) ∧
      ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
        ∃! γ, γ ∈ R ∧ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
  intro D _ V c hloc hhyp hdiv hcart P d R hR
  obtain ⟨e, f, ϖ, α, -, hef, hϖ1, hϖ2, -, -, -, hαf, hαd, -, hrep⟩ := hR
  have hK : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ c.symm k ∈ KP V.rank P := by
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      refine (hhyp P _).1 ?_
      rw [c.apply_symm_apply]
      exact ⟨hk1, e, f, hef, hk2⟩
    · intro hk
      have h1 := (hhyp P _).2 hk
      rw [c.apply_symm_apply] at h1
      have h2 := (hloc P e f hef _).1 hk.1
      rw [c.apply_symm_apply] at h2
      exact ⟨h1.1, h2.2⟩
  have hK1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    refine (hK 1).2 ?_
    rw [map_one]
    exact ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩
  have hKG : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} → k ∈ GfC V := fun k hk => hk.1.1
  obtain ⟨γ0, ⟨hγ0R, -⟩, -⟩ := hrep.2 α ⟨1, hK1, 1, hK1, by simp⟩
  obtain ⟨hγ0G, k₁, hk₁, k₂, hk₂, hγ0⟩ := hrep.1 γ0 hγ0R
  have hαG : α ∈ GfC V := by
    have : α = k₁⁻¹ * γ0 * k₂⁻¹ := by rw [hγ0]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKG _ hk₁)) hγ0G) (Subgroup.inv_mem _ (hKG _ hk₂))
  have hαloc : c.symm α ∈ locU V.rank P :=
    (hloc P e f hef _).2 ⟨by rw [c.apply_symm_apply]; exact hαG, by rw [c.apply_symm_apply]; exact hαf⟩
  obtain ⟨-, hαdiv⟩ := (hdiv P e f ϖ d _ hef hϖ1 hϖ2 hαloc).1 (by rw [c.apply_symm_apply]; exact hαd)
  have hinv : ∀ x k₁ k₂, k₁ ∈ KP V.rank P → k₂ ∈ KP V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) →
      HasDiv (Ov D.host.E P) d (cLoc P (k₁ * x * k₂)) := by
    rintro x k₁ k₂ hk₁ hk₂ ⟨u, hu, a, ha, b, hb, h⟩
    refine ⟨u, hu, cLoc P k₁ * a, Subgroup.mul_mem _ hk₁.2 ha, b * cLoc P k₂, Subgroup.mul_mem _ hb hk₂.2, ?_⟩
    simp only [map_mul, Units.val_mul, h, Matrix.mul_assoc]
  refine ⟨fun γ hγ => ?_, fun x hx hxd => ?_⟩
  · obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hrep.1 γ hγ
    have e1 : c.symm (k₁ * α * k₂) = c.symm k₁ * c.symm α * c.symm k₂ := by simp only [map_mul]
    rw [e1]
    have hk₁' := (hK _).1 hk₁
    have hk₂' := (hK _).1 hk₂
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁'.1 hαloc) hk₂'.1, hinv _ _ _ hk₁' hk₂' hαdiv⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, hxe⟩ := hcart P d _ x hαloc hx hαdiv hxd
    have hcx : c x = c k₁ * α * c k₂ := by rw [hxe]; simp only [map_mul, c.apply_symm_apply]
    have hk₁' : c k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hk₂' : c k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hconv : ∀ γ, γ⁻¹ * c x ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
      intro γ
      rw [hK]
      simp only [map_mul, map_inv, c.symm_apply_apply]
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := hrep.2 (c x) ⟨_, hk₁', _, hk₂', hcx⟩
    exact ⟨γ, ⟨hγR, (hconv γ).1 hγK⟩, fun γ' hγ' => huniq γ' ⟨hγ'.1, (hconv γ').2 hγ'.2⟩⟩

theorem exists_isTransfer : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef → ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsTransfer V θ j h₀ := by
  intro D _ V θ hθ hs hp
  obtain ⟨j, M, hM, hrat, hfin, hinf, hA, hform⟩ := GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup D V θ hθ hs hp
  obtain ⟨h₀, hh₀, hlat⟩ := GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal D V M hM
  obtain ⟨hex, hloc⟩ := GlobalTheory.T.definiteUnitary_localPoints_transfer_iff D V j h₀ M hM hh₀ hfin hform hlat
  have hhyp := GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice D V j h₀ M hM hh₀ hfin hform hlat hloc
  have hdiv := GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors D V j h₀ M hM hh₀ hfin hform hlat
  refine ⟨j, h₀, hh₀, hrat, hfin, hinf, hA, fun P x => ?_, hhyp, ?_⟩
  · obtain ⟨e, f, hef⟩ := hex P
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := (hloc P e f hef x).1 hx
      exact ⟨h1, e, f, hef, h2⟩
    · rintro ⟨h1, e', f', hef', h2⟩
      exact (hloc P e' f' hef' x).2 ⟨h1, h2⟩
  · exact sphOp_of_local D V (cj j h₀) hloc hhyp hdiv (fun P d x y => GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary D V.rank P d x y)

end GlobalTheory.DefTransfer

end
end
end
