module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcrisStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriodsStatement
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLe

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.Lower

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem evW_E_ne_zero (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) : bk.evW bk.E ≠ 0 := by
  intro h
  have h0 : bk.ev bk.E = 0 := inclW_injective (h.trans (map_zero _).symm)
  have hu := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  have h1 := hτ.1
  rw [h0, zero_mul] at h1
  have h2 := (hu.map (frobW l)).ne_zero
  rw [frobW_inclW, h1, map_zero] at h2
  exact h2 rfl

theorem map_smul' {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

def raise (bk : BK K) {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (k : ℕ) :
    Frame bk (N + k) d ρ where
  T := F.T
  unit := F.unit
  A := bk.E ^ k • F.A
  A' := bk.E ^ k • F.A'
  A_mul := by
    rw [Matrix.smul_mul, Matrix.mul_smul, F.A_mul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  φ := by
    rw [map_smul', Matrix.mul_smul, ← F.φ, smul_smul, ← map_pow, ← map_pow, ← map_mul, ← pow_add, add_comm]
  fix := F.fix
  ε := F.ε
  gal := F.gal

def lower (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {N₀ k d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Frame bk (N₀ + k) d ρ) (A₀ A₀' : Matrix (Fin d) (Fin d) bk.S) (hA : F.A = bk.E ^ k • A₀)
    (hA' : F.A' = bk.E ^ k • A₀') : Frame bk N₀ d ρ where
  T := F.T
  unit := F.unit
  A := A₀
  A' := A₀'
  A_mul := by
    have h := F.A_mul
    rw [hA, hA', Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.E ^ k * bk.E ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ bk.E_ne_zero) (pow_ne_zero _ bk.E_ne_zero)
    apply mul_left_cancel₀ hE
    rw [h2]; ring
  φ := by
    have h := F.φ
    rw [hA, map_smul', Matrix.mul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.evW (bk.E ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (evW_E_ne_zero bk hτ)
    apply mul_left_cancel₀ hE
    rw [← h2, map_pow]; ring
  fix := F.fix
  ε := F.ε
  gal := F.gal

theorem exists_frame_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  intro l _ K bk τ hτ C hC N N₀ d ρ F hF H hH
  rcases le_total N N₀ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨raise bk F k, rfl, rfl⟩
  · obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    obtain ⟨hdA, hdA'⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τ hτ C hC N d ρ F Y hF hY H).2 N₀ h hH
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left] at hdA hdA'
    choose A₀ hA₀ using hdA
    choose A₀' hA₀' using hdA'
    refine ⟨lower bk hτ F (Matrix.of A₀) (Matrix.of A₀') ?_ ?_, rfl, rfl⟩
    · ext i j; simp [hA₀ i j]
    · ext i j; simp [hA₀' i j]

end GlobalTheory.BKLim.Lower
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  first | (exact @GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (exact GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (intros; apply GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivialCocycleCrystallinePeriodData

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem wseed_of_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  intro l _ K bk τ _ d ρ s
  refine ⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩
  · intro g G hG
    rw [Matrix.mul_one]
    exact s.gal g G hG
  · intro g G hG i j
    obtain ⟨k, hk⟩ := s.nopole bk.ι ((ainfHom K g).comp bk.ι)
    have h1 := map_dvd bk.iA (hk i j)
    have hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x))) := by
      ext a b
      simp only [Matrix.map_apply, BK.iS, RingHom.comp_apply]
      exact hG.ext _
    have hu : IsUnit (bk.iA ((l : Ainf l) ^ k)) := by
      rw [map_pow, map_natCast]
      exact (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k
    change bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1
    rw [map_mul] at h1
    rw [Matrix.mul_one, hX]
    have h2 := (hu.dvd_mul_left).1 h1
    convert h2 using 1
    · simp only [BK.iS, RingHom.comp_apply, map_pow]

    · simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]
  · intro m
    refine ⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩
    simp [Matrix.map_one]

end GlobalTheory.BKLim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivialCocycleCrystallinePeriodDataStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_trivial_cocycle_crystalline_period_data : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  first | exact @GlobalTheory.BKLim.wseed_of_seed | exact GlobalTheory.BKLim.wseed_of_seed | (intros; apply GlobalTheory.BKLim.wseed_of_seed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumps

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def incl (d : ℕ) : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] (Fin d → ℚ_[l]) :=
  (Algebra.linearMap ℤ_[l] ℚ_[l]).compLeft (Fin d)

theorem incl_apply (d : ℕ) (v : Fin d → ℤ_[l]) : incl d v = fun i => algebraMap ℤ_[l] ℚ_[l] (v i) := rfl

theorem incl_injective (d : ℕ) : Function.Injective (incl (l := l) d) := by
  intro v w h
  funext i
  have := congrFun h i
  simp only [incl_apply] at this
  exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) this

theorem qRep_incl {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) (v : Fin d → ℤ_[l]) :
    qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v) := by
  funext i
  change (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ (fun j => algebraMap ℤ_[l] ℚ_[l] (v j))) i = algebraMap ℤ_[l] ℚ_[l] (((ρ g).val *ᵥ v) i)
  rw [RingHom.map_mulVec]
  rfl

end GlobalTheory.BKLim.StdLat

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def lat {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Formalism.WeaklyAdmissibleFiltrations.Lattice (LL := ℚ_[l]) (O := ℤ_[l]) (V := Fin d → ℚ_[l]) (qRep ρ) where
  T := LinearMap.range (incl d)
  stable g x hx := by
    obtain ⟨v, rfl⟩ := hx
    exact ⟨_, (qRep_incl ρ g v).symm⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (incl d) (incl_injective d))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨Pi.single j 1, ?_⟩
    funext i
    simp [incl_apply, Pi.single_apply]

noncomputable def equiv {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    (Fin d → ℤ_[l]) ≃ₗ[ℤ_[l]] ↥(lat ρ).T :=
  LinearEquiv.ofInjective (incl d) (incl_injective d)

theorem equiv_apply {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (v : Fin d → ℤ_[l]) :
    ((equiv ρ v : ↥(lat ρ).T) : Fin d → ℚ_[l]) = incl d v := rfl

noncomputable def basis {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Module.Basis (Fin d) ℤ_[l] ↥(lat ρ).T :=
  (Pi.basisFun ℤ_[l] (Fin d)).map (equiv ρ)

theorem toMatrix_act {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (basis ρ) (basis ρ) (actT (lat ρ) g) = (ρ g).val := by
  have key : ∀ v, (equiv ρ).symm (actT (lat ρ) g (equiv ρ v)) = (ρ g).val *ᵥ v := by
    intro v
    apply (equiv ρ).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [equiv_apply]
    change qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v)
    exact qRep_incl ρ g v
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, key,
    Pi.basisFun_apply, Pi.basisFun_repr]
  simp [Matrix.mulVec_single]

theorem cont_act {d : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin d) ℤ_[l]) (hρ : Continuous ρ)
    (x : Fin d → ℚ_[l]) : Continuous fun g => qRep ρ g x := by
  have h1 : Continuous fun g => ((ρ g).val : Matrix (Fin d) (Fin d) ℤ_[l]) := Units.continuous_val.comp hρ
  have h2 : Continuous fun g => ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) :=
    h1.matrix_map (continuous_subtype_val)
  exact h2.matrix_mulVec continuous_const

end GlobalTheory.BKLim.StdLat

theorem GlobalTheory.BKLim.crys_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsCrys (P.PD K) (qRep ρ) → Nonempty (Seed bk d (fun g => (ρ g).val) τ) := by
  intro l _ K bk τ hτ P AI T d ρ hρc hc
  have h := GlobalTheory.SeedExists.exists_seed l K bk τ hτ P AI ⟨T⟩ (Fin d → ℚ_[l]) (qRep ρ) (GlobalTheory.BKLim.StdLat.lat ρ)
    (GlobalTheory.BKLim.StdLat.cont_act ρ hρc) hc d (GlobalTheory.BKLim.StdLat.basis ρ)
  simp only [GlobalTheory.BKLim.StdLat.toMatrix_act] at h
  exact h

theorem GlobalTheory.BKLim.exists_frame_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  intro l _ K bk τ hτ P AI T N d ρ hρc hsst hjump
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinv := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  have hdr : IsDR (P.PD K) (qRep ρ) := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  have hHN := hH N hjump
  have hunit : ∀ g, IsUnit ((ρ g).val) := fun g => (ρ g).isUnit
  obtain ⟨s, hs⟩ : ∃ s : WSeed bk d (fun g => (ρ g).val) τ, IsCrys (P.PD K) (qRep ρ) → ∀ g, s.κ g = 1 := by
    by_cases hc : IsCrys (P.PD K) (qRep ρ)
    · obtain ⟨sd⟩ := GlobalTheory.BKLim.crys_seed l K bk τ hτ P AI T d ρ hρc hc
      obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_trivial_cocycle_crystalline_period_data l K bk τ hτ d _ sd
      exact ⟨s', fun _ => hs'⟩
    · obtain ⟨N', c₁, c₂, c₃, k₀, F, F', X, X', Z, Z', κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        GlobalTheory.T.exists_semistable_lattice_periods_acris l K bk P AI T C hC d ρ hsst
      obtain ⟨s⟩ := GlobalTheory.T.semistableSeed_of_acris_periods l K bk C τ hτ d (fun g => (ρ g).val) N' c₁ c₂ c₃ k₀ F F' X X' Z Z' κ
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨s, fun h => absurd h hc⟩
  obtain ⟨N', F, hFdr, hFcr⟩ := GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods l K bk τ hτ d _ hunit s
  obtain ⟨F₀, -, hε⟩ := GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le l K bk τ hτ C hinv.2 N' N d _ F hFdr H hHN
  refine ⟨F₀, ?_, fun hc => ?_⟩
  · unfold Frame.IsDR Frame.IsBeta at hFdr ⊢
    rw [hε]; exact hFdr
  · have := hFcr (hs hc)
    unfold Frame.IsCr at this ⊢
    rw [hε]; exact this
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumpsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  first | (exact @GlobalTheory.BKLim.exists_frame_sst) | (exact GlobalTheory.BKLim.exists_frame_sst) | (intros; apply GlobalTheory.BKLim.exists_frame_sst  <;> assumption)
end
end
