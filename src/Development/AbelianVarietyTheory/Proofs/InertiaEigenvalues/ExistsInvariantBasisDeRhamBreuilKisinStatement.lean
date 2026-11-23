module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameLimitGaloisInvariant
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaLimitBdRPlusDeRhamFrameStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameLimitGaloisInvariantStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) → ∀ g : ↥(GK K), (F.ε g).map ((aDp l).comp WittVector.frobenius) * B.map (Per.σDp (g : GQ l)) = B := by
  first | exact @GlobalTheory.BKLim.BinfInv.inv | exact GlobalTheory.BKLim.BinfInv.inv | (intros; apply GlobalTheory.BKLim.BinfInv.inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.frobenius_galois_relation_frame_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  first | exact @GlobalTheory.GalPhi.galPhi | exact GlobalTheory.GalPhi.galPhi | (intros; apply GlobalTheory.GalPhi.galPhi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBdRPlusMatrixOfCongrOne

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.UnitFil

theorem isUnit_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  intro l _ K bk d k β B h1 h2
  obtain ⟨-, hker, hunit, haD, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    exact this
  have hl0 : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hB : ∀ i j, Per.θD l (B i j) = (1 : Matrix (Fin d) (Fin d) ℂ_[l]) i j := by
    intro i j
    have ha := (hker _).2 (h2 i j)
    obtain ⟨c, hc⟩ := h1 i j
    have hb : bk.ev (β i j) = (l : Ainf l) ^ k * bk.ev ((1 : Matrix (Fin d) (Fin d) bk.S) i j) + bk.ev bk.E * bk.ev c := by
      have : β i j = (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) i j + bk.E * c := by
        rw [← hc]; simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [this, map_add (f := _), map_mul, map_mul, map_pow, map_natCast]
    rw [map_sub, haD, hb, map_add (f := _), map_mul, map_mul, hE, zero_mul, add_zero, map_mul] at ha
    simp only [map_pow, map_natCast] at ha
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, mul_one] at ha ⊢
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i i) = (l : ℂ_[l]) ^ k * 1 := by
        rw [mul_one]; push_cast at ha; linear_combination -ha
      exact mul_left_cancel₀ hl0 ha'
    · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero] at ha ⊢
      push_cast at ha
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i j) = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 ha').resolve_left hl0
  have hmap : B.map (Per.θD l) = 1 := Matrix.ext hB
  rw [Matrix.isUnit_iff_isUnit_det]
  apply hunit
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.BKLim.UnitFil
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBdRPlusMatrixOfCongrOneStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  first | (exact @GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (exact GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (intros; apply GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerQEqMapKerTheta

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem kerQ_eq_map_ker_theta (l : ℕ) [Fact l.Prime] :
    Formalism.Per.kerP l = (RingHom.ker (Formalism.Per.θ l)).map
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)) := by
  refine le_antisymm (fun s hs => ?_)
    (Ideal.map_le_iff_le_comap.2 fun a ha => GlobalTheory.RingIface.alg_mem_kerP l ha)
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Formalism.Per.Ainf l) s
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l)
    ((l : ℕ) : Formalism.Per.Ainf l)).pow k
  have h0 : Formalism.Per.θP l s = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l s (by rwa [pow_one])
  have h1 : Formalism.Per.θP l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) a) = 0 := by
    rw [← h, map_mul, h0, zero_mul]
  rw [GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Formalism.Per.θ l a = 0 := Subtype.ext h1
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, h]
  exact Ideal.mem_map_of_mem _ h2

end GlobalTheory.Per
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisin

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvBasis

variable {l : ℕ} [Fact l.Prime]

theorem pD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  GlobalTheory.RingIface.pD_eq_alg

theorem zD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  GlobalTheory.RingIface.zD_eq_alg

theorem isUnit_gen_pt (l : ℕ) [Fact l.Prime] {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := GlobalTheory.RingIface.isUnit_of_generator l h

theorem padicInt_hom_ext_pt (f g : ℤ_[l] →+* Per.Ainf l) : f = g := by
  ext1 z
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus this _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  conv_lhs => rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem zD_eq_pt (z : ℤ_[l]) :
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (algebraMap ℤ_[l] (Ainf l) z)) = Per.zD l z := by
  have h : algebraMap ℤ_[l] (Ainf l) = Per.zA l := padicInt_hom_ext_pt _ _
  rw [h, zD_alg_pt l z, aDp, RingHom.comp_apply]

theorem matrix_map_smul {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (r : R) (M : Matrix (Fin d) (Fin d) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp

theorem frob_basis_eq {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) {N d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (hY : Y.map (inclW l) = inclW l τ ^ N • F.T) :
    Y.map WittVector.frobenius = Y * F.A.map bk.ev := by
  have hYij : ∀ i j, inclW l (Y i j) = inclW l τ ^ N * F.T i j := fun i j => by
    simpa using congrFun (congrFun hY i) j
  have hφij : ∀ i j, bk.evW bk.E ^ N * frobW l (F.T i j) = ∑ k, F.T i k * inclW l (bk.ev (F.A k j)) := fun i j => by
    simpa [Matrix.mul_apply, BK.evW] using congrFun (congrFun F.φ i) j
  refine Matrix.ext fun i j => ?_
  apply GlobalTheory.Prism.inclW_injective

  rw [Matrix.map_apply, ← frobW_inclW, hYij, map_mul, map_pow, frobW_inclW, hτ.1, Matrix.mul_apply, map_sum]
  simp_rw [map_mul, hYij]
  calc (inclW l (bk.ev bk.E) * inclW l τ) ^ N * frobW l (F.T i j)
      = inclW l τ ^ N * (bk.evW bk.E ^ N * frobW l (F.T i j)) := by simp only [BK.evW, RingHom.comp_apply]; ring
    _ = _ := by rw [hφij, Finset.mul_sum]; simp only [mul_assoc, Matrix.map_apply]

theorem isUnit_Etau {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E * τ))) := by
  rw [map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} := by
      rw [GlobalTheory.Per.kerQ_eq_map_ker_theta, ← bk.span_ev, Ideal.map_span, Set.image_singleton]
    have hu := isUnit_gen_pt l hk
    rw [pD_alg_pt] at hu
    rw [aDp, RingHom.comp_apply]
    exact hu
  · have h := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    rw [pow_one] at h
    exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ h).map _

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  intro l _ K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_beta_limit_bdRPlus_deRhamFrame l K bk N d ρ F hDR
  obtain ⟨k1, β1, hβ1, hB1⟩ := hB 1
  have hBu : IsUnit B := GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one l K bk d k1 β1 B hβ1.1 hB1
  have hinv := GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant l K bk N d ρ F B hB
  have hφY := frob_basis_eq hτ F Y hY
  have hgal := GlobalTheory.T.frobenius_galois_relation_frame_ainf l K bk τ hτ N d ρ F Y hY
  obtain ⟨v, hv⟩ := isUnit_Etau hτ
  set ι : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  set j : Ainf l →+* Per.BdR l := ι.comp (aDp l) with hj
  set P : Matrix (Fin d) (Fin d) (Ainf l) := Y.map WittVector.frobenius with hP
  have hjv : j (bk.ev bk.E * τ) = v := hv.symm
  have hM : ((Y * F.A.map bk.ev).map (aDp l) * B).map ι = P.map j * B.map ι := by
    rw [Matrix.map_mul, ← hφY, Matrix.map_map]; rfl
  refine ⟨B, ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N • (((Y * F.A.map bk.ev).map (aDp l) * B).map ι), hBu, ?_,
    fun m => ?_, ?_, ?_⟩
  · obtain ⟨Y₀, Y₀', hY₀, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    have hY0 : Y₀ = Y := Matrix.ext fun i k => GlobalTheory.Prism.inclW_injective (by
      have := congrFun (congrFun (hY₀.trans hY.symm) i) k
      simpa using this)
    rw [hY0] at hYY
    have hPP : P * Y₀'.map WittVector.frobenius = (bk.ev bk.E * τ) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
      rw [hP, ← Matrix.map_mul, hYY, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hτ.1]
    have hPj : P.map j * (Y₀'.map WittVector.frobenius).map j = ((v : Per.BdR l) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (Per.BdR l)) := by
      rw [← Matrix.map_mul, hPP, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hjv]
    have hPu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine Matrix.isUnit_det_of_right_inverse (B := (((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ (2 * N)) • (Y₀'.map WittVector.frobenius).map j) ?_
      rw [Matrix.mul_smul, hPj, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hMu : IsUnit (P.map j * B.map ι) := hPu.mul (hBu.map (ι.mapMatrix (m := Fin d)))
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (((v⁻¹).isUnit.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hMu)
  · obtain ⟨k, β, -, h⟩ := hB m
    exact ⟨k, β, h⟩
  · rw [← hv, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  · intro g
    have hσj : ∀ a : Ainf l, Per.σD (g : GQ l) (j a) = j (Per.σA (g : GQ l) a) := fun a => by
      simp only [hj, RingHom.comp_apply, hι, GlobalTheory.MemLoc.ActLaws.σD_alg, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
    have hσι : ∀ b : Per.BdRp l, Per.σD (g : GQ l) (ι b) = ι (Per.σDp (g : GQ l) b) := fun b =>
      GlobalTheory.MemLoc.ActLaws.σD_alg _ b
    set c : Per.BdR l := ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N with hc
    set R : Matrix (Fin d) (Fin d) (Per.BdR l) := (ρ g).map (Per.zD l) with hR
    set S : Matrix (Fin d) (Fin d) (Per.BdR l) := (P.map (Per.σA (g : GQ l))).map j with hS
    set T' : Matrix (Fin d) (Fin d) (Per.BdR l) := (B.map (Per.σDp (g : GQ l))).map ι with hT'
    set Ej : Matrix (Fin d) (Fin d) (Per.BdR l) := ((F.ε g).map ((aDp l).comp WittVector.frobenius)).map ι with hEj
    have f1 : (v : Per.BdR l) ^ N • (R * S) = Per.σD (g : GQ l) (v : Per.BdR l) ^ N • (P.map j * Ej) := by
      have h1 := congrArg (fun M => M.map j) (hgal g)
      simp only [matrix_map_smul, Matrix.map_mul, map_pow] at h1
      rw [hjv, ← hσj, hjv] at h1
      have eR : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map j = R := Matrix.ext fun a b => zD_eq_pt (ρ g a b)
      have eE : ((F.ε g).map WittVector.frobenius).map j = Ej := Matrix.ext fun _ _ => rfl
      rw [eR, eE] at h1
      exact h1
    have f2 : Ej * T' = B.map ι := by
      have h2 := congrArg (fun M => M.map ι) (hinv g)
      simpa only [Matrix.map_mul] using h2
    have f3 : (c • (P.map j * B.map ι)).map (Per.σD (g : GQ l)) = Per.σD (g : GQ l) c • (S * T') := by
      rw [matrix_map_smul, Matrix.map_mul]
      congr 2
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hS, hσj]
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hT', hσι]
    have hw : Per.σD (g : GQ l) c * Per.σD (g : GQ l) (v : Per.BdR l) ^ N = 1 := by
      rw [hc, map_pow, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
    have key : (v : Per.BdR l) ^ N • (R * (Per.σD (g : GQ l) c • (S * T'))) = P.map j * B.map ι := by
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, f1,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, f2, hw, one_smul]
    rw [hM, f3]
    calc R * (Per.σD (g : GQ l) c • (S * T')) = (c * (v : Per.BdR l) ^ N) • (R * (Per.σD (g : GQ l) c • (S * T'))) := by
          rw [hc, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      _ = c • (P.map j * B.map ι) := by rw [mul_smul, key]

end GlobalTheory.BKLim.InvBasis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisinStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  first | exact @GlobalTheory.BKLim.InvBasis.exists_invariant_basis | exact GlobalTheory.BKLim.InvBasis.exists_invariant_basis | (intros; apply GlobalTheory.BKLim.InvBasis.exists_invariant_basis <;> assumption)
end
end
