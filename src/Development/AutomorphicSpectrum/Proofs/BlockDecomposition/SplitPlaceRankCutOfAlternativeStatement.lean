module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGLStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitianStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductorStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLattice
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImageStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocalStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormUniformiserEqInvAbsNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGenericStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatricesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompactStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLatticeStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_of_character_trivial_on_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  first | exact @GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | exact GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | (intros; apply GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem block_unipotent_map {A B : Type} {m : ℕ} [Zero A] [One A] [Zero B] [One B] [DecidableEq (Fin m)] (f : A → B) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (x : Matrix (Fin m) (Fin m) A) :
    (blk4 (1 : Matrix (Fin m) (Fin m) A) x 0 1).map f = blk4 1 (x.map f) 0 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite f, f0, f1]

theorem splitHom_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      blk4 1 (tauC τ x.1) 0 1 := by
  have e1 := GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [GlobalTheory.LocIntw.matR_adele, h x] at e1
  have e2 : (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
        (proj D.sp.cm.sig (Jst D n) v (nb x))).map (splitProj τ) := rfl
  have e3 : (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
      (proj D.sp.cm.sig (Jst D n) v (nb x))) = (blk4 1 x.1 0 1).map (cv D v) := e1
  rw [e2, e3, block_unipotent_map _ (map_zero _) (map_one _), block_unipotent_map _ (map_zero _) (map_one _)]
  rfl

theorem thU_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  have e := splitHom_proj_nMap D n nb h v τ x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e' : (thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 i j =
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1
        (finSumFinEquiv i) (finSumFinEquiv j) := rfl
  rw [e', e]
  change (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _)
    (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j)) =
      (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _) i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.Jp

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElementStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_image_of_unipotent_element : ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n), thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | exact GlobalTheory.CompanionTheory.Jp.thU_proj_nMap | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_proj_nMap <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizer

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizerStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalized_valuation_uniformizer : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  first | exact @GlobalTheory.CompanionTheory.Jp.nvOK_nvL | exact GlobalTheory.CompanionTheory.Jp.nvOK_nvL | (intros; apply GlobalTheory.CompanionTheory.Jp.nvOK_nvL <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem hU_thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    hU D n v τ (thU D n v τ g) = GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
      (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) g := by
  unfold hU
  rw [Function.leftInverse_invFun (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).1 g]

theorem hU_isHgt (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsHgt (O := Ov D v) (nvL D v) (hU D n v τ) := by
  intro a d b κ
  obtain ⟨y, hy⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (pM a d b)
  obtain ⟨k, hk⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL κ)
  have hkK : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ k).2 ⟨κ, hk.symm⟩
  obtain ⟨hyP, hab⟩ := GlobalTheory.T.modulus_upper_parabolic_local D n v τ y a d b hy
  rw [← hy, ← hk, ← map_mul, hU_thU]
  exact (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) ⟨y, hyP⟩ hkK).trans hab

theorem rank_beta0 {k : Type} [Field k] {n r t : ℕ} (h : r + t = n) :
    (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : k) else 0).rank = r := by
  classical
  rw [Matrix.rank_diagonal]
  have hr : r ≤ n := by omega
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

theorem psiV_lift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) (w : (Lv D v)ˣ) (ψ₀ : AddChar (kv D v) ℂ)
    (h : ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) =
      ψ₀ (IsLocalRing.residue (Ov D v) c))
    (ℓ : kv D v → Ov D v) (hℓ : ∀ a, IsLocalRing.residue (Ov D v) (ℓ a) = a) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (kv D v)) (T₀ : Matrix (Fin n) (Fin n) (Ov D v)) :
    psiV D.host.F ψ v (Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))) =
      ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
  have key : Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))
      = ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have key2 : Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v))) =
      IsLocalRing.residue (Ov D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, hℓ]
  rw [key, h, key2]

theorem split_place_rank_cut_of_local_computation : JpCondition → SplitPlaceRankCutEigenvalue := by
  intro hA D n r t hrt hr ψ hψ nb hnb v hgood τ
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov D v)
  have hϖ0 : algebraMap (Ov D v) (Lv D v) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Ov D v) (Lv D v))]
    exact hϖ.ne_zero
  obtain ⟨w, hw⟩ : ∃ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ := ⟨Units.mk0 _ hϖ0, rfl⟩
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := GlobalTheory.T.exists_residue_character_of_conductor D ψ v hgood ϖ hϖ w hw
  have hok := GlobalTheory.T.normalized_valuation_uniformizer D v ϖ hϖ w hw
  choose ℓ hℓ using fun a : kv D v => IsLocalRing.residue_surjective (R := Ov D v) a
  have hβ : (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0).rank = r := rank_beta0 hrt
  obtain ⟨ρ, hρ, hρs, hρm⟩ := GlobalTheory.T.surjective_reduction_maximal_compact D n v τ
  obtain ⟨c, hcd, hct, hcint⟩ := hA (Ov D v) (Lv D v) n r t hrt hr ψ₀ hψ₀ _ hβ
  choose f hinf hoff hfX _ using fun Y : Matrix (Fin n) (Fin n) (kv D v) =>
    GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ (((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y)
  have hfinj : Function.Injective f := by
    intro Y Y' hYY
    have h1 : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y =
        ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y' := by
      rw [← hfX Y, ← hfX Y', hYY]
    funext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply] at h2
    have h3 := IsFractionRing.injective (Ov D v) (Lv D v) (mul_left_cancel₀ (Units.ne_zero _) h2)
    rw [← hℓ (Y i j), ← hℓ (Y' i j), h3]
  have hsinf : ∀ x ∈ Finset.univ.image f, ∀ (w' : NumberField.InfinitePlace D.host.F) (i j : Fin n),
      (GlobalTheory.AdelicU.compInf D.host.F D.host.E w') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinf Y
  have hsoff : ∀ x ∈ Finset.univ.image f, ∀ (v' : Pl D), v' ≠ v → ∀ (i j : Fin n),
      (PositivityTheory.Rg.Rsw.L.cv D v') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hoff Y
  refine ⟨⟨Finset.univ.image f, fun x => coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
    (Function.invFun f x), hsinf, hsoff⟩, c, ?_, hcd, hct, ?_⟩
  · intro β' hβ' hint
    have hTint : ∀ i j, (β'.1.map τ) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v := by
      apply GlobalTheory.T.integral_of_character_trivial_on_lattice D ψ v hgood n
      intro X hX
      obtain ⟨x, hinf', hoff', htx, hint'⟩ := GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ X
      rw [← htx, ← GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ x hinf' hoff' β']
      apply hint
      unfold PositivityTheory.Rg.Rsw.L.IntAt
      exact ⟨hinf', hoff', hint' hX⟩
    let T₀ : Matrix (Fin n) (Fin n) (Ov D v) := fun i j => ⟨(β'.1.map τ) i j, hTint i j⟩
    have hT : (β'.1.map τ : Matrix (Fin n) (Fin n) (Lv D v)) = T₀.map (algebraMap (Ov D v) (Lv D v)) := rfl
    have hne : T₀.map (IsLocalRing.residue (Ov D v)) ≠
        Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0 := by
      intro heq
      have h1 := GlobalTheory.T.rank_residue_le_rank_generic (Ov D v) (Lv D v) n T₀
      have h2 := GlobalTheory.Core.Rk.rank_map_field (τ : D.host.E →+* Fv D.host.F v) β'.1
      rw [heq, hβ] at h1
      have h3 : (T₀.map (algebraMap (Ov D v) (Lv D v))).rank = (β'.1.map τ).rank := by rw [← hT]
      exact absurd (h1.trans (h3.trans h2).le) (not_le.2 hβ')
    have hpch : ∀ Y, PositivityTheory.Rg.Rsw.L.pch ψ (f Y).1 (GlobalTheory.MixModel.rat β'.1) =
        ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
      intro Y
      rw [GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ (f Y) (hinf Y) (hoff Y) β', hfX Y, hT]
      exact psiV_lift D ψ v w ψ₀ hψ₀c ℓ hℓ Y T₀
    show ∑ x ∈ Finset.univ.image f, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
      (Function.invFun f x) * PositivityTheory.Rg.Rsw.L.pch ψ x.1 (GlobalTheory.MixModel.rat β'.1) = 0
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    calc _ = ∑ Y, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0) Y *
          ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Function.leftInverse_invFun hfinj Y, hpch Y]
      _ = 0 := GlobalTheory.T.sum_character_orthogonality_matrices (kv D v) n ψ₀ hψ₀ _ _ hne
  · intro νv hH hP z
    have e1 : ∀ g, GlobalTheory.CompanionTheory.Jp.sphV D n v z g =
        GlobalTheory.Doubling.npow (hU D n v τ (thU D n v τ g)) (z + (n : ℂ) / 2) := by
      intro g
      rw [hU_thU]
      rfl
    rw [← hcint ϖ hϖ w hw ℓ hℓ (nvL D v) hok (hU D n v τ) (hU_isHgt D n v τ) _ νv ρ hρs (hρm ϖ hϖ) z]
    dsimp only
    congr 1
    funext k
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Function.leftInverse_invFun hfinj Y, e1, map_mul, map_mul, hρ k, GlobalTheory.T.local_image_of_unipotent_element D n nb hnb v τ (f Y), hfX Y]
    rfl

end GlobalTheory.CompanionTheory.Jp

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternativeStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.split_place_rank_cut_of_alternative : GlobalTheory.CompanionTheory.Jp.JpCondition → GlobalTheory.CompanionTheory.Jp.SplitPlaceRankCutEigenvalue := by
  first | exact @GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | exact GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | (intros; apply GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation <;> assumption)
end
end
