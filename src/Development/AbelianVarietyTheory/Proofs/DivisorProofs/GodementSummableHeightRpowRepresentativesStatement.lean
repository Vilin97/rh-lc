module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodementStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrameStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.exists_leviSection_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv := by
  first | exact @GlobalTheory.SphEis.exists_isLv | exact GlobalTheory.SphEis.exists_isLv | (intros; apply GlobalTheory.SphEis.exists_isLv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosets

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem summable_height_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  obtain ⟨lv, hlv⟩ := GlobalTheory.T.exists_leviSection_isotropicFrame F E σ n J j m C D Z J₀ hF
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hF.cm J L a
  choose p β hp k hk e using fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) =>
    hI ((q.out : ratPts σ J) * g)
  have h1 := GlobalTheory.T.summable_absDet_rational_points_godement F E σ n J j m C D Z J₀ hF lv hlv _
    (fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (q.out : ratPts σ J)) p
    (fun q => k q * g⁻¹) β _ (hK.image (continuous_mul_const g⁻¹)) (fun q => q.out.2)
    (fun q => (eq_mul_inv_of_mul_eq (e q)).trans (mul_assoc _ _ _)) (fun q => ⟨k q, hk q, rfl⟩) hp
    (fun q q' hq => ?_) t (by
      have h2 : (m : ℝ) + 2 * j = n := by exact_mod_cast hF.dim
      push_cast
      linarith)
  · refine h1.congr fun q => ?_
    rw [e, hh _ _ (hp q) _ (hk q)]
  · rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, Subgroup.mem_subgroupOf.2 hq⟩, inv_mul_cancel_right _ _⟩

end GlobalTheory.SphEis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosetsStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.summable_height_rpow_parabolicCosets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  first
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a (inferInstance : Submodule.IsLattice E L) hI h hh g t ht
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentatives

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem summable_height_rpow_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD T hT g e he
  obtain ⟨m, Z, J₀, hFr⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ hD.cm n J hD.herm (r + 1) X Y hD.witt.xx hD.witt.yy hD.witt.xy
  have hinv := (GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms F E σ n J r X Y L a h hD T hT).2.2.1
  have hnn : ∀ x, 0 ≤ h x := by
    intro x
    obtain ⟨p, β, hp, k, hk, rfl⟩ := hD.iwa x
    rw [hD.ht p β hp k hk]
    exact NNReal.coe_nonneg _
  have hS := GlobalTheory.T.summable_height_rpow_parabolicCosets F E σ n J (r + 1) m X Y Z J₀ hFr L a hD.lat hD.iwa (fun x => Real.toNNReal (h x))
    (fun p β hp k hk => by simp only [hD.ht p β hp k hk, Real.toNNReal_coe]) g e (by push_cast; linarith)
  have hXinv : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hFr.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsc : ∀ p ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0), ∃ β : GL (Fin (r + 1)) (AF F ⊗[F] E), ScalesBy σ J X p β := by
    intro p hp
    obtain ⟨⟨B, -, hB⟩, B', -, hB'⟩ := hp
    have hX : adMat F X = adMat F X * (B * B') := by
      calc adMat F X = (matHom _ σ J p).1 * ((matHom _ σ J p⁻¹).1 * adMat F X) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]
        _ = adMat F X * (B * B') := by rw [hB', ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have h1 : B * B' = 1 := by
      calc B * B' = adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X * (B * B') := by rw [hXinv, Matrix.one_mul]
        _ = 1 := by rw [Matrix.mul_assoc, ← hX, hXinv]
    have h2 : B' * B = 1 := by
      first | exact mul_eq_one_comm.mp h1 | exact Matrix.mul_eq_one_comm.mp h1 | exact (Matrix.mul_eq_one_comm).1 h1 | exact Matrix.nonsing_inv_mul_cancel_left _ _ h1
    exact ⟨⟨B, B', h1, h2⟩, hB⟩
  let φ : T → GlobalTheory.Eis.Cosets (GlobalTheory.UAut.parFlag σ J X (fun _ => 0)) (ratPts σ J) := fun t =>
    GlobalTheory.AutomorphicL2Unitary.mk _ t.1
  have hrel : ∀ t : T, ∃ γ : ((GlobalTheory.UAut.parFlag σ J X (fun _ => 0)).subgroupOf (ratPts σ J)),
      (γ : ratPts σ J) * (φ t).out = t.1 :=
    fun t => GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 (Quotient.out_eq (φ t))
  have hinj : Function.Injective φ := by
    intro t t' htt
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 htt
    have hγP : ((γ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) := Subgroup.mem_subgroupOf.1 γ.2
    obtain ⟨β, hβ⟩ := hsc _ hγP
    refine Subtype.ext ((hT t'.1).unique ⟨t.2, β, ?_⟩ ⟨t'.2, 1, ?_⟩)
    · rw [← eq_mul_inv_of_mul_eq hγ]; exact hβ
    · simp [ScalesBy]
  refine (hS.comp_injective hinj).congr fun t => ?_
  obtain ⟨γ, hγ⟩ := hrel t
  have hγP : ((γ⁻¹ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) :=
    Subgroup.mem_subgroupOf.1 (inv_mem γ.2)
  obtain ⟨β, hβ⟩ := hsc _ hγP
  have hout : ((φ t).out : ratPts σ J) = γ⁻¹ * t.1 := eq_inv_mul_of_mul_eq hγ
  simp only [Function.comp, Real.coe_toNNReal _ (hnn _)]
  rw [hout, Subgroup.coe_mul, mul_assoc]
  refine congrArg (· ^ e) (hinv _ ⟨?_, β, Subgroup.mem_top _, ?_⟩ _)
  · exact SetLike.coe_mem _
  · exact hβ

end GlobalTheory.ResidueEisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentativesStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.godement_summable_height_rpow_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  first | exact @GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | exact GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | (intros; apply GlobalTheory.ResidueEisenstein.summable_height_rpow_reps <;> assumption)
end
end
