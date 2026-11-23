module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCoreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlockStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizatiStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  first | exact @GlobalTheory.DblVacFactor.factor | exact GlobalTheory.DblVacFactor.factor | (intros; apply GlobalTheory.DblVacFactor.factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacUnip

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell GlobalTheory.DblVacFactor

section Abstract

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β] [Invertible (2 : R)]

theorem mem_unitary_of_skew (f : R →+* R) (J : Matrix β β R) (K : Matrix (β ⊕ β) (β ⊕ β) R)
    (Δ N : Matrix (β ⊕ β) β R) (Δt Nt : Matrix β (β ⊕ β) R) (x : Matrix β β R)
    (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (hZ : xᵀ * J + J * x.map f = 0) :
    (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = K := by
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

end Abstract

theorem unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  intro F E _ _ _ _ _ σ d W v h2 Z hZat hZlat hZskew
  letI : Invertible (2 : AE F E) := invTwoE
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  have hskew : Zᵀ * J + J * Z.map f = 0 := hZskew
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1 Z
  have hmem := mem_unitary_of_skew f J (dbl J) _ _ _ _ Z hΔT hNT hΔf hNtf (e3 J) (e4 J) (e5 J) hskew
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hu' : u • Z = 0 := hZat u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (u • Z) *
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
  refine ⟨p, hpK, ⟨1, ?_⟩, ?_⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1,
        Matrix.mul_zero, smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
        ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
      rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
    show (1 + ⅟(2 : AE F E) • M) = _
    rw [hNt, invOf_two_eq, algebraMap_smul]
    rfl

end GlobalTheory.DblVacUnip
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  first | exact @GlobalTheory.DblVacUnip.unip_mem | exact GlobalTheory.DblVacUnip.unip_mem | (intros; apply GlobalTheory.DblVacUnip.unip_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.InertTransv.exists_unip_corner_isUnit | exact GlobalTheory.InertTransv.exists_unip_corner_isUnit | (intros; apply GlobalTheory.InertTransv.exists_unip_corner_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApply

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblGenV

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem KD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD (g * h) - 1 = matD g * (matD h - 1) + (matD g - 1) := by
      rw [matD_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    show u • (matD (g * h) - 1) = 0
    have h1 : u • (matD h - 1) = 0 := hh.1 u hu
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
    · rw [_root_.mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem KD_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    show u • (matD g⁻¹ - 1) = 0
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem PDiag_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {p : UD σ W} (hp : p ∈ PDiag σ W) :
    p⁻¹ ∈ PDiag σ W := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t⁻¹, ?_⟩
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hDdef
  set T : Matrix (Fin d) (Fin d) (AE F E) := (t : Matrix (Fin d) (Fin d) (AE F E)) with hT
  set Ti : Matrix (Fin d) (Fin d) (AE F E) := ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) with hTi
  have hTT : T * Ti = 1 := by rw [hT, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ht' : matD p * D = D * T := ht
  have key : matD p⁻¹ * (D * T) = D := by
    rw [← ht', ← Matrix.mul_assoc, matD_inv_mul, Matrix.one_mul]
  show matD p⁻¹ * D = D * Ti
  calc matD p⁻¹ * D = matD p⁻¹ * (D * T) * Ti := by
        rw [Matrix.mul_assoc (matD p⁻¹), Matrix.mul_assoc D, hTT, Matrix.mul_one]
    _ = D * Ti := by rw [key]

end GlobalTheory.DblGenV

namespace GlobalTheory.DblGenV

theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B a (a - G.p) G.p G.V hT.base hT.geo.hV v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ a G.V v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

end GlobalTheory.DblGenV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApplyStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  first | exact @GlobalTheory.DblGenV.mem_of_KD_diag_anti | exact GlobalTheory.DblGenV.mem_of_KD_diag_anti | (intros; apply GlobalTheory.DblGenV.mem_of_KD_diag_anti <;> assumption)
end
end
