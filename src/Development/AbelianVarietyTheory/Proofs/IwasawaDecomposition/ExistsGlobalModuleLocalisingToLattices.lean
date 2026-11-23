module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberField
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField : ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)), Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 → ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  first | exact @GlobalTheory.exists_approx_finite_places | exact GlobalTheory.exists_approx_finite_places | (intros; apply GlobalTheory.exists_approx_finite_places <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGlobalLatticeLocalGiven

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]



end TupApx

end GlobalTheory.GO
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GlobApx

open Formalism.MainNotions.G

theorem mulVec_mem_colSpan {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (w : Fin k → R) :
    g.mulVec (fun j => algebraMap R K (w j)) ∈ colSpan R g := by
  have : g.mulVec (fun j => algebraMap R K (w j)) = ∑ j, w j • fun i => g i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_pow_smul_ge {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ a : ℕ, ∀ N, a ≤ N → ∃ g0 : Matrix (Fin k) (Fin k) R,
      algebraMap R K π ^ N • g = g0.map (algebraMap R K) := by
  obtain ⟨a, g0, h⟩ := GlobalTheory.GO.TupApx.exists_pow_smul (K := K) hπ g
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨π ^ d • g0, ?_⟩
  rw [pow_add, mul_comm, mul_smul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

theorem exists_glob_approx : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  intro ι _ _ W Q _ _ _ _ _ _ F _ f π hπ t ht hd n g hg q0
  have hp0 : ∀ q, algebraMap (W q) (Q q) (π q) ≠ 0 := fun q =>
    (map_ne_zero_iff _ (IsFractionRing.injective (W q) (Q q))).2 (hπ q).ne_zero
  choose a ha using fun q => exists_pow_smul_ge (hπ q) (g q)
  choose b hb using fun q => exists_pow_smul_ge (hπ q) (g q)⁻¹
  set M := Finset.univ.sup (fun q => a q + b q) with hMdef
  have hM : ∀ q, a q ≤ M ∧ b q ≤ M := fun q => by
    have := Finset.le_sup (f := fun q => a q + b q) (Finset.mem_univ q)
    constructor <;> omega
  choose G hG using fun q => ha q M (hM q).1
  choose H hH using fun q => hb q M (hM q).2
  choose x hx using fun i j => hd (Pi.single (M := W) q0 (G q0 i j)) (2 * M + 1)
  choose z hz using hx
  have hB : ∀ q i j, f q ((t ^ M)⁻¹ * x i j) = (algebraMap (W q) (Q q) (π q) ^ M)⁻¹ *
      (algebraMap (W q) (Q q) (Pi.single (M := W) q0 (G q0 i j) q) +
        algebraMap (W q) (Q q) (π q) ^ (2 * M + 1) * algebraMap (W q) (Q q) (z i j q)) := by
    intro q i j
    rw [map_mul, map_inv₀, map_pow, ht, hz, map_add (f := _), map_mul, map_pow]
  refine ⟨Matrix.of fun i j => (t ^ M)⁻¹ * x i j, 1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0), ?_, ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue (W q0) (π q0) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact (hπ q0).not_isUnit
    have : (IsLocalRing.residue (W q0)).mapMatrix (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 1 := by
      rw [map_add (f := _), map_one]
      have : (IsLocalRing.residue (W q0)).mapMatrix (π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)).map (algebraMap (W q0) (Q q0)) =
        1 + algebraMap (W q0) (Q q0) (π q0) • ((H q0).map (algebraMap (W q0) (Q q0)) *
          (Matrix.of fun i j => z i j q0).map (algebraMap (W q0) (Q q0))) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
        Matrix.one_apply, apply_ite (algebraMap (W q0) (Q q0)), map_one, map_zero]
    rw [e1, ← hH q0, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (hg q0), Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun (hG q0) i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB, Pi.single_eq_same, ← h2]
    have := hp0 q0
    field_simp
    ring
  · intro q hq c
    set zc : Fin n → W q := fun i => z i c q
    have hv : (fun i => f q ((Matrix.of fun i j => (t ^ M)⁻¹ * x i j) i c)) =
        (g q).mulVec (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) := by
      have e2 : (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) =
          algebraMap (W q) (Q q) (π q) • ((H q).map (algebraMap (W q) (Q q))).mulVec
            (fun j => algebraMap (W q) (Q q) (zc j)) := by
        funext j

        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e2, ← hH q, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hg q), Matrix.one_mulVec]
      funext i
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hB, Pi.single_eq_of_ne hq, map_zero, zero_add]
      have := hp0 q
      field_simp
      ring
    rw [hv]
    exact mulVec_mem_colSpan _ _

end GlobalTheory.GlobApx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegralStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_global_matrix_approximation_mod_integral : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  first | exact @GlobalTheory.GlobApx.exists_glob_approx | exact GlobalTheory.GlobApx.exists_glob_approx | (intros; apply GlobalTheory.GlobApx.exists_glob_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.KerGlob

theorem weak_approx {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (w : ι → HeightOneSpectrum (𝓞 F)) (hw : Function.Injective w) (y : ∀ i, (w i).adicCompletion F) (c : F) (hc : c ≠ 0) :
    ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) :=
  GlobalTheory.T.exists_approx_finite_places_numberField w hw y c hc

theorem matrix_approx {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)]
    [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)]
    {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q) (hπ : ∀ q, Irreducible (π q)) (t : F)
    (ht : ∀ q, f q t = algebraMap (W q) (Q q) (π q))
    (hd : ∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z))
    {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)) (hg : ∀ q, IsUnit (g q).det) (q0 : ι) :
    ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧
      B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧
      ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) :=
  GlobalTheory.T.exists_global_matrix_approximation_mod_integral W Q f π hπ t ht hd g hg q0

theorem colSpan_mul_le {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) ≤ Formalism.MainNotions.G.colSpan R g := by
  rw [Formalism.MainNotions.G.colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ Formalism.MainNotions.G.colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem colSpan_mul_eq {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) = Formalism.MainNotions.G.colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem map_int {F E : Type} [Field F] [NumberField F] [Field E] (w : HeightOneSpectrum (𝓞 F))
    (φ : E →+* w.adicCompletion F) (x : 𝓞 E) : φ x ∈ w.adicCompletionIntegers F := by
  have h2 : IsIntegral (w.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem step {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {W Q : Type} [CommRing W] [Field Q]
    [Algebra W Q] (e : Q ≃+* w.adicCompletion F)
    (heW : ∀ x, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) (p N : ℕ) (hp : (p : F) ≠ 0)
    (a : F) (y : W)
    (hv : Valued.v (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) ≤
      Valued.v (algebraMap F (w.adicCompletion F) ((p : F) ^ N))) :
    ∃ z : W, e.symm (algebraMap F (w.adicCompletion F) a) = algebraMap W Q (y + (p : W) ^ N * z) := by
  have hcc0 : algebraMap F (w.adicCompletion F) ((p : F) ^ N) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp)
  have hz' : (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) / algebraMap F (w.adicCompletion F) ((p : F) ^ N) ∈
      w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hv zero_le
  obtain ⟨z, hz⟩ := (heW (e.symm _)).2 (by rw [e.apply_symm_apply]; exact hz')
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, map_add (f := _), map_add (f := _), map_mul, hz, map_mul, e.apply_symm_apply, map_pow, map_pow, map_natCast,
    map_natCast]
  have hcc' : algebraMap F (w.adicCompletion F) ((p : F) ^ N) = (p : w.adicCompletion F) ^ N := by
    rw [map_pow, map_natCast]
  rw [← hcc', mul_div_cancel₀ _ hcc0]
  ring

variable {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v))

theorem splitPlaceEmbedding_integers_mem_localIntegers (q : Fin (D.gat u v hg).P.nV) (r : 𝓞 D.host.E) :
    KerOne.iw0 Gs u v hg q (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)) := by
  refine ((Gs u v hg).completion_integers_iff q _ rfl _).2 ?_
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  exact map_int _ (((RingHom.fst _ _).comp ((Gs u v hg).spl _ ((Gs u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((Gs u v hg).pl q).1).adicCompletion D.host.F))) r

theorem splitPlaceEmbedding_baseField_eq_completion (q : Fin (D.gat u v hg).P.nV) (a : D.host.F) :
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E a) =
      ((Gs u v hg).eQ q _ rfl).symm (algebraMap D.host.F ((((Gs u v hg).pl q).1).adicCompletion D.host.F) a) := by
  apply ((Gs u v hg).eQ q _ rfl).injective
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  refine ((Gs u v hg).spl_F _ _ a).trans ?_
  exact (RingEquiv.apply_symm_apply _ _).symm

theorem pl_inj : Function.Injective (fun q : Fin (D.gat u v hg).P.nV => ((Gs u v hg).pl q).1) :=
  fun _ _ h => (Gs u v hg).pl.injective (Subtype.ext h)

theorem dense (y : ∀ q, (D.gat u v hg).P.W q) (N : ℕ) : ∃ x : D.host.F, ∀ q, ∃ z : (D.gat u v hg).P.W q,
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E x) =
      algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)
        (y q + ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q) ^ N * z) := by
  rcases isEmpty_or_nonempty (Fin (D.gat u v hg).P.nV) with h | ⟨⟨q1⟩⟩
  · exact ⟨0, fun q => (IsEmpty.false q).elim⟩
  have hp0 : ((D.what₂.places.resChar v : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (((D.gat u v hg).P.setting q1).prime.ne_zero)
  obtain ⟨a, ha⟩ := weak_approx (fun q => ((Gs u v hg).pl q).1) (pl_inj Gs u v hg)
    (fun q => (Gs u v hg).eQ q _ rfl (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) (y q)))
    (((D.what₂.places.resChar v : ℕ) : D.host.F) ^ N) (pow_ne_zero _ hp0)
  refine ⟨a, fun q => ?_⟩
  obtain ⟨z, hz⟩ := step _ ((Gs u v hg).eQ q _ rfl) ((Gs u v hg).completion_integers_iff q _ rfl) _ N hp0 a (y q) (ha q)
  exact ⟨z, (splitPlaceEmbedding_baseField_eq_completion Gs u v hg q a).trans hz⟩

theorem exists_global_lattice (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)) :
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => KerOne.iw0 Gs u v hg q (x i)} := by
  intro hL
  choose g hgu hgL using hL
  have hfr : ∀ q, IsFractionRing ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) :=
    fun q => ((D.gat u v hg).P.setting q).frac_alt
  let Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
    { carrier := {x | ∀ q, (fun i => KerOne.iw0 Gs u v hg q (x i)) ∈ L q}
      add_mem' := fun {x y} hx hy q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((x + y) i)) =
            (fun i => KerOne.iw0 Gs u v hg q (x i)) + fun i => KerOne.iw0 Gs u v hg q (y i) := by
          funext i; simp
        rw [this]; exact (L q).add_mem (hx q) (hy q)
      zero_mem' := fun q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((0 : Fin n → D.host.E) i)) = 0 := by funext i; simp
        rw [this]; exact (L q).zero_mem
      smul_mem' := fun r x hx q => by
        obtain ⟨c, hc⟩ := splitPlaceEmbedding_integers_mem_localIntegers Gs u v hg q r
        have : (fun i => KerOne.iw0 Gs u v hg q ((r • x) i)) = c • fun i => KerOne.iw0 Gs u v hg q (x i) := by
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, ← hc, Algebra.smul_def]
        rw [this]; exact (L q).smul_mem c (hx q) }
  refine ⟨Λ, fun q0 => ?_⟩
  obtain ⟨B, w, hw, hB, hoff⟩ := matrix_approx (fun q => (D.gat u v hg).P.W q) (fun q => (D.gat u v hg).P.Qq q)
    (fun q => (KerOne.iw0 Gs u v hg q).comp (algebraMap D.host.F D.host.E))
    (fun q => ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q)) (fun q => ((D.gat u v hg).P.setting q).p_unif)
    ((D.what₂.places.resChar v : ℕ) : D.host.F) (fun q => by rw [map_natCast, map_natCast])
    (fun y N => dense Gs u v hg y N) g hgu q0
  have hcol : ∀ c, (fun i => algebraMap D.host.F D.host.E (B i c)) ∈ Λ := by
    intro c q
    by_cases hq : q = q0
    · subst hq
      have : (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) =
          fun i => (g q * w.map (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q))) i c := by
        funext i; exact congrFun (congrFun hB i) c
      show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [this, hgL q, ← colSpan_mul_eq (g q) w hw]
      exact Submodule.subset_span ⟨c, rfl⟩
    · show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [hgL q]; exact hoff q hq c
  apply le_antisymm
  · rw [hgL q0, ← colSpan_mul_eq (g q0) w hw, Formalism.MainNotions.G.colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine Submodule.subset_span ⟨_, hcol c, ?_⟩
    funext i; exact (congrFun (congrFun hB i) c).symm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx q0

end GlobalTheory.Mem.Top.KerGlob
end
end
end
