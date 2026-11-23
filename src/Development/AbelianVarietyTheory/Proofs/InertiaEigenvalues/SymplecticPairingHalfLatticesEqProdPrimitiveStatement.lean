module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicCharacterFactorPrimitiveOnIdempotentSumStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDualStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Mathlib.Topology.Sheaves.Init
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralIffSelfDualTraceCharacterSplitPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



namespace GlobalTheory.ScalarSelfDual

theorem eq_of_parts {D : D7} {x y : AE D} (hx : infPart D x = 0) (hy : infPart D y = 0)
    (h : toEAf D x = toEAf D y) : x = y := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_sub, hx, hy, sub_zero]) ?_
  rw [map_sub, sub_eq_zero]
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem mul_hO_of_half {D : D7} {S T : HSp D} {e : AE D} {l : WO S T} (hl : IsHalf e l) (u : WO S T) :
    e * hO S T l u = hO S T l u := by
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [mul_left_comm, hl d a]



theorem exists_half_frMapO {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (N i j), fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · have hY : ((Matrix.of fun i j => e * L (N i j) : WO S T).map (toEAf D)) = toEAf D e • N := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL, Matrix.smul_apply, smul_eq_mul]
    have h1 : HMul.hMul (βT⁻¹).val βT.val = (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := Units.inv_mul βT
    have h2 : HMul.hMul (βS⁻¹).val βS.val = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) := Units.inv_mul βS
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val N) βS.val = z := by
      simp only [N, Matrix.mul_assoc]
      rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    unfold frMapO
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, e1]
    exact Matrix.ext fun i j => hz i j

theorem frMapO_half {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} {l : WO S T} (hl : IsHalf e l) (i : Fin T.rank) (j : Fin S.rank) :
    toEAf D e * frMapO S T βS βT l i j = frMapO S T βS βT l i j := by
  have hY : toEAf D e • (l.map (toEAf D)) = l.map (toEAf D) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, hl i j]
  have : toEAf D e • frMapO S T βS βT l = frMapO S T βS βT l := by
    unfold frMapO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hY]
  exact congrFun (congrFun this i) j

theorem trace_single_mul' {R : Type} [CommRing R] {m n : ℕ} (i : Fin m) (j : Fin n) (a : R)
    (M : Matrix (Fin n) (Fin m) R) : Matrix.trace (Matrix.single i j a * M) = a * M j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]



theorem int_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → 0 < S.rank → 0 < T.rank → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hfS hfT hs ht Q e he hQ Z hZ
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hsupp : ∀ x : AE D, e * x = x → infPart D x = 0 := fun x hx => by
    rw [← hx, map_mul, hinf, zero_mul]
  let i₀ : Fin S.rank := ⟨0, hs⟩
  let j₀ : Fin T.rank := ⟨0, ht⟩
  have hsingle : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : AE D), e * x = x → ∀ a b,
      toEAf D e * Matrix.single i j (toEAf D x) a b = Matrix.single i j (toEAf D x) a b := by
    intro m n i j x hx a b
    simp only [Matrix.single_apply]
    split_ifs
    · rw [← map_mul, hx]
    · rw [mul_zero]
  have hint : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : EAf D),
      IsIntM (Matrix.single i j x) ↔ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro m n i j x
    constructor
    · intro h
      have := h i j
      rwa [Matrix.single_apply_same] at this
    · intro h a b
      simp only [Matrix.single_apply]
      split_ifs
      · exact h
      · exact zero_mem _
  obtain ⟨u, hu, -, huZ⟩ := GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix D S T βS βT e hee (Matrix.single i₀ j₀ (toEAf D Z)) (hsingle i₀ j₀ Z hZ)
  have hval : ∀ (l : WO S T) (Z' : AE D), IsHalf e l → e * Z' = Z' → toEAf D Z' = frMapO S T βS βT l j₀ i₀ →
      symplO S T l u = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z')) := by
    intro l Z' hl hZ' h
    have : hO S T l u = Z * Z' := by
      refine eq_of_parts (hsupp _ (mul_hO_of_half hl u)) (by rw [map_mul, hsupp Z hZ, zero_mul]) ?_
      rw [GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT u l, huZ, trace_single_mul', map_mul, h]
    unfold symplO
    rw [this]
  have h1 : toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ u ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [← hint i₀ j₀, ← huZ]
    exact ⟨GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u hu,
      fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u h hu⟩
  rw [h1, GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D ψ S T ΛS ΛT hψ hS hT e hee he.2 hinf hfin u hu]
  constructor
  · intro h Z' hZ' hZi
    obtain ⟨l, hl, hlZ⟩ := exists_half_frMapO S T βS βT hee (Matrix.single j₀ i₀ (toEAf D Z')) (hsingle j₀ i₀ Z' hZ')
    rw [← hval l Z' hl hZ' (by rw [hlZ, Matrix.single_apply_same])]
    refine h l ((GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).2 ?_) hl
    rw [hlZ, hint]
    exact hZi
  · intro h l hlm hl
    have hI := (GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).1 hlm
    obtain ⟨Y, -, hY⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) (frMapO S T βS βT l j₀ i₀)
    have hZ' : e * (e * Y) = e * Y := by rw [← mul_assoc, hee]
    have hE : toEAf D (e * Y) = frMapO S T βS βT l j₀ i₀ := by
      rw [map_mul, hY, frMapO_half βS βT hl]
    rw [hval l (e * Y) hl hZ' hE]
    exact h _ hZ' (by rw [hE]; exact hI j₀ i₀)

end GlobalTheory.ScalarSelfDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralIffSelfDualTraceCharacterSplitPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.integral_iff_selfDual_traceCharacter_splitPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → 0 < S.rank → 0 < T.rank → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1) := by
  first | exact @GlobalTheory.ScalarSelfDual.int_iff_dual | exact GlobalTheory.ScalarSelfDual.int_iff_dual | (intros; apply GlobalTheory.ScalarSelfDual.int_iff_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SymplecticPairingHalfLatticesEqProdPrimitive

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatPairing



theorem trace_mul_int {D : D7} {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin a) (EAf D))
    (hA : IsIntM A) (hB : IsIntM B) :
    Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hB j i)



theorem resS_trace_mul {D : D7} (PP : Pl D.host.E) {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D))
    (B : Matrix (Fin b) (Fin a) (EAf D)) (hA : IsIntM A) (hB : IsIntM B)
    (h : Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨Matrix.trace (A * B), h⟩ = Matrix.trace (redM PP A * redM PP B) := by
  have h1 : (⟨Matrix.trace (A * B), h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ∑ i, ∑ j, (⟨A i j, hA i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨B j i, hB j i⟩ := by
    apply Subtype.ext
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul]
  rw [h1]

  simp only [map_sum, map_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [redM, dif_pos (hA i j), dif_pos (hB j i)]

theorem inv_isPrimitive {R : Type} [CommRing R] (χ : AddChar R ℂ) (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  intro a ha h1
  apply h (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h1 x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply] using this

theorem exists_primitive {E : Type} [Field E] [NumberField E] (PP : Pl E) :
    ∃ χ : AddChar (kP PP) ℂ, χ.IsPrimitive := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  letI : Field (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 E ⧸ PP.asIdeal) := Fintype.ofFinite _
  exact ⟨_, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 E ⧸ PP.asIdeal)⟩




theorem pairing_eq_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT Q e he hQ ϖ hϖ hϖQ
  by_cases h0 : S.rank = 0 ∨ T.rank = 0
  · refine ⟨fun PP => (exists_primitive PP).choose, fun PP _ => (exists_primitive PP).choose_spec, ?_⟩
    intro x _ _ u _ _
    have hz : hO S T x u = 0 := by
      unfold hO
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
    rw [symplO, hz, mul_zero, map_zero, AddChar.map_zero_eq_one]
    symm
    refine Finset.prod_eq_one fun PP _ => ?_
    have : ∀ (A : Matrix (Fin T.rank) (Fin S.rank) (kP PP.1)) (B : Matrix (Fin S.rank) (Fin T.rank) (kP PP.1)),
        Matrix.trace (A * B) = 0 := by
      intro A B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
    rw [this, AddChar.map_zero_eq_one]
  · rw [not_or] at h0
    obtain ⟨χ, hχ, hform⟩ := GlobalTheory.T.adelicCharacter_factor_primitive_on_idempotentSum D ψ Q e he ϖ hϖ hϖQ
      (GlobalTheory.T.integral_iff_selfDual_traceCharacter_splitPlaces D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT (Nat.pos_of_ne_zero h0.1) (Nat.pos_of_ne_zero h0.2) Q e he hQ)
    refine ⟨fun PP => (χ PP)⁻¹, fun PP hPP => inv_isPrimitive _ (hχ PP hPP), ?_⟩
    intro x _ hx u hu hux
    have heu : e • u = u := by
      funext i j
      exact hu i j
    have hsm : (u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) = incA D (ϖ : D.host.E) • u := rfl
    have hZ : e * (-hO S T u x) = -hO S T u x := by
      rw [mul_neg, ← GlobalTheory.PlaceModel.hO_smul_left, heu]
    have htr : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) =
        -Matrix.trace (frMapAdj S T βS βT x * frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [mul_neg, map_neg, ← GlobalTheory.PlaceModel.hO_smul_left, ← hsm, GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT]
    have hint := trace_mul_int _ _ hx hux
    have hint' : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [htr]; exact Subring.neg_mem _ hint
    have hs : symplO S T x u =
        Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (-hO S T u x)) := by
      rw [GlobalTheory.PlaceModel.symplO_skew S T u x, symplO, mul_neg, map_neg]
    rw [hs, hform _ hZ hint']
    refine Finset.prod_congr rfl fun PP _ => ?_
    have h2 : (⟨_, hint'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -⟨_, hint⟩ := Subtype.ext htr
    rw [h2, map_neg, resS_trace_mul PP.1 _ _ hx hux, AddChar.inv_apply, Matrix.trace_mul_comm]

end GlobalTheory.FlatPairing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SymplecticPairingHalfLatticesEqProdPrimitiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.symplectic_pairing_half_lattices_eq_prod_primitive : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  first | exact @GlobalTheory.FlatPairing.pairing_eq_prod | exact GlobalTheory.FlatPairing.pairing_eq_prod | (intros; apply GlobalTheory.FlatPairing.pairing_eq_prod <;> assumption)
end
end
