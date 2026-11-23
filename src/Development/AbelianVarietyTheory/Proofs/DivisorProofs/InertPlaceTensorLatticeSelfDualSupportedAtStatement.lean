module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisWithDualBasisInHermitianLatticeAwayPlStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdelicDecompositionAtFinitePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTrace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.UnramTraceDenom

theorem exists_not_mem_mul_isIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  intro F E _ _ _ _ _ hU v e h
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hU
  haveI := v.isPrime
  let b := NumberField.RingOfIntegers.basis E
  have hloc : ∀ i, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F s * Algebra.trace F E ((b i : E) * e) = algebraMap (𝓞 F) F r := by
    intro i
    apply GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
    have hi := h (b i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hi
    have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Algebra.trace F E ((b i : E) * e))
    exact e1 ▸ hi
  choose s hs r hr using hloc
  refine ⟨∏ i, s i, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hs i hi
  · have key : ∀ i, algebraMap (𝓞 F) F (∏ j, s j) * Algebra.trace F E ((b i : E) * e) ∈
        (algebraMap (𝓞 F) F).range := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap (𝓞 F) F (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    have htr : ∀ a : 𝓞 E, Algebra.trace F E (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * a) ∈
        (algebraMap (𝓞 F) F).range := by
      intro a
      have ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : E) * (b i : E) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr a)

        simpa [map_sum, zsmul_eq_mul] using this.symm

      rw [ha, Finset.mul_sum, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      have e2 : algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * (((b.repr a i : ℤ) : E) * (b i : E)) =
          algebraMap F E (((b.repr a i : ℤ) : F) * algebraMap (𝓞 F) F (∏ j, s j)) * ((b i : E) * e) := by
        have hc : ((∏ i, s i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∏ j, s j) := rfl
        rw [hc, map_mul, map_intCast]; ring
      rw [e2, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_assoc]
      exact Subring.mul_mem _ (intCast_mem _ _) (key i)
    obtain ⟨y, hy⟩ := GlobalTheory.InertSelfDual.mem_of_trace (F := F) (E := E)
      (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e) htr
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y

end GlobalTheory.UnramTraceDenom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTraceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  first | exact @GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | exact GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | (intros; apply GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivial

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.KFinLoc

theorem symp_incM_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x y : Matrix (Fin n) (Fin d) E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F x) (incM F y) =
      algebraMap F (AF F) (Algebra.trace F E (θ * GlobalTheory.WeilM.hTens σ JA JB x y)) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← ht, GlobalTheory.WeilM.symp]

  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem trace_hTens_integral_of_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ ψ n d X Y v hψ X₀ h x hx y hy
  refine (hψ _).1 fun t ht => ?_
  have hat : At (evFin F v) (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hmem : GlobalTheory.EmbChart.atPlace v t • incM F (Matrix.vecMulVec x y) ∈ latAtV X Y v :=
    AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v t, hat, by rw [GlobalTheory.EmbChart.evFin_atPlace]; exact ht,
      x, hx, y, hy, rfl⟩
  have h1 := h _ hmem
  have hm : (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (F := F) (AF F) (-1 : E) := by rw [map_neg, map_one]
  rw [GlobalTheory.LatVac.symp_smul_smul, hm, symp_incM_mat, GlobalTheory.EmbChart.atPlace_mul_right,
    GlobalTheory.EmbChart.atPlace_mul_right, GlobalTheory.EmbChart.evFin_atPlace, one_mul, AlgHom.commutes, neg_one_mul,
    mul_comm] at h1
  exact h1

end GlobalTheory.KFinLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHermitianTensorIntegralOfCharTrivialStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.KFinLoc.trace_hTens_integral_of_char | exact GlobalTheory.KFinLoc.trace_hTens_integral_of_char | (intros; apply GlobalTheory.KFinLoc.trace_hTens_integral_of_char <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def contr (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) :
    Fin d → E := fun j => ∑ i, X i j * (J *ᵥ fun m => σ (x m)) i

theorem hTens_eq_form (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) = form σ JB (contr σ JA X x) y := by
  unfold GlobalTheory.WeilM.hTens form contr
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hTens_smul_vec (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (c : E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec (c • x) y) = σ c * GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) := by
  unfold GlobalTheory.WeilM.hTens
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem decomp_sum (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E)
    (p f : Fin n → Fin n → E) (h : ∀ k l, form σ J (p k) (f l) = if k = l then 1 else 0) :
    X = ∑ k, Matrix.vecMulVec (p k) (contr σ J X (f k)) := by
  set P : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => p k i with hP
  set Q : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => (J *ᵥ fun m => σ (f k m)) i with hQ
  have h1 : Pᵀ * Q = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← h k l]
    simp [P, Q, form, dotProduct]
  have h2 : Q * Pᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : P * Qᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  ext i j
  have e : X i j = ((P * Qᵀ) * X) i j := by rw [h3, Matrix.one_mul]
  rw [e, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, contr, P, Q, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem incM_smul {m k : Type} (c : F) (Z : Matrix m k E) : incM F (c • Z) = algebraMap F (AF F) c • incM F Z := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def c, Algebra.smul_def (algebraMap F (AF F) c), map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes c

theorem inv_mem_O {v : Pl (F := F)} {t : 𝓞 F} (ht : t ∉ v.asIdeal) :
    algebraMap F (Fv F v) ((t : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (t : F) = 1 := by
    have := (v.valuation_eq_one_iff_notMem (K := F)).2 ht
    simpa using this
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : F)⁻¹)
  have h3 : v.valuation F (t : F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem sigma_surj (σ : E →ₐ[F] E) (o : 𝓞 E) : ∃ o' : 𝓞 E, σ (o' : E) = o := by
  obtain ⟨e, he⟩ := (AlgHom.bijective σ).2 (o : E)
  have hi : IsIntegral ℤ e := by
    have h : IsIntegral ℤ (σ e) := he ▸ NumberField.RingOfIntegers.isIntegral_coe o
    exact (isIntegral_algHom_iff (σ.restrictScalars ℤ) σ.injective).1 h
  exact ⟨⟨e, hi⟩, he⟩

theorem lemD (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : Pl (F := F))
    (X₀ : Matrix (Fin n) (Fin d) E)
    (hint : ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v)
      (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y))) ∈ v.adicCompletionIntegers F) :
    GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  have hloc : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      IsIntegral ℤ (algebraMap F E (t : F) * GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) := by
    intro x hx y hy
    obtain ⟨t, ht, hti⟩ := GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace F E hun v (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) (fun o => by
      obtain ⟨o', ho'⟩ := sigma_surj σ o
      have hx' : (o' : E) • x ∈ X.L := X.L.smul_mem o' hx
      have h := hint _ hx' y hy
      rw [hTens_smul_vec, ho'] at h
      rwa [mul_neg])
    refine ⟨t, ht, ?_⟩
    have h := hti.neg
    rwa [mul_neg, neg_neg] at h
  obtain ⟨f, p, hf, hp, hpf⟩ := GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place F E σ B X hX v
  have hw : ∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • contr σ X.J X₀ (f k) ∈ Y.L := by
    intro k
    obtain ⟨s0, hs0, hsf⟩ := hf k
    refine GlobalTheory.T.skewSelfDual_lattice_localised_at_place F E σ B Y hY v _ fun y hy => ?_
    obtain ⟨t, ht, hti⟩ := hloc _ hsf y hy
    refine ⟨t * s0, fun h => (v.isPrime.mem_or_mem h).elim ht hs0, ?_⟩
    rw [← hTens_eq_form]
    rw [hTens_smul_vec, AlgHom.commutes] at hti
    convert hti using 1
    rw [show ((t * s0 : 𝓞 F) : F) = (t : F) * (s0 : F) from rfl, map_mul]
    ring
  choose tw htw hwY using hw
  choose tp htp hpX using hp
  have hdec := decomp_sum σ X.J X₀ p f hpf
  rw [hdec]
  have hsum : incM F (∑ k, Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) =
      ∑ k, incM F (Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) := by
    ext i j

    simp [incM, Matrix.sum_apply, map_sum]
  rw [hsum, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  have hc0 : (tp k * tw k : 𝓞 F) ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim (htp k) (htw k)
  have hne : (tp k * tw k : 𝓞 F) ≠ 0 := fun h => hc0 (h ▸ zero_mem _)
  have hcF : ((tp k * tw k : 𝓞 F) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  have hcE : algebraMap F E ((tp k * tw k : 𝓞 F) : F) ≠ 0 := (map_ne_zero _).2 hcF
  have hvm : Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k)) = ((tp k * tw k : 𝓞 F) : F)⁻¹ •
      Matrix.vecMulVec (algebraMap F E (tp k : F) • p k) (algebraMap F E (tw k : F) • contr σ X.J X₀ (f k)) := by
    ext i j
    rw [show ((tp k * tw k : 𝓞 F) : F) = (tp k : F) * (tw k : F) from rfl] at hcE ⊢
    rw [map_mul] at hcE
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def ((tp k : F) * (tw k : F))⁻¹, map_inv₀, map_mul]
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hcE]
    ring
  refine ⟨GlobalTheory.EmbChart.atPlace v (algebraMap F (Fv F v) ((tp k * tw k : 𝓞 F) : F)⁻¹), (fun u hu => by
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]), ?_, _,
    hpX k, _, hwY k, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]
    exact inv_mem_O hc0
  · rw [hvm, incM_smul, smul_smul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul, AlgHom.commutes]

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin z hz
  have hB := hT.base
  have hV' := hT.geo.hV'
  have hW := hT.geo.hW
  have h1v : evFin F v (1 : AF F) ∈ v.adicCompletionIntegers F := by rw [map_one]; exact one_mem _
  constructor
  · intro hzΓ γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v z hzΓ γ hγ
    simpa using h
  · intro hc
    obtain ⟨X₀, hX₀⟩ := GlobalTheory.T.matrix_adelic_decomposition_at_finite_place F E G.V' G.W hV'.lat hW.lat v z hz
    have hc₀ : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
        (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1 := by
      intro γ hγ
      have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v _ hX₀ γ hγ
      have hm : inclR (F := F) (AF F) (((-1 : 𝓞 E)) : E) = -1 := by simp
      rw [hm, one_mul] at h1
      have e : GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ = z + -(z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) := by abel
      rw [e, GlobalTheory.LatVacArith.symp_add_left, GlobalTheory.LatVacArith.symp_neg_left, AddChar.map_add_eq_mul,
        AddChar.map_neg_eq_inv, hc γ hγ, h1, inv_one, one_mul]
    have hint := GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial F E σ B.ψ G.V' G.W v (hB.inert v w hin).2.2 X₀ hc₀
    have hmem := lemD σ B G.V' G.W hB.unram hV' hW v X₀ hint
    have e : z = (z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) + GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ := by abel
    rw [e]
    exact add_mem hX₀ hmem

end GlobalTheory.InertDual
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertDual.latAtV_selfDual | exact GlobalTheory.InertDual.latAtV_selfDual | (intros; apply GlobalTheory.InertDual.latAtV_selfDual <;> assumption)
end
end
