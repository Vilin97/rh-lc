module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedForms
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBalancedCmIntegersActionsSiegelReducedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelGramMemConeIntegerSquares
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedFormsStatement

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosDefBalancedRealFormCmField

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DefForm

variable {E : Type} [Field E] [NumberField E]

def coordForm (m : ℕ) : (Fin m → 𝓞 E) →ₗ[ℤ] (Fin m → 𝓞 E) →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun y z => ∑ k, ∑ τ : E →+* ℂ, (τ (y k : E) * conj (τ (z k : E))).re)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intro n y z; simp only [Finset.smul_sum, Pi.smul_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; rw [zsmul_eq_mul, zsmul_eq_mul]; simp [mul_left_comm])

theorem sum_sum_mul_re {ι : Type} [Fintype ι] (c : ι → ℝ) (u : ι → ℂ) :
    ∑ a, ∑ b, c a * c b * (u a * conj (u b)).re = Complex.normSq (∑ a, (c a : ℂ) * u a) := by

  rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (c a : ℂ) * u a * ((c b : ℂ) * conj (u b)) = ((c a * c b : ℝ) : ℂ) * (u a * conj (u b)) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem coordForm_mem [IsCMField E] (H : Host E) (m : ℕ) : coordForm (E := E) m ∈ realForms H.bar (Fin m → 𝓞 E) := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · simp only [coordForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  · simp only [coordForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    push_cast
    simp only [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
    ring_nf

theorem coordForm_posDef (m : ℕ) : IsPosDef (coordForm (E := E) m) := by
  classical
  rw [isPosDef_iff_basis (Pi.basis fun _ : Fin m => RingOfIntegers.basis E)]
  intro c hc
  have hw : ∀ k (τ : E →+* ℂ), ∑ a, (c a : ℂ) * τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) =
      ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) := by
    intro k τ
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · exact Finset.sum_congr rfl fun j _ => by simp [Pi.basis_apply]
    · intro k' _ hk'
      exact Finset.sum_eq_zero fun j _ => by simp [Pi.basis_apply, Pi.single_apply, Ne.symm hk']
    · simp
  have hsum : ∑ a, ∑ a', c a * c a' * coordForm m ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a)
      ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a') =
      ∑ k, ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) := by
    simp_rw [← hw, ← sum_sum_mul_re]
    simp only [coordForm, LinearMap.mk₂_apply, Finset.mul_sum]
    calc _ = ∑ a, ∑ k, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ τ : E →+* ℂ, ∑ a', c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hsum]
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hc ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
  ext ⟨k, j⟩
  have h2 : ∀ τ : E →+* ℂ, ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) = 0 := fun τ =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h1 k (Finset.mem_univ _)) τ (Finset.mem_univ _))
  have h3 : ∑ j, (c ⟨k, j⟩ : ℂ) • canonicalEmbedding.latticeBasis E j = 0 := by
    ext τ
    simpa [canonicalEmbedding.latticeBasis_apply, integralBasis_apply, canonicalEmbedding.apply_at] using h2 τ
  have := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent _ h3 j
  simpa using this

theorem exists_posDef_realForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := f) fun x => LinearMap.congr_fun hs x
  refine ⟨pullR s (coordForm m), ⟨fun y z => (coordForm_mem H m).1 _ _, fun a y z => ?_⟩, ?_⟩
  · simp only [pullR_apply, map_smul]
    exact (coordForm_mem H m).2 a _ _
  · intro n x hx c hc
    exact coordForm_posDef m n (s ∘ x) (hx.map' s.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)) c hc

end GlobalTheory.DefForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosDefBalancedRealFormCmFieldStatement

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_posDef_balanced_realForm_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  first | exact @GlobalTheory.DefForm.exists_posDef_realForm | exact GlobalTheory.DefForm.exists_posDef_realForm | (intros; apply GlobalTheory.DefForm.exists_posDef_realForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelGramMemConeIntegerSquaresStatement

section

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.siegelGram_mem_cone_integer_squares : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.SiegelCone.gram_mem_cone | exact GlobalTheory.SiegelCone.gram_mem_cone | (intros; apply GlobalTheory.SiegelCone.gram_mem_cone <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMField

section

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

section Cover

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem hasRedCover_of_fintype (bar : O → O) {ι : Type} [Fintype ι] (f : ι → LinearMap.BilinForm ℤ X)
    (h1 : ∀ i y z, f i y z = f i z y) (h2 : ∀ i y, 0 ≤ f i y y)
    (h : ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (c : ι → ℝ), (∀ i, 0 ≤ c i) ∧
      pullR e.toLinearMap B = ∑ i, c i • toReal (f i)) : HasRedCover bar X := by
  let q := Fintype.equivFin ι
  refine ⟨1, fun _ => Fintype.card ι, fun _ i => f (q.symm i), fun _ i => h1 _, fun _ i => h2 _, fun B hB => ?_⟩
  obtain ⟨e, c, hc, he⟩ := h B hB
  refine ⟨e, 0, fun i => c (q.symm i), fun i => hc _, ?_⟩
  rw [he]
  exact (q.symm.sum_comp fun i => c i • toReal (f i)).symm

def sqForm {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) : LinearMap.BilinForm ℤ X :=
  let φ : X →ₗ[ℤ] ℤ := ∑ i, l i • b.coord i
  (LinearMap.mul ℤ ℤ).compl₁₂ φ φ

theorem sqForm_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (y z : X) :
    sqForm b l y z = (∑ i, l i * b.repr y i) * ∑ i, l i * b.repr z i := by
  simp [sqForm, LinearMap.sum_apply]
  rw [Finset.sum_mul_sum, Finset.sum_comm]

theorem sqForm_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (l : Fin n → ℤ) (i j : Fin n) :
    sqForm b l (b i) (b j) = l i * l j := by
  simp [sqForm_apply, Finsupp.single_apply]

theorem exists_equiv_of_actMat_eq {n : ℕ} (b b' : Module.Basis (Fin n) ℤ X)
    (h : (actMat b : O →+* _) = actMat b') : ∃ e : X ≃ₗ[O] X, ∀ i, e (b i) = b' i := by
  let g : X ≃ₗ[ℤ] X := b.equiv b' (Equiv.refl _)
  have hg : ∀ i, g (b i) = b' i := fun i => by simp [g]
  have key : ∀ (c : O) (x : X), g (c • x) = c • g x := by
    intro c x
    have h1 : (g.toLinearMap ∘ₗ (Module.toModuleEnd ℤ X c)) = (Module.toModuleEnd ℤ X c) ∘ₗ g.toLinearMap := by
      refine b.ext fun j => ?_
      change g (c • b j) = c • g (b j)
      rw [hg]
      calc g (c • b j) = g (∑ i, b.repr (c • b j) i • b i) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (c • b j) i • b' i := by simp only [map_sum, map_smul, hg]
        _ = ∑ i, b'.repr (c • b' j) i • b' i := Finset.sum_congr rfl fun i _ => by
            have := congrFun (congrFun (congrArg (fun ρ : O →+* Matrix (Fin n) (Fin n) ℤ => ρ c) h) i) j
            simp only [actMat_apply] at this
            rw [this]
        _ = c • b' j := b'.sum_repr _
    exact LinearMap.congr_fun h1 x
  exact ⟨(g.toAddEquiv).toLinearEquiv key, hg⟩

theorem actMat_balanced {bar : O → O} {n : ℕ} (b : Module.Basis (Fin n) ℤ X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ realForms bar X) {G : Matrix (Fin n) (Fin n) ℝ} (hG : ∀ i j, B (b i) (b j) = G i j) (c : O) :
    ((actMat b c).map (Int.cast : ℤ → ℝ))ᵀ * G = G * (actMat b (bar c)).map (Int.cast : ℤ → ℝ) := by
  ext i j
  have e1 : B (c • b i) (b j) = ∑ k, (b.repr (c • b i) k : ℝ) * G k j :=
    calc B (c • b i) (b j) = B (∑ k, b.repr (c • b i) k • b k) (b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hG, zsmul_eq_mul]
  have e2 : B (b i) (bar c • b j) = ∑ k, G i k * (b.repr (bar c • b j) k : ℝ) :=
    calc B (b i) (bar c • b j) = B (b i) (∑ k, b.repr (bar c • b j) k • b k) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hG, zsmul_eq_mul, mul_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, actMat_apply]
  rw [← e1, ← e2]
  exact hB.2 c _ _

end Cover

theorem hasRedCover (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] : HasRedCover H.bar X := by
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨i, hi⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) X)
    exact Module.Projective.of_split (i.restrictScalars ℤ) ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hi x)
  haveI : Module.Free ℤ X := inferInstance
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀, hB₀'⟩ := GlobalTheory.T.exists_posDef_balanced_realForm_cmField E H X
  have hF := GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced E H n
  obtain ⟨S, hS⟩ := GlobalTheory.T.siegelGram_mem_cone_integer_squares n
  haveI : Nonempty (Module.Basis (Fin n) ℤ X) := ⟨Module.finBasisOfFinrankEq ℤ X hn⟩
  let ref : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → Module.Basis (Fin n) ℤ X := fun ρ => Classical.epsilon fun b => actMat b = ρ
  let ι := ↥hF.toFinset × ↥S
  refine hasRedCover_of_fintype (ι := ι) _ (fun x => sqForm (ref x.1.1) x.2.1) (fun x y z => ?_) (fun x y => ?_) fun B hB => ?_
  · simp only [sqForm_apply, mul_comm]
  · simp only [sqForm_apply]; exact mul_self_nonneg _
  obtain ⟨b, d, d', u, B', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms E H X B₀ hB₀ hB₀' n hn B hB
  have hρ : (actMat b : 𝓞 E →+* _) ∈ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨d', u, h2, h3, fun c => actMat_balanced b h4 h6 c⟩
  set ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ := actMat b with hρdef
  have href : actMat (ref ρ) = ρ := Classical.epsilon_spec (p := fun b => actMat b = ρ) ⟨b, rfl⟩
  obtain ⟨e, he⟩ := exists_equiv_of_actMat_eq (O := 𝓞 E) (ref ρ) b href
  obtain ⟨c, hc, hG⟩ := hS d u h1
  refine ⟨e, fun x => if x.1.1 = ρ then c x.2.1 else 0, fun x => ?_, ?_⟩
  · dsimp only; split_ifs
    · exact hc _
    · exact le_rfl
  refine (ref ρ).ext fun i => (ref ρ).ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [h5, hG]
    simp [Matrix.sum_apply, vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨ρ, hρ⟩ : ↥hF.toFinset)]
  · simp only [if_true, sqForm_basis]
    rw [← Finset.sum_coe_sort S]
    push_cast
    rfl
  · intro y _ hy
    have : y.1 ≠ ρ := fun h => hy (Subtype.ext h)
    simp [this]
  · simp

end GlobalTheory.RedTh
end
end
end
