module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfLineSubsetDiscrete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentInjectsSymmetricAntilinearCommutingStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankEigenspaceOfLieMultiplicity

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.UnifEigenRank

theorem finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by
  let W' : Fin n → E := fun i => ⟨W i, hW i⟩
  have hc : ∀ c : Fin n → k, ((Fintype.linearCombination k W' c : E) : V) = ∑ i, c i • W i := fun c => by
    simp [Fintype.linearCombination_apply, W']
  have hb : Function.Bijective (Fintype.linearCombination k W') := by
    refine (Function.bijective_iff_existsUnique _).2 fun z => ?_
    refine (existsUnique_congr fun c => ?_).1 (h z z.2)
    rw [Subtype.ext_iff, hc, eq_comm]
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end GlobalTheory.UnifEigenRank


open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale) in
theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  intro P₀ u Hm χ hu O _ act F hF τ n hn
  have := act.hom
  let j : epsPt (𝟙 (Sp ℂ)) ≅ epsR ℂ := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp ℂ)) ⟶ P₀.A) ≃* (epsR ℂ ⟶ P₀.A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl P₀.A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ P₀.A).left = η[P₀.A].left := Category.id_comp _
  obtain ⟨v, hv, hb⟩ := LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) n hn
  have key : ∀ (z : Fin P₀.g → ℂ) (w : epsR ℂ ⟶ P₀.A), IsTangent w → u.IsDiff z w →
      ((∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w) ↔
        z ∈ ⨅ a, Module.End.eigenspace (F a) (τ a)) := by
    intro z w hw hd
    rw [Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff]
    have h1 : u.IsDiff (F a z) (w ≫ act.act a) :=
      isDiff_comp u (act.act a) (LinearMap.toContinuousLinearMap (F a)) (hF a) hw hd
    have h2 := isDiff_smul u ((isTan_iff _).2 hw) hd (τ a)
    have t1 := isTangent_comp (act.act a) hw
    have t2 := (isTan_iff _).1 (isTan_scale (τ a) ((isTan_iff _).2 hw))
    constructor
    · intro h
      exact (hu.tan₁ _ t1).unique h1 (by rw [h]; exact h2)
    · intro h
      rw [h] at h1
      exact (hu.tan₂ _).unique ⟨t1, h1⟩ ⟨t2, h2⟩
  choose W hW using fun i => (hu.tan₁ (v i) (hv i).1).exists
  have ht : ∀ i, Chart.IsTan (R := ℂ) (G := P₀.A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have list_prod : ∀ {k : ℕ} (x : Fin k → Fin P₀.g → ℂ) (y : Fin k → (epsR ℂ ⟶ P₀.A)),
      (∀ i, Chart.IsTan (y i)) → (∀ i, u.IsDiff (x i) (y i)) →
      Chart.IsTan (List.ofFn y).prod ∧ u.IsDiff (∑ i, x i) (List.ofFn y).prod := by
    intro k
    induction k with
    | zero =>
      intro x y hy hx
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
      exact ⟨Chart.isTan_one, isDiff_zero u⟩
    | succ k ih =>
      intro x y hy hx
      obtain ⟨h1, h2⟩ := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => hy _) (fun i => hx _)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact ⟨Chart.isTan_mul (hy 0) h1, isDiff_add u (hy 0) h1 (hx 0) h2⟩
  have hp : ∀ c : Fin n → ℂ, IsTangent (prodPts (R := ℂ) (G := P₀.A) c v) ∧
      u.IsDiff (∑ i, c i • W i) (prodPts (R := ℂ) (G := P₀.A) c v) := by
    intro c
    obtain ⟨a, b⟩ := list_prod (fun i => c i • W i) (fun i => Chart.spMap (scaleD (c i)) ≫ v i)
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hW i) (c i))
    exact ⟨(isTan_iff _).1 a, b⟩
  refine UnifEigenRank.finrank_of_existsUnique _ W (fun i => (key _ _ (hv i).1 (hW i)).1 (hv i).2) fun z hz => ?_
  obtain ⟨w, hw, hd⟩ := (hu.tan₂ z).exists
  refine (existsUnique_congr fun c => ?_).1 (hb w ⟨hw, (key _ _ hw hd).2 hz⟩)
  refine Iff.trans (isLieComb_iff c v w) ⟨fun h => ?_, fun h => ?_⟩
  · exact (hu.tan₁ _ hw).unique hd (by rw [h]; exact (hp c).2)
  · rw [h] at hd
    exact (hu.tan₂ _).unique ⟨hw, hd⟩ (hp c)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankEigenspaceOfLieMultiplicityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  first | exact @GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult | exact GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult | (intros; apply GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmAntilinearCommCMLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.DimPEL

theorem exists_sum_eigen {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : 𝓞 E →+* Module.End ℂ V) (v : V) :
    ∃ w : (E →+* ℂ) → V, (∀ τ (a : 𝓞 E), F a (w τ) = τ (a : E) • w τ) ∧ v = ∑ τ, w τ := by
  classical
  let B := canonicalEmbedding.latticeBasis E
  let Φ : ((E →+* ℂ) → ℂ) →ₗ[ℂ] Module.End ℂ V := B.constr ℂ (fun i => F (RingOfIntegers.basis E i))
  have hB : ∀ i, B i = canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    simp [B, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  have h1 : ∀ a : 𝓞 E, Φ (canonicalEmbedding E (a : E)) = F a := by
    intro a
    let L₁ : 𝓞 E →ₗ[ℤ] Module.End ℂ V :=
      (Φ.toAddMonoidHom.comp (((canonicalEmbedding E).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)).toIntLinearMap
    let L₂ : 𝓞 E →ₗ[ℤ] Module.End ℂ V := F.toAddMonoidHom.toIntLinearMap
    have : L₁ = L₂ := by
      apply (RingOfIntegers.basis E).ext
      intro i
      change Φ (canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)) = F _
      rw [← hB]
      simp [Φ]
    exact LinearMap.congr_fun this a
  have h2 : ∀ (a : 𝓞 E) (x : (E →+* ℂ) → ℂ), Φ (canonicalEmbedding E (a : E) * x) = F a * Φ x := by
    intro a x
    have : Φ ∘ₗ LinearMap.mulLeft ℂ (canonicalEmbedding E (a : E)) = LinearMap.mulLeft ℂ (F a) ∘ₗ Φ := by
      apply B.ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hB, h1, ← map_mul F, ← h1, ← map_mul (canonicalEmbedding E)]
      rfl
    exact LinearMap.congr_fun this x
  refine ⟨fun τ => Φ (Pi.single τ 1) v, fun τ a => ?_, ?_⟩
  · have : canonicalEmbedding E (a : E) * Pi.single τ 1 = τ (a : E) • (Pi.single τ 1 : (E →+* ℂ) → ℂ) := by
      ext σ
      by_cases h : σ = τ
      · subst h; simp [canonicalEmbedding.apply_at]
      · simp [Pi.single_eq_of_ne h]
    rw [← Module.End.mul_apply, ← h2, this, map_smul, LinearMap.smul_apply]

  · rw [← LinearMap.sum_apply, ← map_sum, Finset.univ_sum_single]
    have := h1 1
    have e : Φ 1 = 1 := by simpa using this
    change v = Φ 1 v
    rw [e]
    rfl

theorem conj_eq_neg {z : ℂ} {d : ℕ} (h : z ^ 2 = -(d : ℂ)) (hd : 0 < d) : starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : z.re = 0 := by
    have h3 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [this]

abbrev Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) := ⨅ a : 𝓞 E, Module.End.eigenspace (F a) (τ (a : E))

theorem mem_Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (v : Fin g → ℂ) : v ∈ Eig F τ ↔ ∀ a : 𝓞 E, F a v = τ (a : E) • v := by
  simp [Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem theta_mem {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (Θ : Matrix (Fin g) (Fin g) ℂ) (hΘ : ∀ a, Comm Θ (F a)) (v : Fin g → ℂ) (hv : v ∈ Eig F τ) :
    Θ.mulVec (star v) ∈ Eig F (ComplexEmbedding.conjugate τ) := by
  rw [mem_Eig] at hv ⊢
  intro a
  rw [hΘ a v, hv, star_smul, Matrix.mulVec_smul, ComplexEmbedding.conjugate_coe_eq]
  rfl

theorem finrank_symm_comm_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ))
    (hρ : ρ₀ ^ 2 = -(H.d : ℂ)) (_hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hdim : ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q)
    (hS : ∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) :
    Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  classical
  have hd : 0 < H.d := H.d_prime.pos
  have hρ0 : ρ₀ ≠ 0 := by
    intro h
    rw [h] at hρ
    have : (H.d : ℂ) = 0 := by simpa using hρ
    exact hd.ne' (by exact_mod_cast this)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    intro τ
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    simpa using this
  have hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E) := by
    intro τ
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg (hsq τ) hd
  have hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀ := by
    intro τ h h'
    rw [hconj, h] at h'
    apply hρ0
    linear_combination (-1/2 : ℂ) * h'
  have heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀ := by
    intro τ h
    rw [hconj]
    have : τ (H.rt : E) ^ 2 = ρ₀ ^ 2 := by rw [hsq, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]
  have hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q :=
    fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))
  let T := {τ : E →+* ℂ // τ (H.rt : E) = ρ₀}
  have hcard : Fintype.card T ≤ Module.finrank ℚ E / 2 := by
    have h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀} := by
      refine Fintype.card_le_of_injective
        (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_
      intro σ τ h
      have h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1 := congrArg Subtype.val h
      exact Subtype.ext (star_injective h2)
    rw [Fintype.card_subtype_compl, NumberField.Embeddings.card] at h1
    have h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ) := Fintype.card_subtype_le _
    rw [NumberField.Embeddings.card] at h3
    change Fintype.card T ≤ _ - Fintype.card T at h1
    omega
  have hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p := fun τ => by rw [hdim', if_pos τ.2]
  have hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q :=
    fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]
  let b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1) := fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)
  let Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1)) :=
    { toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩
      map_add' := fun Θ Θ' => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.add_mulVec]
      map_smul' := fun c Θ => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ hΘ
    obtain ⟨hs, hc⟩ := hS Θ.1 Θ.2
    have k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ hτ v hv
      have hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0 := fun i =>
        congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)
      have e := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
      rw [← e, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [star_smul, Matrix.mulVec_smul, hb, smul_zero]
    have k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ v hv
      by_cases hτ : τ (H.rt : E) = ρ₀
      · exact k1 τ hτ v hv
      · by_contra h0
        have h1 := hpos _ h0
        rw [hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)] at h1
        simp [hermForm] at h1
    have k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0 := by
      intro v
      obtain ⟨w, hw, rfl⟩ := exists_sum_eigen F v
      rw [star_sum, Matrix.mulVec_sum]
      exact Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := k3 (star v)
    rw [star_star] at this
    simpa using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Module.finrank ℂ S ≤ Fintype.card T * (p * q) := hle
    _ ≤ Module.finrank ℚ E / 2 * (p * q) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

end GlobalTheory.KS.DimPEL
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmAntilinearCommCMLeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_symm_antilinear_comm_CM_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ)), ρ₀ ^ 2 = -(H.d : ℂ) → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q) → (∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) → Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  first | exact @GlobalTheory.KS.DimPEL.finrank_symm_comm_le | exact GlobalTheory.KS.DimPEL.finrank_symm_comm_le | (intros; apply GlobalTheory.KS.DimPEL.finrank_symm_comm_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTan

theorem finrank_derivation_le : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  intro l1 l2 _ hu E _ _ _ H D g J _ a w w' bas _ _ _ _ _ N' o _ b ρ R _ _ _ _ _ t τ hρ hP _ hun
  obtain ⟨t₀, m, u, Hm, χ, κ, hG, ⟨hm, -⟩, hκ, hD⟩ := GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting l1 l2 hu o g (N' ^ 2) J b R t hun
  have hx : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨act, act₀, hc, hdet⟩ := GlobalTheory.FibreAct.exists_fibre_act E H D g (N' ^ 2) J a bas o b ρ _ _ t τ _
    (algebraMap o ℂ) t₀.A m hP hx hm
  obtain ⟨F, hF⟩ := (GlobalTheory.KS.exists_linear_lift_action t₀.pol u Hm χ hG).2 (𝓞 E) act₀
  have hle := GlobalTheory.T.finrank_symm_antilinear_comm_CM_le E H t₀.pol.g D.p D.q (algebraMap o ℂ ρ) Hm F (LinearMap.range κ)
    (by rw [← map_pow, hρ]; simp) hG.ah.1 hG.ah.2.1
    (fun σ => by
      split_ifs with h
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).1 h)
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).2 h))
    (by
      rintro _ ⟨d, rfl⟩
      exact ⟨(hD d).1, fun c => (hD d).2 (act.act c) (act₀.act c) (F c) (hc c) (hF c)⟩)
  rw [LinearMap.finrank_range_of_inj hκ] at hle
  exact hle

end GlobalTheory.PelTan
end
end
