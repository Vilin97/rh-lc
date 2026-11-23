module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaSt
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Tactic.Continuity
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RemoveNthSuccVecCons
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternatingMapEqZeroOfSpan

section

@[expose] public section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.AltSpan

theorem alternatingMap_eq_zero_of_span :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by
  intro P _ _ M _ _ β b hb m f hf
  classical
  have key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v hv
      choose I hI using fun i => hv i (by simp)
      have hvI : v = b ∘ I := funext fun i => (hI i).symm
      rw [hvI]
      exact hf I
    · intro j S _ ih v hv
      have hlin : f.toMultilinearMap.toLinearMap v j = 0 := by
        apply LinearMap.ext_on_range hb
        intro c
        simp only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]
        apply ih
        intro i hi
        by_cases hij : i = j
        · rw [hij]
          simp
        · rw [Function.update_of_ne hij]
          exact hv i (by simp [hij, hi])
      have h1 := LinearMap.congr_fun hlin (v j)
      simpa [MultilinearMap.toLinearMap_apply] using h1
  ext v
  simpa using key Finset.univ v (by simp)

end GlobalTheory.CompanionTheory.AltSpan
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompInsertNthEq

section

@[expose] public section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KAdjoint

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]

theorem comp_insertNth_eq {m : ℕ} (b : β → P) (s : Fin (m + 1)) (i : β) (J : Fin m → β) :
    b ∘ (s.insertNth i J : Fin (m + 1) → β) = s.insertNth (b i) (b ∘ J) := by
  funext j
  refine Fin.succAboveCases s ?_ (fun k => ?_) j
  · simp
  · simp

theorem position_sum (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by
  rw [← (Fin.insertNthEquiv (fun _ => β) s).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

  simp only [kIp, kDel_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, comp_insertNth_eq, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  rw [← h, θ.map_insertNth]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

theorem kIp_kD (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) :
    kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) := by
  have hs : ∀ s : Fin (m + 1), ∑ I : Fin (m + 1) → β,
      B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
        = kIp B b η (kDel T' b θ) := fun s => position_sum B b T T' h η θ s

  simp only [kIp, kD_apply, Function.comp_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [kIp] at hs
  rw [Finset.sum_congr rfl fun s _ => hs s]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.CompanionTheory.KAdjoint
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceContraction

section

@[expose] public section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Invsum

theorem invariance_contraction {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P)
    (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M)
    (hanti : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hinv : ∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (k : γ) (J : Fin q → β) :
    ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) := by
  have step : ∀ s, ω (Function.update (b ∘ J) s (D k ((b ∘ J) s))) =
      -∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) := by
    intro s
    have e : D k ((b ∘ J) s) = ∑ i, c i (J s) k • b i := hD k (J s)
    have h1 : ω (Function.update (b ∘ J) s (∑ i, c i (J s) k • b i)) =
        ∑ i, ω (Function.update (b ∘ J) s (c i (J s) k • b i)) :=
      ω.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i (J s) k • b i) (b ∘ J)
    rw [e, h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : ω (Function.update (b ∘ J) s (c i (J s) k • b i)) =
        c i (J s) k • ω (Function.update (b ∘ J) s (b i)) :=
      ω.map_update_smul (b ∘ J) s (c i (J s) k) (b i)
    have h3 : ((c (J s) i k : ℝ) : ℂ) • ω (Function.update (b ∘ J) s (b i)) =
        c (J s) i k • ω (Function.update (b ∘ J) s (b i)) :=
      algebraMap_smul ℂ (c (J s) i k) (ω (Function.update (b ∘ J) s (b i)))
    rw [h2, h3, hanti (J s) i k, neg_smul]
  rw [hinv k (b ∘ J), Finset.sum_congr rfl fun s _ => step s, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.Invsum
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KDKDelApply

section

@[expose] public section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Kabs

theorem kD_kDel_apply {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_

  rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]

end GlobalTheory.CompanionTheory.Kabs
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KugaAbsHolds

section

@[expose] public section

noncomputable section

open Fin Function

namespace PositivityTheory.Rg.Cz

theorem kIp_kD : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M), (∀ X x y, B (T X x) y = B x (T' X y)) → ∀ {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M), kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) :=
  GlobalTheory.CompanionTheory.KAdjoint.kIp_kD

theorem kDel_kD : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P), kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) - ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) :=
  GlobalTheory.CompanionTheory.KDelFormula.kDel_kD

theorem kD_kDel : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ} (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P), kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) :=
  GlobalTheory.CompanionTheory.Kabs.kD_kDel_apply

theorem kInv_sum : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M), (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) → ∀ {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M), (∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) → ∀ (k : γ) (J : Fin q → β), ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) :=
  GlobalTheory.CompanionTheory.Invsum.invariance_contraction

theorem kAlt_eq_zero : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M] {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ → ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 :=
  GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span

section
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem kHom {β γ : Type} [Fintype β] [Fintype γ] (b : β → P) (a r : P →ₗ[ℝ] Module.End ℂ M)
    (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ)
    (har : ∀ X Y, Commute (a X) (r Y)) (ha'r' : ∀ k, Commute (a' k) (r' k))
    (hca : ∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k)
    (hcr : ∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k)
    (hc : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (J : Fin q → β) :
    kDel (r - a) b (kD (a + r) ω) (b ∘ J) +
      ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) =
    ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) (ω (b ∘ J)) := by
  have hcomm : ∀ j i, (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) =
      ∑ k, (c j i k : ℂ) • (r' k - a' k) := by
    intro j i
    have e1 := (har (b j) (b i)).eq
    have e2 := (har (b i) (b j)).eq
    have h : (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) -
        ((r (b j) * r (b i) - r (b i) * r (b j)) - (a (b j) * a (b i) - a (b i) * a (b j))) =
        (a (b j) * r (b i) - r (b i) * a (b j)) - (r (b j) * a (b i) - a (b i) * r (b j)) := by
      simp only [LinearMap.add_apply, LinearMap.sub_apply]
      noncomm_ring
    rw [e1, e2, sub_self, sub_self, sub_zero, sub_eq_zero] at h
    rw [h, hcr, hca, ← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hsq : ∀ i, (r - a) (b i) * (a + r) (b i) = r (b i) * r (b i) - a (b i) * a (b i) := by
    intro i
    have e := (har (b i) (b i)).eq
    simp only [LinearMap.add_apply, LinearMap.sub_apply, mul_add, sub_mul, e]
    abel
  have hsq' : ∀ k, (r' k - a' k) * (a' k + r' k) = r' k * r' k - a' k * a' k := by
    intro k
    have e := (ha'r' k).eq
    simp only [mul_add, sub_mul, e]
    abel
  have hinv := kInv_sum b D c (fun k => a' k + r' k) hc hD ω hω
  rw [kDel_kD]
  generalize a + r = L at hcomm hsq ⊢
  generalize r - a = L' at hcomm hsq ⊢
  have step1 : ∑ i, L' (b i) (L (b i) (ω (b ∘ J))) -
      ∑ t, ∑ i, L' (b i) (L ((b ∘ J) t) (ω (Function.update (b ∘ J) t (b i)))) +
      ∑ s, ∑ i, L (b (J s)) (L' (b i) (ω (Function.update (b ∘ J) s (b i)))) =
      ∑ i, (L' (b i) * L (b i)) (ω (b ∘ J)) +
      ∑ s, ∑ i, (L (b (J s)) * L' (b i) - L' (b i) * L (b (J s)))
        (ω (Function.update (b ∘ J) s (b i))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finset.sum_sub_distrib, Function.comp_apply]
    abel
  rw [step1]
  simp_rw [hsq, hcomm]
  have step2 : ∀ s i, (∑ k, (c (J s) i k : ℂ) • (r' k - a' k)) (ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    intro s i
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, map_smul]
  simp_rw [step2]
  have step3 : ∑ s, ∑ i, ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, ∑ s, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    calc _ = ∑ s, ∑ k, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [step3]

  simp_rw [← map_sum, hinv, map_neg, ← Module.End.mul_apply, hsq']
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

omit [Module ℝ M] [IsScalarTower ℝ ℂ M] in
theorem kB_re_nonneg (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (x : M) :
    0 ≤ (B x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hpos x hx).le

theorem kT_nonneg {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P)
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (hB : ∀ x y, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (hTT : ∀ X x y, B (T X x) y = B x (T' X y))
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M) :
    0 ≤ (∑ J : Fin q → β, B (ω (b ∘ J))
      (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i)))))).re := by
  cases q with
  | zero => simp
  | succ n =>
    have h1 : ∀ J : Fin (n + 1) → β, (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i))))) =
        kD T (kDel T' b ω) (b ∘ J) := fun J => (kD_kDel T T' b ω (b ∘ J)).symm
    simp_rw [h1]
    have h2 : (∑ J : Fin (n + 1) → β, B (ω (b ∘ J)) (kD T (kDel T' b ω) (b ∘ J))) =
        starRingEnd ℂ (kIp B b (kD T (kDel T' b ω)) ω) := by
      unfold kIp

      rw [map_sum]
      exact Finset.sum_congr rfl fun J _ => hB _ _
    rw [h2, kIp_kD B b T T' hTT (kDel T' b ω) ω, Complex.conj_re, Complex.mul_re]
    have : (((n : ℂ) + 1)).im = 0 := by simp
    rw [this, zero_mul, sub_zero]
    have : (((n : ℂ) + 1)).re = (n : ℝ) + 1 := by simp
    rw [this]
    apply mul_nonneg (by positivity)
    unfold kIp
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun J _ => kB_re_nonneg B hpos _

end

theorem kugaAbs_holds : KugaAbs := by
  intro P _ _ M _ _ _ _ β γ _ _ b B a r a' r' D c hb hB hpos ha hr har ha'r' hca hcr hc hD hcas q ω hω X
  have hadj : ∀ X x y, B ((a + r) X x) y = B x ((r - a) X y) := by
    intro X x y
    simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add (f := _), map_sub, ha, hr]
    ring
  have hzero : kD (a + r) ω = 0 := by
    apply kAlt_eq_zero b hb
    have hK : ∀ J : Fin q → β, kDel (r - a) b (kD (a + r) ω) (b ∘ J) =
        ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)) -
        ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) :=
      fun J => eq_sub_of_add_eq (kHom b a r a' r' D c har ha'r' hca hcr hc hD ω hω J)
    have hA := kIp_kD B b (a + r) (r - a) hadj ω (kD (a + r) ω)
    have hT := kT_nonneg B b (a + r) (r - a) hB hpos hadj ω
    have h2 : ∀ J : Fin q → β, (B (ω (b ∘ J))
        (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
          Module.End ℂ M) (ω (b ∘ J)))).re ≤ 0 := by
      intro J
      rw [hB]
      simpa using hcas (ω (b ∘ J))
    have h1 : (kIp B b ω (kDel (r - a) b (kD (a + r) ω))).re ≤ 0 := by
      unfold kIp
      simp only [hK, map_sub, Finset.sum_sub_distrib, Complex.sub_re]
      have h3 := Finset.sum_nonpos (fun J (_ : J ∈ Finset.univ) => h2 J)
      rw [Complex.re_sum] at hT
      rw [Complex.re_sum, Complex.re_sum]
      linarith
    have h4 : (kIp B b (kD (a + r) ω) (kD (a + r) ω)).re ≤ 0 := by
      rw [hA, Complex.mul_re]
      have : (((q : ℂ) + 1)).im = 0 := by simp
      rw [this, zero_mul, sub_zero]
      have : (((q : ℂ) + 1)).re = (q : ℝ) + 1 := by simp
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    unfold kIp at h4
    rw [Complex.re_sum] at h4
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun I (_ : I ∈ Finset.univ) =>
      kB_re_nonneg B hpos (kD (a + r) ω (b ∘ I)))).1
      (le_antisymm h4 (Finset.sum_nonneg (fun I _ => kB_re_nonneg B hpos _)))
    intro I
    by_contra hI
    exact (hpos _ hI).ne' (h5 I (Finset.mem_univ _))
  have := congrArg (fun f => f X) hzero
  simpa [kD_apply] using this

end PositivityTheory.Rg.Cz

end
end
end
