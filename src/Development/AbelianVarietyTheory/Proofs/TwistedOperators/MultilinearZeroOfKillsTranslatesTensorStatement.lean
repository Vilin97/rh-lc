module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]

  simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity


open IrreducibleUnitaryDensity in
theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := open IrreducibleUnitaryDensity in by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensityStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.irreducibleUnitary_vector_density : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) → ∀ (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)), (∀ g, ∑ j, Λ j (π g (a j)) = 0) → ∀ φ u : H, ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  first | exact @GlobalTheory.irreducibleUnitary_density | exact GlobalTheory.irreducibleUnitary_density | (intros; apply GlobalTheory.irreducibleUnitary_density <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensorStatement

section

@[expose] public section

open scoped InnerProductSpace
-- `MultilinearMap` now takes the scalar ring hom explicitly.  Preserve the
-- older `MultilinearMap R M N` spelling used by the statement in this file.
local notation "MultilinearMap " "ℂ " M:max N:max =>
  _root_.MultilinearMap (RingHom.id ℂ) M N

namespace GlobalTheory.DensityMultiPlace

private theorem multilinear_translates_zero_local : ∀ (ι : Type) [Fintype ι]
    (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)]
    (π : ∀ i, G i →* (H i →L[ℂ] H i)) (hu : ∀ i g x, ‖π i g x‖ = ‖x‖)
    (hs : ∀ i, ∀ B : H i →L[ℂ] H i,
      (∀ g, B.comp (π i g) = (π i g).comp B) →
        ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i))
    (Sm : ∀ i, Submodule ℂ (H i)) (hd : ∀ i, Dense (Sm i : Set (H i)))
    (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i)
    (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ)
    (hL : ∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖)
    (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i)
    (hv : ∀ g : ∀ i, G i,
      ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0)
    (φ : ∀ i, H i) (u : ∀ i, Sm i),
    (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  intro ι _ H _ _ _ G _ π hu hs Sm hd hinv L C hL n c v hv φ u
  classical
  let w : Fin n → (∀ i, G i) → ∀ i, Sm i :=
    fun j g i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩
  have key : ∀ s : Finset ι, ∀ (g : ∀ i, G i) (u : ∀ i, Sm i),
      ∑ j, c j * (∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) * L (s.piecewise u (w j g)) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro g u
      simpa [w] using hv g
    · intro a s ha ih g u
      have hnorm : ∀ (m : ∀ i, Sm i) (x : Sm a),
          ∏ i, ‖((Function.update m a x) i : H i)‖
            = (∏ i ∈ Finset.univ.erase a, ‖(m i : H i)‖) * ‖x‖ := by
        intro m x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self,
          mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hbd : ∀ j (x : Sm a), ‖L.toLinearMap (s.piecewise u (w j g)) a x‖
          ≤ (C * ∏ i ∈ Finset.univ.erase a,
            ‖((s.piecewise u (w j g)) i : H i)‖) * ‖x‖ := by
        intro j x
        rw [MultilinearMap.toLinearMap_apply, mul_assoc, ← hnorm]
        exact hL _
      have hden : DenseRange (Sm a).subtypeL := (hd a).denseRange_val
      have hui : IsUniformInducing (Sm a).subtypeL :=
        isUniformEmbedding_subtype_val.isUniformInducing
      let Λ : Fin n → (H a →L[ℂ] ℂ) := fun j =>
        (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) •
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)).extend
            (Sm a).subtypeL
      have hΛ : ∀ j (x : Sm a), Λ j (x : H a) =
          (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) *
            L (Function.update (s.piecewise u (w j g)) a x) := by
        intro j x
        have this := ContinuousLinearMap.extend_eq
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)) hden hui x
        simp only [Λ, ContinuousLinearMap.smul_apply, smul_eq_mul]
        erw [this]
        rw [LinearMap.mkContinuous_apply, MultilinearMap.toLinearMap_apply]
      have hupd : ∀ j (k : G a), s.piecewise u (w j (Function.update g a k)) =
          Function.update (s.piecewise u (w j g)) a
            ⟨π a k (v j a), hinv a k _ (v j a).2⟩ := by
        intro j k
        funext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.piecewise_eq_of_notMem _ _ _ ha, w]
        · rw [Function.update_of_ne hia]
          by_cases his : i ∈ s
          · simp [Finset.piecewise_eq_of_mem _ _ _ his]
          · simp [Finset.piecewise_eq_of_notMem _ _ _ his, w, Function.update_of_ne hia]
      have hG : ∀ k : G a, ∑ j, Λ j (π a k (v j a)) = 0 := by
        intro k
        have h1 := ih (Function.update g a k) u
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (π a k (v j a) : H a) =
          ((⟨π a k (v j a), hinv a k _ (v j a).2⟩ : Sm a) : H a) from rfl,
          hΛ, hupd, mul_assoc]
      have h2 := GlobalTheory.T.irreducibleUnitary_vector_density
        (H a) (G a) (π a) (hu a) (hs a) n (fun j => (v j a : H a)) Λ hG (φ a) (u a)
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΛ, Finset.prod_insert ha, Finset.piecewise_insert]
      ring
  have h := key Finset.univ (fun _ => 1) u
  simp only [Finset.piecewise_univ] at h
  rw [Finset.sum_mul]
  rw [← h]

end GlobalTheory.DensityMultiPlace


theorem _root_.GlobalTheory.T.multilinear_zero_of_kills_translates_tensor : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  exact @GlobalTheory.DensityMultiPlace.multilinear_translates_zero_local
end
end
