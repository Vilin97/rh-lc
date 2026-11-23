module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
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
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NoOrthogonalIdempotents
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardPolynomialVanishesOnBicommutant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StarProjectionCommute
import Mathlib.Tactic.Linter.Style
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BicommutantRestrictionPrime

section

@[expose] public section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DirectFactor

theorem bicommutant_restriction_prime :
    ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0 := by
  intro G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy
  let W₀ : Submodule ℂ H := Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))
  have hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀ := fun g' h =>
    Submodule.subset_span ⟨(g', h), rfl⟩
  have hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀ := by
    intro g v hv
    obtain ⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k :=
      ⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩
    have hpg : π g = π (j (p g)) * π k := by
      have := congrArg π hg
      rwa [map_mul] at this
    have hKB : ∀ g', π k * π (j g') = π (j g') * π k := fun g' => by
      rw [← map_mul, ← map_mul, (hc g' k hk).eq]
    have hKy : π k * y = y * π k := hy (π k) hKB
    have a1 : ∀ v, π k (y v) = y (π k v) := fun v => DFunLike.congr_fun hKy v
    have a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v) := fun g' v =>
      DFunLike.congr_fun (hKB g') v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g', h⟩, rfl⟩ := hv
      have e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h)) := by
        rw [hpg, map_mul, map_mul]
        simp only [ContinuousLinearMap.mul_apply, a1, a2]
      simpa only [e] using hgen (p g * g') (π k h)
    | zero => simp
    | add u w _ _ hu hw => simpa only [map_add (f := _)] using W₀.add_mem hu hw
    | smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu
  have hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g', h⟩, rfl⟩
    exact DFunLike.congr_fun (hxy g') h
  rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop
  · exfalso
    apply hy0
    ext h
    have hm : y h ∈ W₀.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      simpa using hgen 1 h
    rw [hbot] at hm
    simpa using hm
  · ext h
    have hm : h ∈ W₀.topologicalClosure := by rw [htop]; trivial
    simpa using hker hm

end GlobalTheory.CompanionTheory.DirectFactor
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsMinimalOfOrthogonalBound

section

@[expose] public section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.OrthoFamily

theorem exists_minimal_of_no_family_below
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Set (Submodule ℂ H))
    (hcl : ∀ S ∈ L, IsClosed (S : Set H))
    (hinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) (n : ℕ) :
    ∀ S ∈ L, S ≠ ⊥ →
      (∀ f : Fin n → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → (∀ i, f i ≤ S) →
        ¬ Pairwise fun i k => f i ⟂ f k) →
      ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact (hS (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)).elim
  | succ n ih =>
    intro S hSL hS0 hS
    by_cases hmin : ∀ T ∈ L, T ≤ S → T = ⊥ ∨ T = S
    · exact ⟨S, hSL, hS0, hmin⟩
    · push_neg at hmin
      obtain ⟨T, hTL, hTS, hT0, hTne⟩ := hmin
      refine ih T hTL hT0 ?_
      intro f hfL hf0 hfT hpw
      haveI : CompleteSpace T := (hcl T hTL).completeSpace_coe
      have hR0 : S ⊓ Tᗮ ≠ ⊥ := by
        intro h
        apply hTne
        have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTS
        rw [inf_comm, h, sup_bot_eq] at hsup
        exact hsup
      have ho : ∀ j, (S ⊓ Tᗮ) ⟂ f j := fun j => inf_le_right.trans (Submodule.orthogonal_le (hfT j))
      apply hS (Fin.cons (S ⊓ Tᗮ) f)
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hinf S hSL T hTL
        | succ j => rw [Fin.cons_succ]; exact hfL j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hR0
        | succ j => rw [Fin.cons_succ]; exact hf0 j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact inf_le_left
        | succ j => rw [Fin.cons_succ]; exact (hfT j).trans hTS
      · intro i k hik
        induction i using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact absurd rfl hik
          | succ j =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact ho j
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact (ho j).symm
          | succ j' =>
            rw [Fin.cons_succ, Fin.cons_succ]
            exact hpw (fun h => hik (congrArg Fin.succ h))

theorem exists_minimal_of_orthogonal_bound :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  intro H _ _ _ L m S₀ hcl hinf hS₀ hS₀0 hfam
  exact exists_minimal_of_no_family_below L hcl hinf (m + 1) S₀ hS₀ hS₀0
    (fun f hfL hf0 _ => hfam f hfL hf0)

end GlobalTheory.CompanionTheory.OrthoFamily
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SchurOnMinimalSubspace

section

@[expose] public section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Factor

theorem schur_on_minimal_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ := by
  intro H _ _ _ N Q hstar hQc hQinv hmin A hcomm
  haveI : CompleteSpace Q := hQc.completeSpace_coe

  let σ : N → (Q →L[ℂ] Q) := fun T =>
    (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)

  have hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ := by
    intro T hT w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hw _ (hQinv _ (hstar T hT) u hu)

  have hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w) := by
    intro T hT w
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hQinv T hT _ (Submodule.starProjection_apply_mem Q w)
    · rw [← map_sub]
      exact hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)
  let B : Q →L[ℂ] Q := (Q.orthogonalProjection).comp (A.comp Q.subtypeL)
  have hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v) := fun _ => rfl
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ
    (by
      intro g
      refine ⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      change ⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])
    (by
      intro S hS hSinv
      have hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H) := by
        exact hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS
      have hle : S.map Q.subtype ≤ Q := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype := by
        rintro T hT _ ⟨x, hx, rfl⟩
        exact ⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩
      rcases hmin _ hclosed hle hinv with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : H) ∈ S.map Q.subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [eq_top_iff]
        intro x _
        have hx : (x : H) ∈ S.map Q.subtype := by
          rw [h]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy)
    B
    (by
      intro g
      ext v
      change Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))
      have h := congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)
      have h' : g.1 (A v) = A (g.1 v) := h
      rw [← h', hproj g.1 g.2])
  refine ⟨c, fun v hv => ?_⟩
  have h1 : Q.starProjection (A v) = c • v := by
    have := hB ⟨v, hv⟩
    rw [hc] at this
    simpa using this.symm
  rw [← h1]
  exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.CompanionTheory.Factor
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement

section

@[expose] public section

noncomputable section

open CompanionTheory.D.gk.admitted (stdPoly)
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl

theorem proj_comm_of_star_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : Set (H →L[ℂ] H)} (hN : ∀ T ∈ N, star T ∈ N) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hS : ∀ T ∈ N, ∀ v ∈ S, T v ∈ S) (T : H →L[ℂ] H) (hT : T ∈ N) :
    T * S.starProjection = S.starProjection * T := by
  ext v
  have hperp : ∀ u, u ∈ Sᗮ → T u ∈ Sᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    have h1 : ⟪w, T u⟫_ℂ = ⟪star T w, u⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hu _ (hS _ (hN T hT) _ hw)
  show T (S.starProjection v) = S.starProjection (T v)
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (hS T hT _ (S.starProjection_apply_mem v))
  rw [← map_sub]
  exact hperp _ (S.sub_starProjection_mem_orthogonal v)

theorem stFactor_from (h1 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0) (h2 : ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0) (h3 : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False) (h4 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q) (h5 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ) (h6 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W) : StFactor := by
  intro G G₁ H _ _ _ _ _ π hπ hirr j p hpj hcomm E hE
  obtain ⟨hE0, hEE, hEadj, hEc, m, hm⟩ := hE
  set ρ : G₁ →* (H →L[ℂ] H) := π.comp j with hρdef
  have hρ : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hπ _ v
  let N : Set (H →L[ℂ] H) := {T | ∀ g, T * ρ g = ρ g * T}
  let A : Set (H →L[ℂ] H) := {T | ∀ n ∈ N, n * T = T * n}
  have hN : ∀ T ∈ N, star T ∈ N := by
    intro T hT g
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, CompanionTheory.D.gk.admitted.FinOfPIAux.star_eq ρ hρ, inv_inv] at h
    exact h.symm
  have hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb n hn
    rw [← mul_assoc, ha n hn, mul_assoc, hb n hn, mul_assoc]
  have hSA : Set.range ρ ⊆ A := by
    rintro _ ⟨g, rfl⟩ n hn
    exact hn g
  have hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ Set.range ρ, x * s * y = 0) → x = 0 := by
    intro x _ y hy hy0 h
    exact h2 G G₁ H π hirr j p hpj hcomm x y (fun T hT => hy T hT) hy0 (fun g => h _ ⟨g, rfl⟩)
  have hPI : ∀ a : Fin m → (H →L[ℂ] H), (∀ i, a i ∈ A) → stdPoly E a = 0 :=
    fun a ha => h1 G₁ H ρ hρ E m hm a fun i T hT => ha i T hT
  let R : Submodule ℂ H := LinearMap.range (E : H →ₗ[ℂ] H)
  have hRmem : ∀ v, v ∈ R ↔ E v = v := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      exact DFunLike.congr_fun hEE w
    · intro h
      exact ⟨v, h⟩
  have hRcl : IsClosed (R : Set H) := by
    have : (R : Set H) = {v | E v = v} := Set.ext hRmem
    rw [this]
    exact isClosed_eq E.continuous continuous_id
  let L : Set (Submodule ℂ H) :=
    {S | IsClosed (S : Set H) ∧ (∀ T ∈ N, ∀ v ∈ S, T v ∈ S) ∧ S ≤ R}
  have hRL : R ∈ L := by
    refine ⟨hRcl, fun T hT v hv => ?_, le_rfl⟩
    rw [hRmem] at hv ⊢
    have := DFunLike.congr_fun (hEc T hT) v
    simp only [mul_apply_eq_comp] at this
    rw [← this, hv]
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hE0
    ext v
    have : E v ∈ R := ⟨v, rfl⟩
    rw [h] at this
    simpa using this
  have hLinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L := by
    rintro S ⟨hS1, hS2, hS3⟩ U ⟨hU1, hU2, hU3⟩
    refine ⟨hS1.inter U.isClosed_orthogonal, fun T hT v hv => ⟨hS2 T hT v hv.1, ?_⟩, inf_le_left.trans hS3⟩
    have hv2 : v ∈ Uᗮ := hv.2
    show T v ∈ Uᗮ
    rw [Submodule.mem_orthogonal] at hv2 ⊢
    intro w hw
    have h1 : ⟪w, T v⟫_ℂ = ⟪star T w, v⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hv2 _ (hU2 _ (hN T hT) _ hw)
  have hbound : ∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) →
      ¬ Pairwise fun i k => f i ⟂ f k := by
    intro f hf hf0 hp
    have hc : ∀ i, CompleteSpace (f i) := fun i => (hf i).1.completeSpace_coe
    refine h3 (H →L[ℂ] H) A (Set.range ρ) E m (fun i => (f i).starProjection) hAmul hSA hprime hPI
      (fun i n hn => proj_comm_of_star_closed hN (f i) (hf i).2.1 n hn) (fun i h0 => hf0 i ?_) (fun i => ?_) (fun i k hik => ?_)
      (fun i => ?_)
    · rw [Submodule.eq_bot_iff]
      intro v hv
      have := Submodule.starProjection_eq_self_iff.mpr hv
      rw [← this, h0]
      rfl
    · ext v
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ v) |> fun h => h
    · ext v
      have hv : (f k).starProjection v ∈ (f i)ᗮ :=
        (hp hik).symm ((f k).starProjection_apply_mem v)
      exact Submodule.eq_starProjection_of_mem_orthogonal (zero_mem _) (by simpa using hv)
    · ext v
      exact (hRmem _).mp ((hf i).2.2 ((f i).starProjection_apply_mem v))
  obtain ⟨Q, hQL, hQ0, hQmin⟩ := h4 H L m R (fun S hS => hS.1) hLinf hRL hR0 hbound
  obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  refine h6 G₁ H ρ hρ Q ξ hQL.1 hξ hξ0 (fun T hT v hv => hQL.2.1 T hT v hv) (fun g => ?_)
  obtain ⟨c, hc⟩ := h5 H N Q hN hQL.1 hQL.2.1
    (fun U hU1 hU2 hU3 => hQmin U ⟨hU1, hU3, hU2.trans hQL.2.2⟩ hU2) (ρ g) (fun T hT => hT g)
  exact ⟨c, hc ξ hξ⟩

theorem stFactor : StFactor :=
  stFactor_from GlobalTheory.CompanionTheory.Factor.stdPoly_bicomm GlobalTheory.CompanionTheory.DirectFactor.bicommutant_restriction_prime GlobalTheory.CompanionTheory.PrimeRing.StdChain.no_orthogonal_idempotents GlobalTheory.CompanionTheory.OrthoFamily.exists_minimal_of_orthogonal_bound GlobalTheory.CompanionTheory.Factor.schur_on_minimal_subspace GlobalTheory.CompanionTheory.CyclicScalar.exists_isIrredSubrep

end GlobalTheory.CompanionTheory.RgFl

end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatementStatement

section

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.FactorizationStatement : StFactor := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFactor | exact GlobalTheory.CompanionTheory.RgFl.stFactor | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFactor <;> assumption)
end
end
