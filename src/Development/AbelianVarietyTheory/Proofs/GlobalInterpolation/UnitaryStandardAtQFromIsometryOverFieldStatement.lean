module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprimeStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprime

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomKapi


open Formalism.L2.Th1.H in
theorem nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (S M : AddSubgroup V) {z : V} (hz : z ∈ M) :
    relIdx S M • z ∈ S := by
  have h := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)
  have h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S := AddSubgroup.mem_addSubgroupOf.1 h
  simpa [relIdx, AddSubgroup.relIndex] using h2

theorem denom_prime_to : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D cc δ B hcc q _ hcop u hn hnq G hG x hx
  set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) with hndef
  set N := Ideal.absNorm cc with hNdef
  have hq : q.Prime := Fact.out
  have hnc : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
  refine ⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B

  have hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀
  have hw₀mem : w₀ ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨_, hNc, rfl⟩
  have hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx
  have hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E)) := by
    rw [map_smul]
    exact congrArg (w₀ • ·) (B.gC_spec x)
  have hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) := by
    rw [hgC, map_smul, hG]
  have hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) :=
    ⟨_, ⟨_, hz, rfl⟩, rfl⟩
  have hS := nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM
  rw [← hndef, hu] at hS
  have hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice := by
    have := hS w (Set.mem_univ w)
    simpa using this
  obtain ⟨c, -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)
  have hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E) := by
    apply mul_left_cancel₀ hδ
    rw [← hc', hw₀]
    push_cast
    simp only [map_mul, map_natCast, nsmul_eq_mul]
    ring
  have hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K) :=
    Subtype.coe_injective (D.host.φ₀.injective hC)
  exact ⟨c, hK.symm⟩

end GlobalTheory.MomKapi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprimeStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.MomKapi.denom_prime_to | exact GlobalTheory.MomKapi.denom_prime_to | (intros; apply GlobalTheory.MomKapi.denom_prime_to <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImage

section

@[expose] public section

namespace GlobalTheory

theorem linearEquiv_descends_of_preserves_image {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (h : ∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) :
    ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧
      LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
        f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  classical
  let F : (ι → K) → (ι → ℂ) := fun v i => f (v i)
  have hFinj : Function.Injective F := by
    intro v w hvw
    funext i
    exact f.injective (congrFun hvw i)
  choose G hG using h
  have hG' : ∀ v, u (F v) = F (G v) := hG
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w; funext i; simp [F]
  have hFsmul : ∀ (c : K) v, F (c • v) = f c • F v := by
    intro c v; funext i; simp [F]
  let Gl : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := G
      map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add (f := _), hG', hG', hFadd])
      map_smul' := fun c v => hFinj (by
        simp only [RingHom.id_apply]
        rw [← hG', hFsmul, map_smul, hG', hFsmul]) }
  have hGl : ∀ v, Gl v = G v := fun _ => rfl
  have hinj : Function.Injective Gl := by
    intro v w hvw
    apply hFinj
    apply u.injective
    rw [hG', hG']
    exact congrArg F hvw
  let g : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo Gl hinj
  have hg : ∀ v, g v = G v := fun v => by
    simp [g, hGl]
  have hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij; simp [F]
    · simp [F, Pi.single_eq_of_ne hij]
  have hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
      (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f := by
    ext i j
    have := congrFun (hG' (Pi.single j 1)) i
    rw [hsingle j] at this
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simp only [LinearEquiv.coe_coe, hg]
    exact this
  refine ⟨g, fun v => ?_, ?_⟩
  · rw [hg]; exact hG v
  · rw [← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      LinearMap.det_toMatrix']

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImageStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectors

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectorsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.LatDesc.unitary_maps_rational | exact GlobalTheory.LatDesc.unitary_maps_rational | (intros; apply GlobalTheory.LatDesc.unitary_maps_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverField

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapIsom

theorem form_u (D : D7) (L : PeriodPair) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hu : Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, u x w * (starRingEnd ℂ) (u y w) = ∑ w, x w * (starRingEnd ℂ) (y w) := by
  have h := hu x y
  change Formalism.L2.Th1.H.matH (hOne L _) (u x) (u y) = Formalism.L2.Th1.H.matH (hOne L _) x y at h
  rw [matH_hOne, matH_hOne] at h
  have hA : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos L).ne'
  exact (div_left_inj' hA).1 h

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hqc ι u hu h1 h2 h3
  obtain ⟨G, hG, hdet⟩ := GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) u
    (GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors D cc δ B hcc u h1)
  have hG' : ∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E))
      = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E) := fun v => hG v
  let γ : IsoK D :=
    { g := B.γ₀.g.trans G
      isom := by
        intro x y
        apply D.host.φ₀.injective
        have e1 := form_u D B.L u hu (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))
          (fun w => D.host.φ₀ ((B.γ₀.g y w : D.host.K) : D.host.E))
        rw [hG', hG'] at e1

        rw [← B.γ₀.isom x y, map_sum, map_sum]
        simp only [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
        exact e1 }
  refine ⟨γ, ⟨fun x hx => GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime D cc δ B hcc q hqc u h1 h2 G hG' x hx,
    fun v hv => GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt D cc δ B hcc hδ q hqc u hu h1 h2 h3 G hG' v hv⟩, ?_⟩
  have hd : γ.detRel B.γ₀ = LinearMap.det (G : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) := by
    have e : (B.γ₀.g.symm.trans γ.g) = G := by
      apply LinearEquiv.ext; intro v
      show G (B.γ₀.g (B.γ₀.g.symm v)) = G v
      rw [LinearEquiv.apply_symm_apply]
    unfold IsoK.detRel
    rw [e]
  rw [hdet, hd]
  rfl

end GlobalTheory.KapIsom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverFieldStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.unitary_standard_at_q_from_isometry_over_field : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.KapIsom.main | exact GlobalTheory.KapIsom.main | (intros; apply GlobalTheory.KapIsom.main <;> assumption)
end
end
