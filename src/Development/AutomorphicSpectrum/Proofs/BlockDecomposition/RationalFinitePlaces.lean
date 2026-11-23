module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPositiveHermitianFormStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Mathlib.RingTheory.PicardGroup
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerUnitaryIffStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryGroupCompactQuotientStatement
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizer

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TorCent

theorem finite_roots_of_unity (M : Type) [Field M] [NumberField M] :
    {ζ : M | ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_
  rintro ζ ⟨k, hk, h⟩
  refine ⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩
  have h1 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  exact (Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le

theorem exists_distinct_roots {M : Type} [Field M] {n : ℕ} (A : Matrix (Fin n) (Fin n) M)
    (hs : A.charpoly.Separable) (hsp : A.charpoly.Splits) :
    ∃ z : Fin n → M, Function.Injective z ∧ A.charpoly = ∏ a, (X - C (z a)) := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 hsp
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  refine ⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩
  rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r),
    Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]

theorem eq_diagonal_of_commute {M : Type} [Field M] {n : ℕ} {z : Fin n → M}
    (hz : Function.Injective z) {F : Matrix (Fin n) (Fin n) M}
    (h : F * diagonal z = diagonal z * F) : F = diagonal fun i => F i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have h2 : F i j * (z j - z i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))

theorem finite_torsion_centralizer : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  intro E _ _ n N hsep
  let M := N.val.charpoly.SplittingField
  haveI : NumberField M := NumberField.of_module_finite E M
  let f : E →+* M := algebraMap E M
  let A : Matrix (Fin n) (Fin n) M := N.val.map f
  have hA : A.charpoly = N.val.charpoly.map f := charpoly_map _ _
  have hs : A.charpoly.Separable := by rw [hA]; exact hsep.map
  have hsp : A.charpoly.Splits := by rw [hA]; exact SplittingField.splits _
  obtain ⟨z, hz, hprod⟩ := exists_distinct_roots A hs hsp
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs
    (by rw [charpoly_diagonal, hprod])
  let B : Matrix (Fin n) (Fin n) M := x.val
  let Bi : Matrix (Fin n) (Fin n) M := (x⁻¹).val
  have hBB : B * Bi = 1 := by simp [B, Bi]
  have hBB' : Bi * B = 1 := by simp [B, Bi]
  have hx' : diagonal z * B = B * A := hx
  have hx2 : Bi * diagonal z = A * Bi := by
    calc Bi * diagonal z = Bi * (diagonal z * B) * Bi := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  let F : GL (Fin n) E → Matrix (Fin n) (Fin n) M := fun g => B * g.val.map f * Bi
  have hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g := by
    intro g hg
    have h1 : g.val * N.val = N.val * g.val := congrArg Units.val hg
    have h2 : g.val.map f * A = A * g.val.map f := by
      simp only [A]
      rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    simp only [F]
    calc B * g.val.map f * Bi * diagonal z = B * (g.val.map f * A) * Bi := by
          rw [Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = diagonal z * (B * g.val.map f * Bi) := by
          rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc, Matrix.mul_assoc]
  have hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k) := by
    intro g k
    induction k with
    | zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [F, Units.val_mul]
      rw [Matrix.map_mul]
      calc B * (g ^ k).val.map f * Bi * (B * g.val.map f * Bi)
          = B * (g ^ k).val.map f * (Bi * B) * g.val.map f * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let φ : GL (Fin n) E → Fin n → M := fun g i => F g i i
  have hfin := Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M
  refine Set.Finite.of_injOn (f := φ) ?_ ?_ hfin
  · rintro g ⟨hg, ho⟩ i
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
    refine ⟨k, hk, ?_⟩
    have h1 : F g ^ k = 1 := by
      rw [hFpow, hgk]; simp [F, hBB, Matrix.map_one]
    rw [eq_diagonal_of_commute hz (hFc g hg), diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [φ] using h2
  · rintro g ⟨hg, -⟩ g' ⟨hg', -⟩ e
    have h1 : F g = F g' := by
      rw [eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]
      exact congrArg diagonal e
    have h2 : g.val.map f = g'.val.map f := by
      have h3 : Bi * F g * B = Bi * F g' * B := by rw [h1]
      have h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y := fun Y => by
        calc Bi * (B * Y * Bi) * B = (Bi * B) * Y * (Bi * B) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      simpa only [F, h4] using h3
    refine Units.ext ?_
    ext i j
    exact f.injective (congrFun (congrFun h2 i) j)

end GlobalTheory.CompanionTheory.TorCent
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.finite_torsion_centralizer_alt : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | exact GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer | (intros; apply GlobalTheory.CompanionTheory.TorCent.finite_torsion_centralizer <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFComm

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatCentComm

theorem commute_norm {G : Type} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (D g : G)
    (hg : g ∈ twCent θ D) : g * (D * θ D) = (D * θ D) * g := by
  have h1 : g * D = D * θ g := hg
  have h2 : θ g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg θ h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * θ D)
      = (D * θ D) * ((θ D)⁻¹ * (D⁻¹ * g * D) * θ D) := by group
    _ = _ := by rw [← h3]

theorem twCent_ratF_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
    (δ * thE E n δ).val.charpoly.Separable →
    ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  intro E _ _ _ n δ hs a ha b hb
  have hθ : ∀ g, thF E n (thF E n g) = g :=
    GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [GlobalTheory.MassNorm.thF_ratF, ← map_mul]
    exact h1
  have hc : ∀ g ∈ twCent (thF E n) (ratF E n δ),
      Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val := fun g hg => by
    change g.val * _ = _ * g.val
    rw [← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]
  obtain ⟨p, hp⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)
  obtain ⟨q, hq⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]

end GlobalTheory.CompanionTheory.RatCentComm
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFCommStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.twCent_comm_of_charpoly_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable →
  ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  first | exact @GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | exact GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | (intros; apply GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatFinG

theorem selberg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U Γ : Subgroup G) (C : Set G) (n₀ : G)
    (hC : IsCompact C) (hcov : ∀ g ∈ U, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (hn : n₀ ∈ Γ) :
    ∃ C' : Set G, IsCompact C' ∧ ∀ t ∈ U, t * n₀ = n₀ * t → ∃ γ ∈ Γ, γ * n₀ = n₀ * γ ∧ ∃ c ∈ C', t = γ * c := by
  have hX : IsCompact ((fun p : G × G => p.1 * n₀ * p.2⁻¹) '' (C ×ˢ C)) :=
    (hC.prod hC).image (by fun_prop)
  have hF := hfin _ hX
  let rep : G → G := fun f => if h : ∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f then h.choose else 1
  have hrep : ∀ f, (∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f) → rep f ∈ Γ ∧ (rep f)⁻¹ * n₀ * rep f = f := by
    intro f h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨⋃ f ∈ (Γ : Set G) ∩ _, (fun c => rep f * c) '' C, hF.isCompact_biUnion fun f _ =>
    hC.image (by fun_prop), ?_⟩
  intro t ht hcomm
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  set f := γ⁻¹ * n₀ * γ with hf
  have hfc : f = c * n₀ * c⁻¹ := by
    have e : γ⁻¹ * n₀ * γ * c = c * n₀ := by
      have : n₀ * (γ * c) = γ * c * n₀ := hcomm.symm
      calc γ⁻¹ * n₀ * γ * c = γ⁻¹ * (n₀ * (γ * c)) := by group
        _ = γ⁻¹ * (γ * c * n₀) := by rw [this]
        _ = c * n₀ := by group
    rw [hf, eq_mul_inv_iff_mul_eq, e]
  have hfΓ : f ∈ Γ := mul_mem (mul_mem (inv_mem hγ) hn) hγ
  obtain ⟨h1, h2⟩ := hrep f ⟨γ, hγ, rfl⟩
  refine ⟨γ * (rep f)⁻¹, mul_mem hγ (inv_mem h1), ?_, rep f * c, ?_, by group⟩
  · have e : (rep f)⁻¹ * n₀ * rep f = γ⁻¹ * n₀ * γ := h2
    calc γ * (rep f)⁻¹ * n₀ = γ * ((rep f)⁻¹ * n₀ * rep f) * (rep f)⁻¹ := by group
      _ = γ * (γ⁻¹ * n₀ * γ) * (rep f)⁻¹ := by rw [e]
      _ = n₀ * (γ * (rep f)⁻¹) := by group
  · refine Set.mem_biUnion (x := f) ⟨hfΓ, ⟨(c, c), ⟨hc, hc⟩, hfc.symm⟩⟩ ⟨c, hc, rfl⟩

abbrev gam1 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) : Subgroup (GL (Fin n) (Af E)) :=
  (ratF E n).range ⊓ twCent (thF E n) (ratF E n δ)

theorem algebraMap_inj (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

theorem ratF_injective (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    Function.Injective (ratF E n) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => algebraMap_inj E ?_)
  exact congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h

theorem ratF_mem_UJ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E)
    (γ : GL (Fin n) E) : ratF E n γ ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ↔
      γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H := by
  have hi := algebraMap_inj E
  have hv : (ratF E n γ).val = γ.val.map (algebraMap E (Af E)) := rfl
  have hcT : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.val.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val).map (algebraMap E (Af E)) := by
    refine Matrix.ext fun i j => ?_
    exact conjFin_algebraMap _ _
  change cT _ (ratF E n γ).val * _ * (ratF E n γ).val = _ ↔ cT _ γ.val * H * γ.val = H
  rw [hv, hcT, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => Matrix.map_injective hi h, fun h => by rw [h]⟩

theorem factor (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (hδ : polE δ ∈ Ell E n) :
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧ ∀ t ∈ twCent (thF E n) (ratF E n δ), ∃ γ ∈ gam1 E n δ, ∃ c ∈ C, t = γ * c) ∧
    (∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((gam1 E n δ : Set (GL (Fin n) (Af E))) ∩ X).Finite) ∧
    {γ : GL (Fin n) (Af E) | γ ∈ gam1 E n δ ∧ IsOfFinOrder γ}.Finite := by
  have hs : (δ * thE E n δ).val.charpoly.Separable := hδ.2.2.1
  have hr : ∀ τ : E →+* ℂ, ∀ z ∈ ((δ * thE E n δ).val.charpoly.map τ).roots, ‖z‖ = 1 := hδ.2.2.2
  obtain ⟨H, hu, hh, hN, hp⟩ := GlobalTheory.T.exists_positive_hermitian_form E n _ hs hr
  obtain ⟨⟨C₀, hC₀, hcov⟩, hfin⟩ := GlobalTheory.T.unitary_group_compact_quotient E n H hu hh hp
  have hc := GlobalTheory.T.twisted_centralizer_unitary_iff E n δ H hs hu hN
  set U := UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) with hU
  set Γ := (UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H).map (ratF E n) with hΓ
  have hΓfin : ∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((Γ : Set (GL (Fin n) (Af E))) ∩ X).Finite := by
    intro X hX
    refine ((hfin X hX).image (ratF E n)).subset ?_
    rintro _ ⟨⟨γ, hγ, rfl⟩, hx⟩
    exact ⟨γ, ⟨hγ, hx⟩, rfl⟩
  have hsub : ∀ y ∈ gam1 E n δ, y ∈ Γ := by
    rintro _ ⟨⟨γ, rfl⟩, ht⟩
    exact ⟨γ, (ratF_mem_UJ E n H γ).1 ((hc _).1 ht).1, rfl⟩
  obtain ⟨C', hC', hsel⟩ := selberg U Γ C₀ (ratF E n (δ * thE E n δ)) hC₀
    (fun g hg => by
      obtain ⟨γ, hγ, k, hk, e⟩ := hcov g hg
      exact ⟨_, ⟨γ, hγ, rfl⟩, k, hk, e⟩)
    hΓfin ⟨_, hN, rfl⟩
  refine ⟨⟨C', hC', fun t ht => ?_⟩, fun X hX => (hΓfin X hX).subset fun y hy => ⟨hsub y hy.1, hy.2⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (hc t).1 ht
    obtain ⟨γ, hγ, hcm, c, hc', e⟩ := hsel t h1 h2
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact ⟨ratF E n γ₀, ⟨⟨γ₀, rfl⟩, (hc _).2 ⟨(ratF_mem_UJ E n H γ₀).2 hγ₀, hcm⟩⟩, c, hc', e⟩
  · refine ((GlobalTheory.T.finite_torsion_centralizer_alt E n _ hs).image (ratF E n)).subset ?_
    rintro y ⟨hy, hfo⟩
    obtain ⟨⟨γ, rfl⟩, ht⟩ := hy
    refine ⟨γ, ⟨ratF_injective E n ?_, ?_⟩, rfl⟩
    · rw [map_mul (ratF E n) γ, map_mul (ratF E n) _ γ]
      exact ((hc _).1 ht).2
    · exact (ratF_injective E n).isOfFinOrder_iff.1 hfo

theorem mem_twCent_thP {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (x : GL (Fin a) (Af E)) (y : GL (Fin b) (Af E))
    (p : Gf E a b) : p ∈ twCent (thP E a b) (x, y) ↔ p.1 ∈ twCent (thF E a) x ∧ p.2 ∈ twCent (thF E b) y := by
  change p * (x, y) = (x, y) * thP E a b p ↔ p.1 * x = x * thF E a p.1 ∧ p.2 * y = y * thF E b p.2
  exact Prod.ext_iff

theorem mem_gam {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (p : Gf E a b) : p ∈ gam δ₁ δ₂ ↔ p.1 ∈ gam1 E a δ₁ ∧ p.2 ∈ gam1 E b δ₂ := by
  rw [gam, Subgroup.mem_inf, mem_twCent_thP, gam1, gam1, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨q, rfl⟩, h1, h2⟩
    exact ⟨⟨⟨q.1, rfl⟩, h1⟩, ⟨q.2, rfl⟩, h2⟩
  · rintro ⟨⟨⟨q₁, e₁⟩, h1⟩, ⟨q₂, e₂⟩, h2⟩
    exact ⟨⟨(q₁, q₂), Prod.ext e₁ e₂⟩, h1, h2⟩

theorem ratFin : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  intro E _ _ _ _ a b δ₁ δ₂ h₁ h₂
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  obtain ⟨⟨C₁, hC₁, hc₁⟩, hf₁, ht₁⟩ := factor E a δ₁ h₁
  obtain ⟨⟨C₂, hC₂, hc₂⟩, hf₂, ht₂⟩ := factor E b δ₂ h₂
  have hs₁ : (δ₁ * thE E a δ₁).val.charpoly.Separable := h₁.2.2.1
  have hs₂ : (δ₂ * thE E b δ₂).val.charpoly.Separable := h₂.2.2.1
  have hK₁ := GlobalTheory.T.finite_kernel_compact_open E a
  have hK₂ := GlobalTheory.T.finite_kernel_compact_open E b
  have hKc : (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (Kf E a : Set _) ×ˢ (Kf E b : Set _) :=
    Subgroup.coe_prod _ _
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.1.prod hK₂.1
  have hKcp : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.2.prod hK₂.2
  have hcl : IsClosed ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    have e : ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) =
        (twCent (thF E a) (ratF E a δ₁) : Set _) ×ˢ (twCent (thF E b) (ratF E b δ₂) : Set _) := by
      ext p
      exact mem_twCent_thP _ _ p
    rw [e]
    exact (GlobalTheory.MassNorm.isClosed_twCent_thF E a _).prod (GlobalTheory.MassNorm.isClosed_twCent_thF E b _)
  set T := twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) with hTdef
  have hcomm : ∀ p ∈ T, ∀ q ∈ T, p * q = q * p := fun p hp q hq => by
    rw [hTdef, mem_twCent_thP] at hp hq
    exact Prod.ext (GlobalTheory.T.twCent_comm_of_charpoly_separable E a δ₁ hs₁ _ hp.1 _ hq.1) (GlobalTheory.T.twCent_comm_of_charpoly_separable E b δ₂ hs₂ _ hp.2 _ hq.2)
  have hle : gam δ₁ δ₂ ≤ T := fun p hp => hp.2
  have hcov : ∀ t ∈ T, ∃ γ ∈ gam δ₁ δ₂, ∃ c ∈ C₁ ×ˢ C₂, t = γ * c := fun t ht => by
    rw [hTdef, mem_twCent_thP] at ht
    obtain ⟨γ₁, hγ₁, c₁, hcc₁, e₁⟩ := hc₁ _ ht.1
    obtain ⟨γ₂, hγ₂, c₂, hcc₂, e₂⟩ := hc₂ _ ht.2
    exact ⟨(γ₁, γ₂), (mem_gam δ₁ δ₂ _).2 ⟨hγ₁, hγ₂⟩, (c₁, c₂), ⟨hcc₁, hcc₂⟩, Prod.ext e₁ e₂⟩
  have hfin : ∀ X : Set (Gf E a b), IsCompact X → ((gam δ₁ δ₂ : Set (Gf E a b)) ∩ X).Finite := fun X hX => by
    have h1 := hf₁ _ (hX.image continuous_fst)
    have h2 := hf₂ _ (hX.image continuous_snd)
    refine (h1.prod h2).subset ?_
    rintro p ⟨hp, hx⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    exact ⟨⟨hp'.1, ⟨p, hx, rfl⟩⟩, hp'.2, ⟨p, hx, rfl⟩⟩
  have htor : {γ : Gf E a b | γ ∈ gam δ₁ δ₂ ∧ IsOfFinOrder γ}.Finite := by
    refine (ht₁.prod ht₂).subset ?_
    rintro p ⟨hp, hfo⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
    have e' : p.1 ^ k = 1 ∧ p.2 ^ k = 1 := Prod.ext_iff.1 e
    exact ⟨⟨hp'.1, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.1⟩⟩, hp'.2, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.2⟩⟩
  haveI : T2Space (Gf E a b) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have hmain := GlobalTheory.T.finite_torsion_lattice_compact (Gf E a b) ((Kf E a).prod (Kf E b)) T (gam δ₁ δ₂)
    (C₁ ×ˢ C₂) hKo hKcp hcl hcomm hle (hC₁.prod hC₂) hcov hfin htor
  exact ⟨⟨hcomm, hmain.1⟩, hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩

end GlobalTheory.CompanionTheory.RatFinG
end
end
end
