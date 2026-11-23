module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootMapComplexLinearIndependentStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparableStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveMonicSeparableSpecializationStatement
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeries
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReduction

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.ShiftHomomorphism

noncomputable def shiftHom (D : ℕ) (c : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPowerSeries (Fin D) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.X i + MvPowerSeries.C (c i))

theorem shiftHom_X (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  simp [shiftHom]

theorem constantCoeff_comp_shiftHom (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [shiftHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    first | rfl | simp [MvPowerSeries.algebraMap_apply] | simp [Algebra.algebraMap_eq_smul_one]
  · intro i; simp [shiftHom]

theorem shiftHom_injective (D : ℕ) (c : Fin D → ℂ) : Function.Injective (shiftHom D c) := by
  let τ : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i))
  let τ' : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i))
  have hinv : τ'.comp τ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro i; simp [τ, τ']
  have hτ : Function.Injective τ := by
    intro a b h
    have := congrArg τ' h
    simpa [← AlgHom.comp_apply, hinv] using this
  have hfac : shiftHom D c = (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp τ := by
    apply MvPolynomial.algHom_ext; intro i; simp [shiftHom, τ]
  rw [hfac]
  exact (MvPolynomial.coe_injective _ _).comp hτ

end GlobalTheory.ShiftHomomorphism

namespace GlobalTheory


open GlobalTheory.ShiftHomomorphism in
theorem branches_of_unramified_point : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  intro D P c hP hsep
  haveI : IsDomain (MvPowerSeries (Fin D) ℂ) := NoZeroDivisors.to_isDomain _
  set ψ := shiftHom D c with hψ
  set Q := P.map ψ.toRingHom with hQ
  have hQm : Q.Monic := hP.map _
  have hred : Q.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)) = P.map (MvPolynomial.eval c) := by
    rw [hQ, Polynomial.map_map, constantCoeff_comp_shiftHom]
  obtain ⟨θ, hθi, hθr⟩ := GlobalTheory.T.exists_lifts_of_separable_reduction D Q hQm (by rw [hred]; exact hsep)
  have hroot : ∀ j, P.eval₂ ψ.toRingHom (θ j) = 0 := by
    intro j
    have := hθr j
    rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_map] at this
    exact this
  refine ⟨Q.natDegree, fun j => AdjoinRoot.liftAlgHom P ψ (θ j) (hroot j), ?_, ?_⟩
  · intro u hu
    obtain ⟨R, rfl⟩ := AdjoinRoot.mk_surjective u
    have hR : AdjoinRoot.mk P R = AdjoinRoot.mk P (R %ₘ P) := by
      rw [← AdjoinRoot.modByMonicHom_mk hP R, AdjoinRoot.mk_leftInverse hP]
    rw [hR] at hu ⊢
    by_contra hne
    have hR0 : R %ₘ P ≠ 0 := by
      intro h; apply hne; rw [h, map_zero]
    have hdeg : (R %ₘ P).natDegree < P.natDegree :=
      Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt R hP)
    have hz : (R %ₘ P).map ψ.toRingHom = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hθi ?_ ?_
      · intro j
        have := hu j
        simpa [AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval_map] using this
      · calc ((R %ₘ P).map ψ.toRingHom).natDegree ≤ (R %ₘ P).natDegree := Polynomial.natDegree_map_le
          _ < P.natDegree := hdeg
          _ = Q.natDegree := (hP.natDegree_map _).symm
          _ = Fintype.card (Fin Q.natDegree) := (Fintype.card_fin _).symm
    apply hR0
    exact Polynomial.map_injective _ (shiftHom_injective D c) (by rw [hz, Polynomial.map_zero])
  · intro j i
    simp [AdjoinRoot.liftAlgHom]
    rw [hψ]; exact shiftHom_X D c i

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReductionStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_formal_branches_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  first | exact @GlobalTheory.branches_of_unramified_point | exact GlobalTheory.branches_of_unramified_point | (intros; apply GlobalTheory.branches_of_unramified_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeriesStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem : ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  first | exact @GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | exact GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | (intros; apply GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionField

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem prod_mem_span_range_prod_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type*} [Fintype J] (g : J → A) (m : ℕ) (f : Fin m → A)
    (hf : ∀ l, f l ∈ Submodule.span R (Set.range g)) (y : A) :
    (∏ l, f l) * y ∈
      Submodule.span R (Set.range fun u : Fin m → J => (∏ l, g (u l)) * y) := by
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (hf l)
  have h : (∏ l, f l) * y = ∑ u : Fin m → J, (∏ l, c l (u l)) • ((∏ l, g (u l)) * y) := by
    simp_rw [← hc, Fintype.prod_sum, Finset.sum_mul, Algebra.smul_def, Finset.prod_mul_distrib,
      map_prod, mul_assoc]
  rw [h]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

theorem many_independent_products_in_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ)
    (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K),
    LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K,
    LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧
      v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  intro K _ _ D x hx J _ e he m hm
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hxQ : IsTranscendenceBasis ℚ x := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).1 hx
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 he
  obtain ⟨P, ψ, g, c, hPm, hψ, hψx, hg, hge, hsep⟩ := GlobalTheory.T.exists_primitive_monic_separable_specialization' K D x hxQ J e
  choose e' he' using fun j => (AlgHom.mem_range ψ).1 (hge j)
  have he'Q : LinearIndependent ℚ e' := by
    have h1 : LinearIndependent ℚ (fun j => g * e j) := by
      refine heQ.map' (LinearMap.mulLeft ℚ g) (LinearMap.ker_eq_bot.2 ?_)
      exact mul_right_injective₀ hg
    have h2 : (ψ.toLinearMap ∘ e') = fun j => g * e j := funext he'
    exact LinearIndependent.of_comp ψ.toLinearMap (h2 ▸ h1)
  obtain ⟨τ, hτX, hτq, hτind⟩ := GlobalTheory.T.adjoinRoot_complex_map_linearIndependent D P hPm
  have hPCm : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).Monic := hPm.map _
  have hsepC : ((P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map
      (MvPolynomial.eval (fun i => (c i : ℂ)))).Separable := by
    have h : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map (MvPolynomial.eval (fun i => (c i : ℂ))) =
        (P.map (MvPolynomial.eval c)).map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext <;> simp
    rw [h]; exact hsep.map
  let PC := P.map (MvPolynomial.map (algebraMap ℚ ℂ))
  obtain ⟨n, φ, hφinj, hφX⟩ := GlobalTheory.T.exists_formal_branches_of_separable_reduction D PC (fun i => (c i : ℂ)) hPCm hsepC
  let w : (Fin m → J) × (Fin D → Fin m) → AdjoinRoot P := fun ub =>
    (∏ l, e' (ub.1 l)) * ∏ i, AdjoinRoot.of P (MvPolynomial.X i) ^ (ub.2 i : ℕ)
  obtain ⟨κ, a, ha, hspan, hind⟩ := exists_linearIndependent' ℚ w
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let xC : Fin D → AdjoinRoot PC := fun i => AdjoinRoot.of PC (MvPolynomial.X i)
  let F : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun j => τ (e' j))
  let G : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun k => τ (w (a k)))
  haveI : Module.Finite ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : Module.Finite ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτspan : ∀ u ∈ Submodule.span ℚ (Set.range (w ∘ a)), τ u ∈ G := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact G.add_mem hy hz
    | smul q y _ hy => rw [hτq]; exact G.smul_mem _ hy
  have key := GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem D n (AdjoinRoot PC) φ xC (fun i => (c i : ℂ)) hφinj hφX F G m hm (by
    intro f b hf hb
    have h1 := prod_mem_span_range_prod_mul (R := ℂ) (fun j => τ (e' j)) m f hf (∏ i, xC i ^ b i)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨u, rfl⟩
    have hw : w (u, fun i => ⟨b i, hb i⟩) ∈ Submodule.span ℚ (Set.range (w ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    have h2 := hτspan _ hw
    simpa [w, map_prod, map_mul, map_pow, hτX, xC] using h2)
  have hFr : Module.finrank ℂ F = Fintype.card J := finrank_span_eq_card (hτind J e' he'Q)
  have hGr : Module.finrank ℂ G ≤ Fintype.card κ := finrank_range_le_card _
  let L : AdjoinRoot P →ₗ[ℚ] K := (LinearMap.mulLeft ℚ ((g ^ m)⁻¹)).comp ψ.toLinearMap
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot.2 ?_
    show Function.Injective (fun u => (g ^ m)⁻¹ * ψ u)
    exact (mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ hg))).comp hψ
  have hindK : LinearIndependent ℚ (L ∘ (w ∘ a)) := hind.map' L hL
  have hcard : Fintype.card J * m ^ D ≤ Fintype.card κ := hFr ▸ (key.trans hGr)
  let emb : Fin (Fintype.card J * m ^ D) ↪ κ :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨L ∘ (w ∘ a) ∘ emb, ?_, ?_⟩
  · exact (hindK.comp emb emb.injective).restrict_scalars' ℤ
  · intro s
    refine ⟨(a (emb s)).1, fun i => ((a (emb s)).2 i : ℕ), fun i => ((a (emb s)).2 i).isLt, ?_⟩
    simp only [Function.comp_apply, L, w, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, map_prod, map_pow, hψx, he', Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp

end GlobalTheory
end
end
