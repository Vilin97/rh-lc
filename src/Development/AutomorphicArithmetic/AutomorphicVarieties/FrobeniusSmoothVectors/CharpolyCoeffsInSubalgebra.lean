module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AbEval
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimQuotientBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EqIdempotentCutOfComplementKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TriangularRepresentationDiagonal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocalDeformationTraceModMaximal

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.local_deformation_trace_mod_maximal :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (maximalIdeal O).map (algebraMap O L.R) ≤ maximalIdeal L.R ∧ (∀ (g : F.G0) (i : Fin n), F.Ψ g = 1 → L.ρ.r g i i - 1 ∈ maximalIdeal L.R) ∧ ∀ (P : Ideal L.R) [IsLocalRing (L.R ⧸ P)], (maximalIdeal O).map (algebraMap O L.R) ≤ P → Finite (ResidueField (L.R ⧸ P)) ∧ (∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P)) ∧ (L.ρ.map (Ideal.Quotient.mk P)).Cont (maximalIdeal (L.R ⧸ P)) ∧ ∃ f : ResidueField O →+* L.R ⧸ P, (∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a)) ∧ ((L.ρ.map (Ideal.Quotient.mk P)).map (residue (L.R ⧸ P))).IsBar ((residue (L.R ⧸ P)).comp f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  obtain ⟨hc, hb, -⟩ := UpperTheory.V.Fr.loc_rho hF hn S x L
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O L.R a ∈ maximalIdeal L.R := fun a ha => by
    have h1 : algebraMap O L.O' a ∈ maximalIdeal L.O' := L.unr ▸ Ideal.mem_map_of_mem _ ha
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ h1
  haveI hloc : IsLocalHom (algebraMap O L.R) := ⟨fun a ha => by
    by_contra hna
    exact hm a hna ha⟩
  have hb0 := hb (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _
  refine ⟨Ideal.map_le_iff_le_comap.2 hm, fun g i hg => ?_, fun P _ hP => ?_⟩
  · have h := hb0.1 g i
    rw [hg, NRep.map_r] at h
    rw [← residue_eq_zero_iff, map_sub, h]
    simp
  haveI hlocP : IsLocalHom (Ideal.Quotient.mk P) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmP : ∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P) :=
    fun y hy => map_nonunit (Ideal.Quotient.mk P) y hy
  have hle : ∀ N : ℕ, maximalIdeal L.R ^ N ≤ (maximalIdeal (L.R ⧸ P) ^ N).comap (Ideal.Quotient.mk P) := fun N =>
    le_trans (Ideal.pow_right_mono (fun y hy => hmP y hy) N) (Ideal.le_comap_pow _ N)
  refine ⟨?_, hmP, ⟨fun i j N => ?_, fun v i N => ?_⟩, ?_⟩
  · haveI : Finite (ResidueField L.R) := Finite.of_surjective _ (resMap_bijective L.O' L.R).2
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk P)) fun y => ?_
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨residue _ y, ResidueField.map_residue _ _⟩
  · exact (hc.1 i j N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · exact (hc.2 v i N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · let f : ResidueField O →+* L.R ⧸ P :=
      Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk P).comp (algebraMap O L.R))
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hP (Ideal.mem_map_of_mem _ ha))
    have hf : ∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a) := fun a => rfl
    have key : ∀ (y : L.R) (t : ResidueField O), residue L.R y = ResidueField.map (algebraMap O L.R) t →
        residue (L.R ⧸ P) (Ideal.Quotient.mk P y) = residue (L.R ⧸ P) (f t) := fun y t h => by
      obtain ⟨a, rfl⟩ := residue_surjective t
      rw [← hf, ← ResidueField.map_residue (Ideal.Quotient.mk P), h, ResidueField.map_residue,
        ResidueField.map_residue]
    exact ⟨f, hf, fun g i => key _ _ (hb0.1 g i), fun v i g => key _ _ (hb0.2 v i g)⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MaximalIdealImageKills

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.maximal_ideal_image_kills :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ {Q : Type} [CommRing Q] [IsLocalRing Q] [IsNoetherianRing Q] (f : ResidueField O →+* Q) (φ : S.A →+* Q), (∀ a : O, φ (algebraMap O S.A a) = f (residue O a)) → (∀ y ∈ S.mB, φ (S.inc y) ∈ maximalIdeal Q) → (S.u.map φ).triM = ⊥ → (S.u.map φ).IsBar f → ∀ y ∈ S.mB, φ (S.inc y) = 0 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ f φ hf hm htri hbar y hy
  have hK : (⨅ N : ℕ, maximalIdeal Q ^ N) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top
  rw [← Ideal.mem_bot, ← hK, Ideal.mem_iInf]
  intro N
  obtain ⟨M, hM⟩ := (cont_u hF hn S).2.2.2 0 N
  obtain ⟨z, hz, hyz⟩ := y.2 (M + 1)
  let zB : S.B := ⟨z, le_adicClosure _ hz⟩
  have hd : y - zB ∈ S.mB := by
    show (y : S.R) - z ∈ maximalIdeal S.R
    exact Ideal.pow_le_self (Nat.succ_ne_zero M) hyz
  have hzB : zB ∈ S.mB := by
    have := sub_mem hy hd
    simpa using this
  have hz0 : φ (S.inc zB) = 0 := by
    obtain ⟨c, hc⟩ := adjoin_image_in_residue_range S f φ hf htri hbar (S.inc zB) hz
    have h1 := hm zB hzB
    rw [← hc] at h1 ⊢
    by_cases h0 : c = 0
    · rw [h0, map_zero]
    · exact absurd ((IsUnit.mk0 c h0).map f) h1
  have hgr : S.inc (y - zB) ∈ S.gr 0 := by
    have h1 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
    have h2 := Submodule.smul_mem _ (y - zB) h1
    rw [Algebra.smul_def, mul_one] at h2
    exact h2
  have ha := hM _ hgr (Ideal.pow_le_pow_right (Nat.le_succ M) hyz)
  have hle : S.mB ^ N ≤ (maximalIdeal Q ^ N).comap (φ.comp (S.inc : S.B →+* S.A)) :=
    le_trans (Ideal.pow_right_mono (fun b hb => hm b hb) N) (Ideal.le_comap_pow _ N)
  have key : φ (S.inc (y - zB)) ∈ maximalIdeal Q ^ N := by
    refine Submodule.smul_induction_on (p := fun a => φ a ∈ maximalIdeal Q ^ N) ha ?_ ?_
    · intro b hb x _
      rw [Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hle hb)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact add_mem ha hb
  rwa [map_sub, map_sub, hz0, sub_zero] at key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResiduallyDiagonalRepresentation

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.residually_diagonal_representation :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] (f : k →+* Q) (ρ : NRep F n Q), (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → (∀ v g, (ρ.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ρ.ψ v i g : Q))) → (∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) → ρ.IsBar f := by
  intro l _ k _ F n Q _ _ _ f ρ hbar htri hchar hdiag
  refine ⟨hdiag, ?_⟩
  intro v i g
  have hz : ∀ (s : F.G0) (a b : Fin n), a < b → ρ.r s a b = 0 := fun s a b hab => by
    have : ρ.r s a b ∈ ρ.triM := Ideal.subset_span ⟨s, a, b, hab, rfl⟩
    rw [htri] at this
    exact (Submodule.mem_bot Q).1 this
  have hT : (ρ.r (F.loc0 v g))ᵀ.BlockTriangular id := fun a b hab => hz _ b a hab
  have h1 := Matrix.charpoly_of_upperTriangular _ hT
  rw [Matrix.charpoly_transpose, hchar] at h1
  have h2 := congrArg (Polynomial.eval (ρ.ψ v i g : Q)) h1
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [sub_eq_zero, Matrix.transpose_apply, hdiag] at hj
  have h3 := hbar.2 v i g
  rw [NRep.map_ψ, hj] at h3
  have h4 := ((residue Q).comp f).injective h3
  rw [hj, h4]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyCoeffsInSubalgebra

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem localization_prime_generation {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ} (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3)
    (S : Space O F n) (x : Ideal S.A) (L : S.Loc x) {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ)
    (hh : h ≠ 0) (hs : ∀ a, F.Ψ (s a) = 1)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) →
      ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧
        ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1))
    (P : Ideal L.R) (hP : P.IsPrime) (h0 : L.ρ.triM ≤ P) (h1 : (maximalIdeal O).map (algebraMap O L.R) ≤ P)
    (h2 : ∀ a (i : Fin n), (i : ℕ) = 0 → L.ρ.r (s a) i i - 1 ∈ P)
    (h3 : ∀ a (i : Fin n), w n i = 0 → L.ρ.r (s' a) i i - 1 ∈ P) : S.mB.map L.b ≤ P := by
  haveI : IsLocalRing (L.R ⧸ P) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨hfin, hloc, hc, f, hf, hb⟩ := (local_deformation_trace_mod_maximal hF hn S x L).2.2 P h1
  have ht : (L.ρ.map (Ideal.Quotient.mk P)).triM = ⊥ := by
    rw [NRep.triM, Ideal.span_eq_bot]
    rintro _ ⟨g, i, j, hij, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h0 (Ideal.subset_span ⟨g, i, j, hij, rfl⟩))
  have hd := triangular_representation_diagonal hF hn f (L.ρ.map (Ideal.Quotient.mk P)) hc hb ht s s' h hh hs H
    (fun a i hi => Ideal.Quotient.eq.2 (h2 a i hi)) (fun a i hi => Ideal.Quotient.eq.2 (h3 a i hi))
  have hch : ∀ v g, ((L.ρ.map (Ideal.Quotient.mk P)).r (F.loc0 v g)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((L.ρ.map (Ideal.Quotient.mk P)).ψ v i g : L.R ⧸ P)) := fun v g => by
    have e := congrArg (Polynomial.map ((Ideal.Quotient.mk P).comp (L.ι : S.A →+* L.R))) (o1 hF hn S v g)
    rw [← Matrix.charpoly_map, Polynomial.map_prod] at e
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    exact e
  have hB := residually_diagonal_representation f _ hb ht hch hd
  have hm : ∀ y ∈ S.mB, L.b y ∈ maximalIdeal L.R := fun y hy => by
    have := (loc_flat hF hn S x L).2.2 hy
    rw [← L.lies] at this
    exact this
  have := maximal_ideal_image_kills hF hn S f ((Ideal.Quotient.mk P).comp (L.ι : S.A →+* L.R))
    (fun a => by rw [← hf]; exact congrArg (Ideal.Quotient.mk P) (L.ι.commutes a))
    (fun y hy => hloc _ (hm y hy)) ht hB
  exact Ideal.map_le_iff_le_comap.2 fun y hy =>
    Ideal.mem_comap.2 ((Ideal.Quotient.eq_zero_iff_mem (I := P)).1 (this y hy))

theorem UpperTheory.V.Fr.l51 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ L.ρ.triM) ≤ ((n - 1) * F.d + 2 + (3 * C₀ + 5) : ℕ) ∧ L.ρ.triP = ⊤ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hx
  refine ⟨?_, ((loc_rho hF hn S x L).2.2.2 hx).1⟩
  obtain ⟨s, s', h, hh, hs, hs', H⟩ := ab_gen hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ' := hϖ.maximalIdeal_eq
  obtain ⟨q1, q2, -⟩ := local_deformation_trace_mod_maximal hF hn S x L
  have hs1 : ∀ a, F.Ψ (s' a) = 1 := fun a => by
    obtain ⟨v, g, -, e, e'⟩ := hs' a
    rw [e']
    exact e
  let i0 : Fin n := ⟨0, by omega⟩
  let t : Unit ⊕ Fin (1 + C₀ + F.d) ⊕ ({i : Fin n // w n i = 0} × Fin F.d) → L.R :=
    Sum.elim (fun _ => algebraMap O L.R ϖ)
      (Sum.elim (fun a => L.ρ.r (s a) i0 i0 - 1) fun p => L.ρ.r (s' p.2) p.1 p.1 - 1)
  have hc := krull_dim_quotient_bound L.ρ.triM (S.mB.map L.b) t (by
      rintro (_ | a | p)
      · exact q1 (Ideal.mem_map_of_mem _ (hϖ' ▸ Ideal.mem_span_singleton_self ϖ))
      · exact q2 _ _ (hs a)
      · exact q2 _ _ (hs1 p.2))
    (fun P hP h0 ht => localization_prime_generation hF hn S x L s s' h hh hs H P hP h0
      (by rw [hϖ', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; exact ht (.inl ()))
      (fun a i hi => by
        obtain rfl : i = i0 := Fin.ext hi
        exact ht (.inr (.inl a)))
      (fun a i hi => ht (.inr (.inr (⟨i, hi⟩, a)))))
  have hw : Fintype.card {i : Fin n // w n i = 0} + 2 = n := by
    rcases hn with rfl | rfl <;> decide
  refine hc.trans ((add_le_add_left (fib_dim hF hn S x L hx) _).trans ?_)
  rw [← Nat.cast_add, Nat.cast_le]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  have e : n - 1 = Fintype.card {i : Fin n // w n i = 0} + 1 := by omega
  rw [e, add_mul]
  omega
end
end
