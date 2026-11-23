module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AnnOfFlat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Detsec
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EnnrealVolumeRatioStepCancel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SumLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ThickOfDer
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Oddm

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.oddm :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (a g : ℕ) (G : MvPowerSeries (Fin a ⊕ Fin g) O), G ∈ wtPart O (Space.Loc.par a g) 1 → (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) G ∈ maximalIdeal O) → ∃ M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O, (∀ j, MvPowerSeries.constantCoeff (M j) ∈ maximalIdeal O) ∧ G = ∑ j, M j * MvPowerSeries.X (.inr j) := by
  classical
  intro O _ _ a g G hG hlin
  let M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O := fun j m =>
    if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
      MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0
  have hM : ∀ j m, MvPowerSeries.coeff m (M j) =
      if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
        MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0 := fun _ _ => rfl
  refine ⟨M, ?_, ?_⟩
  · intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hM]
    simpa using hlin (Sum.inr j)
  · ext n

    rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one, hM]
    by_cases hex : ∃ j : Fin g, n (Sum.inr j) ≠ 0
    · let S := Finset.univ.filter (fun j : Fin g => n (Sum.inr j) ≠ 0)
      have hS : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, by simp [S, hj]⟩
      have hj0 : n (Sum.inr (S.min' hS)) ≠ 0 := by
        have := S.min'_mem hS
        simpa [S] using this
      have hmin : ∀ k : Fin g, n (Sum.inr k) ≠ 0 → S.min' hS ≤ k := fun k hk =>
        S.min'_le k (by simp [S, hk])
      have hle : ∀ j : Fin g, n (Sum.inr j) ≠ 0 → Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        rw [Finsupp.single_le_iff]
        omega
      rw [Finset.sum_eq_single (S.min' hS)]
      · rw [if_pos (hle _ hj0), if_pos, tsub_add_cancel_of_le (hle _ hj0)]
        intro k hk
        by_contra hne
        have := hmin k (by simpa [Finsupp.tsub_apply, Finsupp.single_apply, ne_of_gt hk] using hne)
        exact absurd hk (not_lt.mpr this)
      · intro j _ hj
        by_cases hjl : Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n
        · rw [if_pos hjl]
          have hnj : n (Sum.inr j) ≠ 0 := by
            have := hjl (Sum.inr j)
            simp at this
            omega
          have hlt : S.min' hS < j := lt_of_le_of_ne (hmin j hnj) (Ne.symm hj)
          rw [if_neg]
          intro hall
          have := hall _ hlt
          simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm (ne_of_lt hlt)] at this
          exact hj0 this
        · rw [if_neg hjl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hex
      have hz : ∀ j : Fin g, ¬ Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        have := hj (Sum.inr j)
        simp [hex j] at this
      simp only [hz, if_false, Finset.sum_const_zero]
      apply hG
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero]
      · decide
      · intro i _
        rcases i with i | i
        · simp [Space.Loc.par]
        · simp [hex i]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ChainedOfComap

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_comap {A R : Type} [CommRing A] [CommRing R] (p : A →+* R) (hp : Function.Surjective p)
    (P : Ideal R) : ringKrullDim (A ⧸ P.comap p) = ringKrullDim (R ⧸ P) := by
  have h : RingHom.ker ((Ideal.Quotient.mk P).comp p) = P.comap p := by
    ext a; simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [← h]
  exact ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hp))

private theorem chained_of_comap {A R : Type} [CommRing A] [CommRing R] (p : A →+* R) (hp : Function.Surjective p)
    (I : Ideal R) (D : ℕ) (h : Chained (I.comap p) D) : Chained I D := by
  have hm : (I.comap p).minimalPrimes = Ideal.comap p '' I.minimalPrimes :=
    Ideal.comap_minimalPrimes_eq_of_surjective hp I
  refine ⟨fun P hP => ?_, fun P hP Q hQ => ?_⟩
  · rw [← dim_comap p hp]
    exact h.1 _ (hm ▸ ⟨P, hP, rfl⟩)
  · have h1 := h.2 (P.comap p) (hm ▸ ⟨P, hP, rfl⟩) (Q.comap p) (hm ▸ ⟨Q, hQ, rfl⟩)
    have h2 : ∀ b, Relation.ReflTransGen (fun P Q : Ideal A => P ∈ (I.comap p).minimalPrimes ∧
        Q ∈ (I.comap p).minimalPrimes ∧ (D : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ (P ⊔ Q))) (P.comap p) b →
        Relation.ReflTransGen (fun P Q : Ideal R => P ∈ I.minimalPrimes ∧ Q ∈ I.minimalPrimes ∧
          (D : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (P ⊔ Q))) P (b.map p) := by
      intro b hb
      induction hb with
      | refl => rw [Ideal.map_comap_of_surjective p hp]
      | tail _ hab ih =>
        refine ih.tail ?_
        obtain ⟨ha, hb, hd⟩ := hab
        rw [hm] at ha hb
        obtain ⟨a, ha, rfl⟩ := ha
        obtain ⟨b, hb, rfl⟩ := hb
        rw [Ideal.map_comap_of_surjective p hp, Ideal.map_comap_of_surjective p hp]
        refine ⟨ha, hb, ?_⟩
        have : (a ⊔ b).comap p = a.comap p ⊔ b.comap p := by
          conv_lhs => rw [← Ideal.map_comap_of_surjective p hp a, ← Ideal.map_comap_of_surjective p hp b,
            ← Ideal.map_sup, Ideal.comap_map_of_surjective p hp]
          exact sup_eq_left.2 (le_sup_of_le_left (Ideal.comap_mono bot_le))
        rwa [← dim_comap p hp, this]
    have h3 := h2 _ h1
    rwa [Ideal.map_comap_of_surjective p hp] at h3

private theorem cc_mem {σ O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Nontrivial R]
    (p : MvPowerSeries σ O →+* R) (f : MvPowerSeries σ O) (hf : p f = 0) :
    MvPowerSeries.constantCoeff f ∈ maximalIdeal O := by
  intro hu
  have := (MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map p
  rw [hf] at this
  exact not_isUnit_zero this

private theorem detsec' (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (a b g D : ℕ) (hg : g ≠ 0) (f : Fin b → MvPowerSeries (Fin a ⊕ Fin g) O)
    (M : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin a ⊕ Fin g) O)) (h : a = b + D)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) ∈ maximalIdeal O)
    (hM : ∀ i j, MvPowerSeries.constantCoeff (M i j) ∈ maximalIdeal O) :
    Chained (Ideal.span (Set.range f ∪ Set.range (M *ᵥ fun j => MvPowerSeries.X (.inr j)) ∪ {M.det})) D := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg
  exact detsec O a b g D f M h hf hM

theorem UpperTheory.V.Fr.sharp3 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → ∃ I : Ideal L.R, L.Sharp I := by
  intro l _ O _ _ _ _ F C₀ hF S x L hB hx
  obtain ⟨-, -, hcmp, htri⟩ := loc_rho hF (Or.inr rfl) S x L
  have hoff : ∀ I : Ideal L.R, Chained I (3 * F.d + 1) → ∀ P ∈ I.minimalPrimes, L.ρ.OffTri P := by
    intro I hI P hP
    refine ⟨fun h => hP.1.1.ne_top (top_le_iff.1 ((htri hx).1 ▸ h)), fun h => ?_⟩
    have h1 := (krull_dim_lt_of_not_le_triangular hF (Or.inr rfl) S x L hB hx).1
    have h2 : ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (L.R ⧸ L.ρ.triM) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)
    have h3 := ((hI.1 P hP).trans h2).trans_lt h1
    have h4 : 3 * F.d + 1 + 1 < 3 * F.d := by exact_mod_cast h3
    omega
  by_cases hee : S.u.ee ≤ x
  · obtain ⟨E⟩ := epres hF S x L hee
    have hG : ∀ i, E.Go i ∈ RingHom.ker E.p := fun i =>
      E.ker ▸ Ideal.subset_span (Or.inr ⟨i, rfl⟩)
    have hFe : ∀ i, E.Fe i ∈ RingHom.ker E.p := fun i =>
      E.ker ▸ Ideal.subset_span (Or.inl ⟨i, rfl⟩)
    choose M hM hGM using fun i => oddm L.O' E.a E.g (E.Go i) (E.odd i) (E.min _ (hG i))
    have hGo : E.Go = Matrix.of M *ᵥ fun j => MvPowerSeries.X (.inr j) := funext hGM
    have hch : Chained (Ideal.span {E.p (Matrix.of M).det}) (3 * F.d + 1) := by
      refine chained_of_comap E.p.toRingHom E.surj _ _ ?_
      have h1 := detsec' L.O' E.a E.b E.g _ (gpos hF S x L hx E) E.Fe (Matrix.of M) E.num
        (fun i => cc_mem E.p.toRingHom _ (hFe i)) hM
      rw [← hGo, Ideal.span_union, ← E.ker] at h1
      convert h1 using 1
      have : Ideal.span {E.p (Matrix.of M).det} = (Ideal.span {(Matrix.of M).det}).map E.p.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]; rfl
      rw [this, Ideal.comap_map_of_surjective E.p.toRingHom E.surj, sup_comm]
      rfl
    refine ⟨_, fun h => absurd hee h, fun P hP hne => ?_, hch, fun P hP => ?_⟩
    · rw [E.ee, Ideal.span_le, Set.range_subset_iff, not_forall] at hne
      obtain ⟨j, hj⟩ := hne
      rw [Ideal.span_singleton_le_iff_mem]
      refine (hP.mem_or_mem ?_).resolve_right hj
      have h1 : ((Matrix.of M).adjugate *ᵥ E.Go) j = (Matrix.of M).det * MvPowerSeries.X (.inr j) := by
        rw [hGo, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
      have h2 : ((Matrix.of M).adjugate *ᵥ E.Go) j ∈ RingHom.ker E.p := by
        rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hG i)
      rw [h1, RingHom.mem_ker, map_mul] at h2
      rw [h2]
      exact P.zero_mem
    · by_cases he : L.ρ.ee ≤ P
      · exact Or.inr (thick hF S x L E _ hGo P hP.1.1 ⟨hoff _ hch P hP, rfl, he⟩
          (hP.1.2 (Ideal.mem_span_singleton_self _)))
      · exact Or.inl ⟨hoff _ hch P hP, fun _ => he⟩
  · obtain ⟨N, N', p, f, hN, hp, hk⟩ := pres hF (Or.inr rfl) S x L
    have hch : Chained (⊥ : Ideal L.R) (3 * F.d + 1) := by
      refine chained_of_comap p.toRingHom hp _ _ ?_
      haveI hco : IsCO L.O' (MvPowerSeries (Fin N) L.O') := co_mvps L.O' L.O' (Fin N)
      haveI : IsNoetherianRing (MvPowerSeries (Fin N) L.O') := hco.toIsNoetherian
      haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin N) L.O')) (MvPowerSeries (Fin N) L.O') :=
        hco.complete
      have h1 := c1ch (MvPowerSeries (Fin N) L.O') N' (3 * F.d + 1) f
        (by rw [nilradical_eq_zero]; exact Ideal.isPrime_bot) ⟨L.O', L.cO, L.dO, L.vO, inferInstance, _, hco⟩
        (fun i hu => by
          have h0 : f i ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨i, rfl⟩
          have := hu.map p
          rw [RingHom.mem_ker.1 h0] at this
          exact not_isUnit_zero this)
        (by
          rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
            Nat.card_eq_fintype_card, Fintype.card_fin, hN]
          norm_cast
          omega)
      rw [← hk] at h1
      exact h1
    refine ⟨⊥, fun _ => rfl, fun _ _ _ => bot_le, hch, fun P hP => Or.inl ⟨hoff _ hch P hP, fun _ h => hee ?_⟩⟩
    exact ((hcmp P).2.2.1 h).trans ((Ideal.comap_mono (le_maximalIdeal hP.1.1.ne_top)).trans L.lies.le)
end
end
