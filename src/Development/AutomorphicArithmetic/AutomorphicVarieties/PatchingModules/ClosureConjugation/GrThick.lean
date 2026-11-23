module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Mathlib.Data.Matrix.Basis
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Algebra.Module.BigOperators
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AlghomOfUnits

section

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.alghom_of_units :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (e : ∀ s, d s → d s → E), (∀ s i j k, e s i j * e s j k = e s i k) → (∀ s i j k l, j ≠ k → e s i j * e s k l = 0) → (∀ s t i j k l, s ≠ t → e s i j * e t k l = 0) → ∑ s, ∑ i, e s i i = 1 → ∃ j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E, ∀ s i k, j (Pi.single s (single i k 1)) = e s i k := by
  intro K E _ _ _ σ _ _ d _ _ _ e hmul horth hst hsum
  let f : (∀ s, Matrix (d s) (d s) K) → E := fun M => ∑ s, ∑ i, ∑ k, M s i k • e s i k
  have hadd : ∀ M N, f (M + N) = f M + f N := by
    intro M N
    simp only [f, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : K) M, f (c • M) = c • f M := by
    intro c M
    simp only [f, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have key : ∀ (N : ∀ s, Matrix (d s) (d s) K) s i j (a : K),
      (a • e s i j) * f N = ∑ k, (a * N s j k) • e s i k := by
    intro N s i j a
    simp only [f]
    rw [Finset.mul_sum, Finset.sum_eq_single s]
    · rw [Finset.mul_sum, Finset.sum_eq_single j]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_smul_comm, hmul]
      · intro l _ hl
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [smul_mul_smul_comm, horth s i j l k (Ne.symm hl), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t _ ht
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [smul_mul_smul_comm, hst s t i j l k (Ne.symm ht), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hm : ∀ M N, f (M * N) = f M * f N := by
    intro M N
    have : f M * f N = ∑ s, ∑ i, ∑ j, ∑ k, (M s i j * N s j k) • e s i k := by
      show (∑ s, ∑ i, ∑ k, M s i k • e s i k) * f N = _
      simp only [Finset.sum_mul, key]
    rw [this]
    simp only [f, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have h1 : f 1 = 1 := by
    simp only [f, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hsum
  let L : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E :=
    { toFun := f, map_add' := hadd, map_smul' := hsmul }
  refine ⟨AlgHom.ofLinearMap L h1 hm, ?_⟩
  intro s i k
  show f (Pi.single s (Matrix.single i k 1)) = e s i k
  simp only [f]
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same]
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [if_neg]
        exact fun h => hb h.2.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      exact fun h => hb h.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ _) h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrSs

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_ss :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} {a : ℕ} {T : TrInv B E} {r : E →ₐ[B] Matrix (Fin n) (Fin n) F} {ep : Fin n → E} (g : GrAlg T n a r ep) (κ : Type) [Field κ] [Algebra B κ] (s : B), algebraMap B κ s ≠ 0 → s ∈ Module.annihilator B g.N → IsSemisimpleRing (κ ⊗[B] E) := by
  intro B E F _ _ _ _ _ _ n a T r ep g κ _ _ s hs hann
  classical
  let M : Fin n → Fin n → Matrix (Fin n) (Fin n) g.AA :=
    fun i k => Matrix.single i k (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0)
  have hM : ∀ i k, ∃ x : E, g.φ x = M i k := by
    intro i k
    rw [← Set.mem_range, g.range]
    intro p q
    refine ⟨fun _ => ?_, fun hpq => ?_⟩
    · simp only [M, Matrix.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact zero_mem _
      · exact zero_mem _
    · simp only [M, Matrix.single_apply]
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl⟩ := h1
        exact absurd h2 hpq
      · exact zero_mem _
      · exact zero_mem _
  choose e he using hM
  have hmul : ∀ i k l : Fin n, ((i : ℕ) < a ↔ (k : ℕ) < a) → ((k : ℕ) < a ↔ (l : ℕ) < a) →
      e i k * e k l = e i l := by
    intro i k l hik hkl
    apply g.φ_inj
    rw [map_mul, he, he, he]
    simp only [M, if_pos hik, if_pos hkl, if_pos (hik.trans hkl), Matrix.single_mul_single_same,
      mul_one]
  have hzero : ∀ i k l m : Fin n, k ≠ l → e i k * e l m = 0 := by
    intro i k l m hkl
    apply g.φ_inj
    rw [map_mul, he, he, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkl _
  have hcross : ∀ i k : Fin n, ¬((i : ℕ) < a ↔ (k : ℕ) < a) → e i k = 0 := by
    intro i k hik
    apply g.φ_inj
    rw [he, map_zero]
    simp only [M, if_neg hik, Matrix.single_zero]
  have hsum : ∑ i, e i i = 1 := by
    apply g.φ_inj

    rw [map_sum, map_one]
    simp only [he, M, iff_self, if_true]
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [Matrix.one_apply_ne hpq]
      exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hpq (h.1.symm.trans h.2)))
  have hdec : ∀ y : E, ∃ b : Fin n → Fin n → B, s • y = ∑ i, ∑ k, b i k • e i k := by
    intro y
    have hent : ∀ i k, ∃ c : B, s • g.φ y i k = c • (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0) := by
      intro i k
      obtain ⟨h1, h2⟩ := (g.range (g.φ y)).mp ⟨y, rfl⟩ i k
      by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
      · obtain ⟨c, hc⟩ := Submodule.mem_one.mp (h1 hik)
        refine ⟨s * c, ?_⟩
        rw [if_pos hik, ← hc, Algebra.algebraMap_eq_smul_one, smul_smul]
      · refine ⟨0, ?_⟩
        rw [if_neg hik, smul_zero]
        have := (Module.mem_annihilator.mp hann) ⟨_, h2 hik⟩
        simpa using congrArg Subtype.val this
    choose c hc using hent
    refine ⟨c, g.φ_inj ?_⟩

    rw [map_smul, map_sum]
    ext p q

    simp only [map_sum, map_smul, he, M, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    rw [hc, Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero (fun k _ => by
        rw [if_neg (fun h => hi h.1), smul_zero])) (by simp),
      Finset.sum_eq_single q (fun k _ hk => by rw [if_neg (fun h => hk h.2), smul_zero]) (by simp)]
    simp
  let bf : Fin n → Bool := fun i => decide ((i : ℕ) < a)
  let cl : Fin n → Set.range bf := Set.rangeFactorization bf
  have hcl : ∀ i k : Fin n, cl i = cl k ↔ ((i : ℕ) < a ↔ (k : ℕ) < a) := by
    intro i k
    simp only [cl, bf, Set.rangeFactorization, Subtype.mk.injEq, decide_eq_decide]
  let d : Set.range bf → Type := fun t => {i : Fin n // cl i = t}
  haveI : ∀ t, Nonempty (d t) := fun t => by
    obtain ⟨i, hi⟩ := Set.rangeFactorization_surjective t
    exact ⟨⟨i, hi⟩⟩
  let ee : (t : Set.range bf) → d t → d t → κ ⊗[B] E := fun t i k => (1 : κ) ⊗ₜ[B] e i.1 k.1
  obtain ⟨j, hj⟩ := alghom_of_units (K := κ) (E := κ ⊗[B] E) d ee
    (fun t i k l => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hmul _ _ _ ((hcl _ _).mp (i.2.trans k.2.symm)) ((hcl _ _).mp (k.2.trans l.2.symm))])
    (fun t i k l m hkl => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => hkl (Subtype.ext h)), TensorProduct.tmul_zero])
    (fun t u i k l m htu => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => htu (by rw [← k.2, ← l.2, h])), TensorProduct.tmul_zero])
    (by
      simp only [ee]
      rw [Fintype.sum_fiberwise cl (fun i => (1 : κ) ⊗ₜ[B] e i i), ← TensorProduct.tmul_sum, hsum,
        Algebra.TensorProduct.one_def])
  have hgen : ∀ i k : Fin n, (1 : κ) ⊗ₜ[B] e i k ∈ j.range := by
    intro i k
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk : cl k = cl i := (hcl k i).mpr hik.symm
      exact (AlgHom.mem_range j).mpr
        ⟨Pi.single (cl i) (Matrix.single ⟨i, rfl⟩ ⟨k, hk⟩ 1), hj (cl i) ⟨i, rfl⟩ ⟨k, hk⟩⟩
    · rw [hcross i k hik, TensorProduct.tmul_zero]
      exact Subalgebra.zero_mem _
  have hone : ∀ y : E, (1 : κ) ⊗ₜ[B] y ∈ j.range := by
    intro y
    obtain ⟨b, hb⟩ := hdec y
    have h1 : (1 : κ) ⊗ₜ[B] y = (algebraMap B κ s)⁻¹ • ((1 : κ) ⊗ₜ[B] (s • y)) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        smul_eq_mul, inv_mul_cancel₀ hs]
    rw [h1, hb, TensorProduct.tmul_sum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i _ => ?_)) _
    rw [TensorProduct.tmul_sum]
    refine Subalgebra.sum_mem _ (fun k _ => ?_)
    have h2 : (1 : κ) ⊗ₜ[B] (b i k • e i k) = (algebraMap B κ (b i k)) • ((1 : κ) ⊗ₜ[B] e i k) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [h2]
    exact Subalgebra.smul_mem _ (hgen i k) _
  refine RingHom.isSemisimpleRing_of_surjective j.toRingHom ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul u y =>
    obtain ⟨z, hz⟩ := (AlgHom.mem_range j).mp (hone y)
    refine ⟨u • z, ?_⟩
    show j (u • z) = _
    rw [map_smul, hz, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add (f := _), hz, hw]⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrThick

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem quot_ss {B Bh E κ Γ : Type} [CommRing B] [CommRing Bh] [Algebra B Bh] [Ring E] [Algebra Bh E]
    [Field κ] [Algebra Bh κ] [Group Γ] (I : Set (MonoidAlgebra B Γ))
    (ι : MonoidAlgebra Bh Γ →ₐ[Bh] E) (surj : Function.Surjective ι)
    (ker : ∀ y, ι y = 0 → y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I))
    [IsSemisimpleRing (κ ⊗[Bh] E)] :
    IsSemisimpleRing (TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I)).ringCon.Quotient := by
  set J := TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I) with hJ
  let π : MonoidAlgebra κ Γ →+* J.ringCon.Quotient := J.ringCon.mk'
  have hπ : ∀ z, z ∈ J → π z = 0 := by
    intro z hz
    rw [← map_zero π]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.mem_iff _ _).1 hz)
  let ψ0 : MonoidAlgebra Bh Γ →+* J.ringCon.Quotient :=
    π.comp (MonoidAlgebra.mapRingHom Γ (algebraMap Bh κ))
  have hk : RingHom.ker ι.toRingHom ≤ RingHom.ker ψ0 := by
    intro y hy
    have h1 := ker y hy
    have h2 : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I) ≤ TwoSidedIdeal.ker ψ0 := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
      apply hπ
      apply TwoSidedIdeal.subset_span
      refine ⟨z, hz, ?_⟩
      ext a
      simp
    exact (TwoSidedIdeal.mem_ker _).1 (h2 h1)
  let ψ : E →+* J.ringCon.Quotient := ι.toRingHom.liftOfSurjective surj ⟨ψ0, hk⟩
  have hψ : ∀ y, ψ (ι y) = ψ0 y := fun y => RingHom.liftOfSurjective_comp_apply ι.toRingHom surj ⟨ψ0, hk⟩ y
  let ψa : E →ₐ[Bh] J.ringCon.Quotient :=
    { ψ with
      commutes' := fun b => by
        change ψ (algebraMap Bh E b) = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        rw [← ι.commutes, hψ]
        change π _ = _
        congr 1
        simp [MonoidAlgebra.coe_algebraMap] }
  let ka : κ →ₐ[Bh] J.ringCon.Quotient :=
    { π.comp (algebraMap κ (MonoidAlgebra κ Γ)) with
      commutes' := fun b => by
        change π _ = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        congr 1 }
  have hc : ∀ a y, Commute (ka a) (ψa y) := by
    intro a y
    obtain ⟨y, rfl⟩ := surj y
    change Commute (π (algebraMap κ _ a)) (ψ (ι y))
    rw [hψ]
    exact Commute.map (Algebra.commutes a _) π
  let Φ := Algebra.TensorProduct.lift ka ψa hc
  refine RingHom.isSemisimpleRing_of_surjective Φ.toRingHom ?_
  intro w
  obtain ⟨w, rfl⟩ : ∃ z, π z = w := J.ringCon.mk'_surjective w
  induction w using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | single m a =>
    refine ⟨a ⊗ₜ ι (MonoidAlgebra.single m 1), ?_⟩
    change Φ _ = _
    rw [Algebra.TensorProduct.lift_tmul]
    change π (algebraMap κ _ a) * ψ (ι _) = _
    rw [hψ]
    change π _ * π _ = _
    rw [← map_mul]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.single_mul_single]

theorem UpperTheory.V.Pa.gr_thick :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), ∀ Q : Ideal Bh, Q.IsPrime → NonSS I (algebraMap B Bh) Q → Module.annihilator Bh g.N ≤ Q := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g Q _ hQ s hs
  obtain ⟨κ, _, f, hf, hns⟩ := hQ
  by_contra hsQ
  letI : Algebra Bh κ := f.toAlgebra
  have hs0 : algebraMap Bh κ s ≠ 0 := fun h0 => hsQ (hf ▸ (RingHom.mem_ker.2 h0 : s ∈ RingHom.ker f))
  haveI := UpperTheory.V.Pa.gr_ss g κ s hs0 hs
  exact hns (quot_ss (κ := κ) I H.ι H.surj (fun y hy => (H.ker y).1 hy))
end
end
